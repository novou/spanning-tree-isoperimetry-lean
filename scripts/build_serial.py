#!/usr/bin/env python3
"""Regenerate Lake artifacts serially for the proof and comparison modules.

Each module's :deps facet must pass Lake's --no-build check immediately before
its :leanArts build. Together with topological order and frozen sources, this
ensures that only the requested module can require compilation. The runtime
thread setting is an extra precaution, not the concurrency guarantee.

Run exclusively: no other build, compiler, or source edits during this script.
Use --plan to inspect the closure without invoking Lake or any compiler.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
# Challenge and Solution deliberately declare the same interface in independent
# environments. Build each module separately; never import them into one module.
ROOT_MODULES = ("SpanningTreeIsoperimetry", "Solution", "Challenge")
LOGS = ROOT / "build" / "serial"
LAKE = ROOT / "scripts" / "lake.sh"
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def imports(path):
    """Read module imports, excluding nested comments and strings."""
    text = path.read_text()
    clean, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            clean.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            clean.append("  ")
            i += 2
        elif depth:
            clean.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                break
            clean.append(" " * (end - i))
            i = end
        elif text[i] == '"':
            clean.append(" ")
            i += 1
            while i < len(text):
                char = text[i]
                clean.append("\n" if char == "\n" else " ")
                i += 1
                if char == "\\":
                    i += 1
                elif char == '"':
                    break
        else:
            clean.append(text[i])
            i += 1
    if depth:
        raise RuntimeError(f"Unclosed comment in {path}")
    result = []
    for line in "".join(clean).splitlines():
        match = re.fullmatch(
            r"\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+?)\s*",
            line,
        )
        if match:
            for name in match[1].split():
                if not MODULE_NAME.fullmatch(name):
                    raise RuntimeError(f"Unsupported import syntax in {path}: {line}")
                result.append(name)
    return result


def local_source(name):
    relative = Path(*name.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "Foundations"):
        path = base / relative
        if path.is_file():
            return path
    if name in ROOT_MODULES or name.startswith(("SpanningTreeIsoperimetry.", "SquareMaximality")):
        raise RuntimeError(f"Missing local source: {name}")
    return None


def plan(roots=ROOT_MODULES):
    order, sources, external, visiting = [], {}, set(), set()

    def visit(name):
        path = local_source(name)
        if path is None:
            external.add(name)
            return
        if name in visiting:
            raise RuntimeError(f"Import cycle at {name}")
        if name in sources:
            return
        visiting.add(name)
        for dependency in imports(path):
            visit(dependency)
        visiting.remove(name)
        sources[name] = path
        order.append(name)

    for name in roots:
        visit(name)
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    toolchain_dir = toolchain.replace("/", "--").replace(":", "---")
    system_lib = ROOT / ".tooling" / "elan" / "toolchains" / toolchain_dir / "lib" / "lean"
    external_targets, system_modules = [], []
    for name in sorted(external):
        relative = Path(*name.split("."))
        if (system_lib / relative.with_suffix(".olean")).is_file():
            system_modules.append(name)
        elif any((package / relative.with_suffix(".lean")).is_file()
                 for package in (ROOT / ".lake" / "packages").iterdir()):
            external_targets.append(name)
        else:
            raise RuntimeError(f"External import is not installed: {name}")
    return order, sources, external_targets, system_modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true", help="inspect only; do not invoke Lake")
    args = parser.parse_args()
    order, sources, external, system = plan()
    LOGS.mkdir(parents=True, exist_ok=True)
    plan_file = LOGS / "plan.json"
    plan_file.write_text(json.dumps({
        "roots": ROOT_MODULES, "local_order": order,
        "external_preflight": external, "installed_system_modules": system,
    }, indent=2) + "\n")
    print(f"Plan: {len(order)} local modules; {len(external)} external cached targets; "
          f"{len(system)} installed system imports. {plan_file}", flush=True)
    if args.plan:
        return

    frozen = list(sources.values()) + [ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                                      ROOT / "lean-toolchain"]
    stats = {path: (path.stat().st_mtime_ns, path.stat().st_size) for path in frozen}
    environment = dict(os.environ, LEAN_NUM_THREADS="1")

    def check_frozen():
        for path, previous in stats.items():
            stat = path.stat()
            if (stat.st_mtime_ns, stat.st_size) != previous:
                raise RuntimeError(f"Source/config changed during serial build: {path}")

    def run(arguments, log_name, allow_failure=False):
        check_frozen()
        log = LOGS / log_name
        with log.open("w") as output:
            result = subprocess.run([str(LAKE), *arguments], cwd=ROOT, env=environment,
                                    stdout=output, stderr=subprocess.STDOUT)
        check_frozen()
        if result.returncode and not allow_failure:
            raise RuntimeError(f"Lake failed ({result.returncode}); stopped without further builds. "
                               f"See {log}\n{log.read_text()[-2500:]}")
        return result.returncode == 0

    root_targets = [f"+{name}:leanArts" for name in ROOT_MODULES]

    # Check the explicit roots as well as Lake's default targets: a configuration
    # that accidentally drops Solution must not reduce this script's coverage.
    if (run(["--no-cache", "--no-build", "build", *root_targets],
            "roots-fast-path.log", allow_failure=True)
            and run(["--no-cache", "--no-build", "build"],
                    "aggregate-fast-path.log", allow_failure=True)):
        run(["build"], "aggregate-build.log")
        print("All proof and comparison modules cached; ordinary lake build passed.", flush=True)
        return

    # Interface edits often invalidate only these roots. Each successful :deps
    # preflight still permits exactly one compiler in the following build.
    roots_only = True
    for name in ROOT_MODULES:
        if not run(["--no-cache", "--no-build", "build", f"+{name}:deps"],
                   f"{name}-deps-fast-path.log", allow_failure=True):
            roots_only = False
            break
        run(["--no-cache", "build", f"+{name}:leanArts"], f"{name}-module-build.log")
    if roots_only:
        run(["--no-cache", "--no-build", "build", *root_targets], "roots-cached-preflight.log")
        run(["--no-build", "build"], "aggregate-cached-preflight.log")
        run(["build"], "aggregate-build.log")
        print("Root modules checked serially; ordinary cached lake build passed.", flush=True)
        return

    # --no-build is checked before Lake executes a build action. A stale external
    # cache aborts the run; this script never repairs external packages implicitly.
    if external:
        print("Preflight external cached dependencies", flush=True)
        run(["--no-cache", "--no-build", "build",
             *[f"+{name}:leanArts" for name in external]], "external-preflight.log")

    for number, name in enumerate(order, 1):
        label = f"{number:04d}-{name}"
        if run(["--no-cache", "--no-build", "build", f"+{name}:leanArts"],
               label + ".cached.log", allow_failure=True):
            print(f"[{number}/{len(order)}] cached {name}", flush=True)
            continue
        # :deps is Lake's module presetup/import/native-dependency facet. After
        # this succeeds, the immediately following single target can rebuild
        # only itself. Its output includes ordinary Lake traces and .ilean files.
        run(["--no-cache", "--no-build", "build", f"+{name}:deps"], label + ".deps.log")
        run(["--no-cache", "build", f"+{name}:leanArts"], label + ".build.log")
        print(f"[{number}/{len(order)}] {name}", flush=True)

    run(["--no-cache", "--no-build", "build", *root_targets], "roots-cached-preflight.log")
    run(["--no-build", "build"], "aggregate-cached-preflight.log")
    run(["build"], "aggregate-build.log")
    print("Serial rebuild and ordinary cached lake build passed.", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
