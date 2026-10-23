#!/usr/bin/env python3
"""Build the comparison modules and audit all local proof theorem dependencies."""
from pathlib import Path
import json
import re
import subprocess
import sys

from build_serial import MODULE_NAME, ROOT_MODULES, plan

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC"
)


def without_comments(text):
    output, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            output.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            output.append("  ")
            i += 2
        elif depth:
            output.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            output.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            output.append(" ")
            i += 1
            while i < len(text):
                c = text[i]
                i += 1
                if c == "\\":
                    i += 1
                elif c == '"':
                    break
        else:
            output.append(text[i])
            i += 1
    if depth:
        raise RuntimeError("Unclosed source comment")
    return "".join(output)


def check_source(path, challenge=False):
    text = without_comments(path.read_text())
    holes = 0
    for forbidden in FORBIDDEN.finditer(text):
        if challenge and forbidden.group() == "sorry":
            holes += 1
        else:
            raise RuntimeError(f"Disallowed construct in {path}: {forbidden.group()}")
    return holes


def run(command, log):
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"Command failed: see {log}\n{result.stdout[-2500:]}")
    return result.stdout


# Keep the manuscript endpoints explicit so a reduced proof import cannot pass.
REQUIRED_ENDPOINTS = {
    "SpanningTreeIsoperimetry." + name for name in (
        "maximizer_isoperimetric",
        "LargeClassification.uniqueClassificationTarget",
        "AllCardinalityClassification.maximumValueTarget",
        "AllCardinalityClassification.nonuniquenessTarget",
        "AllCardinalityClassification.maximizer_iff",
        "sharp_stability_inequality",
        "StabilitySharpness.coefficient_optimal",
        "ScalarProduct.cornerStrip_product",
        "ExtremalAsymptotic.extremal_count_asymptotic",
        "IntegerRigidityComparison.integer_rigidity",
        "GeneralQuadrantMinorReduction.determinant_reduction",
        "PotentialKernelDiagonal.diagonal_formula",
        "PotentialKernelImages.quadrantGreen_image_formula",
        "ScalarSpectralInterlacing.strict_zero_interlacing",
        "FirstProfileDerivatives.second_derivative_formula",
        "FirstProfileDerivatives.second_derivative_bounds",
        "StripFourierIdentity.regularized_identity",
        "StripFourierIdentity.strip_limit_identity",
        "StripFourierFourthOrder.coefficient_fourth_order_bound",
        "StripFourierLaplace.coefficient_laplace",
        "EpsilonFourierAlias.epsilon_fourier_alias",
        "FixedAspectRectangleError.limiting_aspect_isBigO",
        "FourteenFacePolynomials.faceDeterminant_difference",
    )
}


def comparison_config():
    path = ROOT / "comparator.json"
    config = json.loads(path.read_text())
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        raise RuntimeError("Audit expects independent Challenge and Solution comparison modules")
    names = config.get("theorem_names")
    if (not isinstance(names, list) or not names
            or any(not isinstance(name, str) or not MODULE_NAME.fullmatch(name) for name in names)
            or len(names) != len(set(names))):
        raise RuntimeError("Comparator theorem_names must be a nonempty list of distinct declaration names")
    if set(config.get("permitted_axioms", [])) != ALLOWED_AXIOMS:
        raise RuntimeError("Comparator permitted_axioms must be exactly the standard proof axioms")
    return config


def proof_sources():
    """Cover every local proof source, including helpers outside the root closure."""
    paths = set(ROOT.glob("*.lean"))
    for directory in (ROOT / "SpanningTreeIsoperimetry", ROOT / "Foundations"):
        paths.update(directory.rglob("*.lean"))
    paths.discard(ROOT / "Challenge.lean")
    return sorted(paths)


def audit_runner(module_order):
    # `import all` is not inherited through ordinary public imports. Import
    # every proof module directly to retain its private theorem declarations.
    template = (ROOT / "scripts/Audit.lean").read_text()
    if not template.startswith("module\n"):
        raise RuntimeError("Audit template must begin with a module header")
    extra_imports = "\n".join(f"import all {name}" for name in module_order if name != "Solution")
    path = BUILD / "Audit.lean"
    path.write_text(template.replace("module\n", f"module\n\n{extra_imports}\n", 1))
    return path


def audit_records(output, expected_modules):
    records = []
    for line in output.splitlines():
        if "AUDIT|" not in line:
            continue
        _, owner, name, axioms = line[line.index("AUDIT|"):].split("|", 3)
        records.append({"module": owner, "name": name,
                        "axioms": [a for a in axioms.split(",") if a]})
    counts = re.findall(r"AUDIT_COUNT\|(\d+)", output)
    if len(counts) != 1 or int(counts[0]) != len(records) or not records:
        raise RuntimeError("Incomplete compiled-environment audit")
    if len({record["name"] for record in records}) != len(records):
        raise RuntimeError("Duplicate theorem records in compiled-environment audit")
    compiled_modules = set(re.findall(r"AUDIT_MODULE\|([^\s|]+)", output))
    if compiled_modules != set(expected_modules):
        raise RuntimeError("Compiled proof module closure mismatch: "
                           + f"missing {sorted(set(expected_modules) - compiled_modules)}; "
                           + f"unexpected {sorted(compiled_modules - set(expected_modules))}")
    used = {axiom for record in records for axiom in record["axioms"]}
    if used - ALLOWED_AXIOMS:
        raise RuntimeError("Unexpected axioms: " + ", ".join(sorted(used - ALLOWED_AXIOMS)))
    return records, used


def main():
    BUILD.mkdir(exist_ok=True)
    report_path = BUILD / "audit.json"
    report_path.unlink(missing_ok=True)
    config = comparison_config()
    for path in proof_sources():
        check_source(path)
    challenge_holes = check_source(ROOT / "Challenge.lean", challenge=True)
    order, sources, _, _ = plan(("Solution", "SpanningTreeIsoperimetry"))
    if "Challenge" in sources:
        raise RuntimeError("Challenge is imported by the proof closure")
    for path in sources.values():
        check_source(path)
    run([sys.executable, str(ROOT / "scripts/build_serial.py")], BUILD / "build.log")
    runner = audit_runner(order)
    output = run([str(ROOT / "scripts/lake.sh"), "env", "lean", str(runner.relative_to(ROOT))],
                 BUILD / "axioms.log")
    records, used = audit_records(output, order)
    missing = REQUIRED_ENDPOINTS - {record["name"] for record in records}
    if missing:
        raise RuntimeError("Required theorem exports missing: " + ", ".join(sorted(missing)))
    solution_names = {record["name"] for record in records if record["module"] == "Solution"}
    missing_solution = set(config["theorem_names"]) - solution_names
    if missing_solution:
        raise RuntimeError("Compared Solution theorem exports missing: "
                           + ", ".join(sorted(missing_solution)))
    report = {
        "build_passed": True,
        "build_roots": list(ROOT_MODULES),
        "theorem_declarations_audited": len(records),
        "proof_modules_audited": order,
        "axioms_used": sorted(used),
        "declarations": records,
        "required_endpoints_checked": sorted(REQUIRED_ENDPOINTS),
        "solution_theorems_checked": sorted(config["theorem_names"]),
        "solution_proof_holes": 0,
        "challenge_statement_holes": challenge_holes,
        "challenge_imported_by_proofs": False,
        "comparison_configuration": "comparator.json",
        "statement_comparison": "Run lake comparator separately; this report records the proof audit.",
        "scope_correspondence": "docs/coverage.md",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Build passed; {len(records)} compiled theorem declarations audited; only standard axioms.")
    print(f"All {len(REQUIRED_ENDPOINTS)} manuscript endpoints and {len(config['theorem_names'])} "
          "compared Solution theorem exports are present.")
    print(f"Solution proof holes: 0; independent Challenge statement holes: {challenge_holes}.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
