#!/usr/bin/env python3
"""Build the project and audit the actual axiom dependencies of public theorems."""
from pathlib import Path
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
BUILD.mkdir(exist_ok=True)


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
    return "".join(output)


def theorem_names(path):
    text = without_comments(path.read_text())
    forbidden = re.search(r"\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC", text)
    if forbidden:
        raise RuntimeError(f"Disallowed construct in {path}: {forbidden.group()}")
    scopes, names = [], []
    for line in text.splitlines():
        line = line.strip()
        m = re.match(r"(?:(?:noncomputable|public)\s+)?(namespace|section)\s*([^\s]*)", line)
        if m:
            scopes.append((m[1], m[2]))
            continue
        if re.match(r"end(?:\s|$)", line):
            if scopes:
                scopes.pop()
            continue
        line = re.sub(r"^@\[[^]]*\]\s*", "", line)
        m = re.match(r"(?:protected\s+)?(?:theorem|lemma)\s+([^\s(:{]+)", line)
        if m:
            prefix = ".".join(name for kind, name in scopes if kind == "namespace")
            names.append((prefix + "." if prefix else "") + m[1])
    return names


def run(command, log):
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"Command failed: see {log}\n{result.stdout[-2500:]}")
    return result.stdout


for directory in (ROOT / "SpanningTreeIsoperimetry", ROOT / "Foundations"):
    for path in sorted(directory.rglob("*.lean")):
        theorem_names(path)  # Reject untrusted proof constructs, ignoring comments/strings.
run([sys.executable, str(ROOT / "scripts/build_serial.py")], BUILD / "build.log")
output = run([str(ROOT / "scripts/lake.sh"), "env", "lean", "scripts/Audit.lean"],
             BUILD / "axioms.log")
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
allowed = {"propext", "Classical.choice", "Quot.sound"}
used = {a for record in records for a in record["axioms"]}
if used - allowed:
    raise RuntimeError("Unexpected axioms: " + ", ".join(sorted(used - allowed)))
# A successful release audit must include the public conclusions, rather than
# merely pass for an accidentally reduced import closure.
required = {
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
missing = required - {record["name"] for record in records}
if missing:
    raise RuntimeError("Required theorem exports missing: " + ", ".join(sorted(missing)))
report = {"build_passed": True, "theorem_declarations_audited": len(records),
          "axioms_used": sorted(used), "declarations": records,
          "required_endpoints_checked": sorted(required),
          "requested_scope_formalized": True,
          "scope_exclusions": ["Fast-counting bit complexity, removed at the author's request"]}
(BUILD / "audit.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"Build passed; {len(records)} compiled theorem declarations audited; only standard axioms.")
print(f"All {len(required)} required public endpoint exports are present.")
print("Requested mathematical scope is complete; see docs/coverage.md for correspondence.")
