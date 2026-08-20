"""Shared-workspace materialization and claim scaffolding for the agent loop.

One generation run owns one workspace under the temp root: the sampled benchmark instances,
the objectives the planner proposes, the accepted claims, the feedback of discarded attempts,
and one Lean project per claim that the formalizer iterates on. Accepted statements are
published under ``results/theorems/<claim_id>/`` in the same format as the published dataset.
"""

import json
import re
import shutil
from pathlib import Path

import runtime  # noqa: E402  (bootstraps sys.path for the evaluate modules)
import dataset as evaluate_dataset  # noqa: E402  (evaluate)
from utils.filesystem import write_text
from utils.leanmarathon.verify_blueprint import mask_comments_and_strings

SUPPORT_FILES = ("lakefile.toml", "lean-toolchain", "lake-manifest.json")
FORBIDDEN_TOKENS = ("sorryAx", "sorry_using", "admit", "stop", "axiom", "native_decide", "Lean.trustCompiler")
DOTTED_NAME_TOKENS = frozenset({"sorry", "admit", "stop"})
PLACEHOLDER = (
    "-- Write the formal statement here: narrow Mathlib imports, auxiliary definitions,\n"
    "-- and exactly one main theorem or lemma as the last declaration, proved `by sorry`.\n"
)


class WorkspaceError(RuntimeError):
    """Raised when the workspace or a claim cannot be materialized."""


def load_benchmark(config):
    """Load every published dataset item together with its Lean theorem sources."""
    return evaluate_dataset.load_items(config["dataset_root"])


def sample_benchmark(items, size, seed):
    """Randomly sample the benchmark instances that seed one generation run."""
    import random

    return random.Random(seed).sample(list(items), min(int(size), len(items)))


def init_run_workspace(config, items, workspace):
    """Materialize the sampled benchmark into the shared workspace (idempotent)."""
    workspace = Path(workspace)
    if (workspace / "benchmark").is_dir():
        return workspace
    if workspace.exists():
        shutil.rmtree(workspace)
    for name in ("benchmark", "objectives", "accepted", "feedback", "claims"):
        (workspace / name).mkdir(parents=True)
    for item in items:
        target = workspace / "benchmark" / item["id"]
        target.mkdir()
        write_text(target / "core_claim.md", item["core_claim"].strip() + "\n")
        write_text(target / "nl_theorem.md", item["nl_theorem"].strip() + "\n")
        write_text(target / "theorem.lean", item["theorem_source"])
    return workspace


def check_script(config, target, strict):
    """Return the content of one claim's compile script."""
    strict_flags = " -Dwarn.sorry=true -DwarningAsError=true" if strict else ""
    return (
        "#!/bin/bash\n"
        "# Type-check the Lean file of this task. Run it as often as you need.\n"
        "set -uo pipefail\n"
        f'export LEAN_ROOT="{config["lean_root"]}"\n'
        'export PATH="$LEAN_ROOT/bin:$PATH"\n'
        'cd "$(dirname "$0")/project"\n'
        f'exec lake env lean -j {int(config["lean_jobs"])}{strict_flags} -- {target}\n'
    )


def scaffold_claim(config, claim_workspace, template_item):
    """Create the formalizer's working directory and its ready-to-build Lean project."""
    claim_workspace = Path(claim_workspace)
    project = claim_workspace / "project"
    project.mkdir(parents=True)
    for name in SUPPORT_FILES:
        shutil.copyfile(template_item["theorem_dir"] / name, project / name)
    write_text(project / "theorem.lean", PLACEHOLDER)
    script = claim_workspace / "check.sh"
    write_text(script, check_script(config, "theorem.lean", False))
    script.chmod(0o755)
    evaluate_dataset.attach_shared_packages(project, config["mathlib_root"])
    return claim_workspace


def forbidden_tokens(masked):
    """Return the proof-bypassing tokens appearing outside comments and strings."""
    found = []
    for token in FORBIDDEN_TOKENS:
        boundary = r"(?<![\w'.])" if token in DOTTED_NAME_TOKENS else r"(?<![\w'])"
        if re.search(boundary + re.escape(token) + r"(?![\w'])", masked):
            found.append(token)
    return found


def validate_theorem(source):
    """Check one formalizer-written theorem file; return parts and issues."""
    issues = []
    masked = mask_comments_and_strings(source)
    if source.strip() == PLACEHOLDER.strip():
        issues.append("theorem.lean was not written")
    issues.extend(f"forbidden token in theorem source: {token}" for token in forbidden_tokens(masked))
    if len(re.findall(r"(?<![\w'.])sorry(?![\w'])", masked)) != 1:
        issues.append("theorem source must contain exactly one `sorry`, as the main declaration's proof")
    try:
        parts = evaluate_dataset.split_theorem_source(source)
    except evaluate_dataset.DatasetError as error:
        return None, issues + [str(error)]
    return parts, issues


NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.'\u00c0-\uffff]+)", re.MULTILINE)
NAMED_END_RE = re.compile(r"^end\s+([A-Za-z0-9_.'\u00c0-\uffff]+)$")


def qualified_declaration(parts):
    """Return the declaration name qualified by every namespace open around it."""
    footer_names = []
    for line in parts.get("footer", "").splitlines():
        match = NAMED_END_RE.fullmatch(line.strip())
        if match:
            footer_names.append(match.group(1))
    opened = NAMESPACE_RE.findall(parts.get("header", ""))
    # Namespaces opened in the header and closed after the declaration stay open around it,
    # in header order (outermost first).
    open_namespaces = [name for name in opened if name in footer_names]
    prefix = ".".join(open_namespaces)
    return f"{prefix}.{parts['declaration']}" if prefix else parts["declaration"]


def publish_theorem(config, claim_workspace, claim_id):
    """Validate and publish one accepted claim's theorem project into results."""
    claim_workspace = Path(claim_workspace)
    source = (claim_workspace / "project" / "theorem.lean").read_text(encoding="utf-8")
    parts, issues = validate_theorem(source)
    if issues:
        return None, issues
    target = Path(config["results_root"]) / "theorems" / runtime.safe_name(claim_id)
    target.mkdir(parents=True, exist_ok=True)
    write_text(target / "theorem.lean", source.rstrip() + "\n")
    for name in SUPPORT_FILES:
        shutil.copyfile(claim_workspace / "project" / name, target / name)
    return {
        "claim_id": claim_id,
        "theorem_dir": str(target),
        "core_label": qualified_declaration(parts),
        "header": parts["header"],
        "statement": parts["statement"],
    }, []


def accepted_summary(accepted_dir, claim_id, verdict, published):
    """Write one accepted claim's natural-language summary into the shared workspace."""
    target = Path(accepted_dir)
    target.mkdir(parents=True, exist_ok=True)
    write_text(
        target / "claim.md",
        "# Accepted claim\n\n"
        f"- claim id: `{claim_id}`\n"
        f"- natural-language claim: {verdict['nl_claim']}\n"
        f"- significance: {verdict.get('significance', '')}\n"
        f"- judger rationale: {verdict.get('rationale', '')}\n",
    )
    shutil.copyfile(
        Path(published["theorem_dir"]) / "theorem.lean",
        target / "theorem.lean",
    )
    return target


def read_claims(config):
    """Return every published accepted-claim record."""
    path = Path(config["results_root"]) / "claims.jsonl"
    if not path.is_file():
        return []
    claims = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            claims.append(json.loads(line))
    return claims
