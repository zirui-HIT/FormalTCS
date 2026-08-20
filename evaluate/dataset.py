"""Benchmark dataset loading and per-task harness workspace materialization.

Every evaluated task exchanges data through files inside the harness workspace: the model
reads `input/` with its own tools and must write its deliverable into `output/`. Lean tasks
additionally receive a ready-to-build Lake project whose dependencies are symbolic links to
the shared prebuilt Mathlib, so no project ever downloads or rebuilds Mathlib.
"""

import hashlib
import json
import re
import shutil
from pathlib import Path

DECLARATION_RE = re.compile(r"(?m)^(theorem|lemma)\s+([^\s({\[:]+)")
NAMESPACE_END_RE = re.compile(r"^end\s+[A-Za-z0-9_.'\u00c0-\uffff]+$")
FOOTER_END_RE = re.compile(r"^end(\s+[A-Za-z0-9_.'\u00c0-\uffff]+)?$")
IMPORT_RE = re.compile(r"^(public\s+)?import\s")
PUBLIC_SECTION_RE = re.compile(r"^(@\[expose\]\s+)?public section\s*$")
PROOF_TAIL_RE = re.compile(r":=\s*by\s+sorry\s*$")
ANY_PROOF_TAIL_RE = re.compile(r":=\s*(by\b[\s\S]*|\S[\s\S]*)$")

TASKS = ("cc2nc", "nc2ft", "c2np", "ft2fp")
OUTPUT_FILES = {
    "cc2nc": "output/nl_claim.md",
    "nc2ft": "output/statement.lean",
    "c2np": "output/nl_proof.md",
    "ft2fp": "output/proof.lean",
}
DATASET_FILES = ("theorem.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json")


class DatasetError(RuntimeError):
    """Raised when dataset inputs are missing or malformed."""


def load_items(dataset_root):
    """Load every published dataset item together with its Lean theorem sources."""
    dataset_root = Path(dataset_root)
    collection = dataset_root / "collection.json"
    if not collection.is_file():
        raise DatasetError(f"dataset collection does not exist: {collection}")
    items = []
    for value in json.loads(collection.read_text(encoding="utf-8")):
        theorem_dir = dataset_root / "theorems" / value["id"]
        source = (theorem_dir / "theorem.lean").read_text(encoding="utf-8")
        parts = split_theorem_source(source)
        if not value["metainfo"]["core_label"].endswith(parts["declaration"]):
            raise DatasetError(f"declaration mismatch for {value['id']}")
        items.append(
            {
                "id": value["id"],
                "core_claim": value["core_claim"],
                "nl_theorem": value["nl_theorem"],
                "nl_proof": value["nl_proof"],
                "core_label": value["metainfo"]["core_label"],
                "paper": value["metainfo"]["paper"],
                "theorem_dir": theorem_dir,
                "theorem_source": source,
                **parts,
            }
        )
    return items


def split_theorem_source(source):
    """Split a published `theorem.lean` into preamble, bare statement, and namespace footer."""
    text = source.rstrip()
    footer = []
    while True:
        lines = text.splitlines()
        if lines and FOOTER_END_RE.fullmatch(lines[-1].strip()):
            footer.insert(0, lines[-1])
            text = "\n".join(lines[:-1]).rstrip()
            continue
        break
    without_proof, count = PROOF_TAIL_RE.subn(":=", text)
    if count != 1:
        raise DatasetError("theorem source does not end with a single `:= by sorry` proof")
    matches = list(DECLARATION_RE.finditer(without_proof))
    if not matches:
        raise DatasetError("theorem source contains no theorem or lemma declaration")
    start = matches[-1].start()
    return {
        "header": without_proof[:start].rstrip() + "\n",
        "statement": without_proof[start:].strip(),
        "footer": "\n".join(footer),
        "declaration": matches[-1].group(2),
    }


def import_block(header):
    """Return the import prologue of a preamble, which is all NC2FT hands the model."""
    lines = header.splitlines()
    last = max((index for index, line in enumerate(lines) if IMPORT_RE.match(line)), default=None)
    if last is None:
        raise DatasetError("preamble contains no import line")
    prologue = lines[: last + 1]
    prologue += [line for line in lines[last + 1 :] if PUBLIC_SECTION_RE.match(line)]
    return "\n".join(prologue) + "\n"


def split_candidate(source):
    """Split a self-contained model-written Lean file into its own header and bare statement."""
    text = source.strip()
    while True:
        lines = text.splitlines()
        if lines and FOOTER_END_RE.fullmatch(lines[-1].strip()):
            text = "\n".join(lines[:-1]).rstrip()
            continue
        break
    matches = list(DECLARATION_RE.finditer(text))
    if not matches:
        raise DatasetError("candidate contains no theorem or lemma declaration")
    start = matches[-1].start()
    header = text[:start].rstrip()
    return {
        "header": header + "\n" if header else "",
        "statement": strip_proof(text[start:]),
    }


def strip_proof(statement):
    """Reduce a possibly proved theorem to its statement ending in `:=`."""
    text = statement.strip()
    matches = list(DECLARATION_RE.finditer(text))
    if matches:
        text = text[matches[-1].start():].strip()
    text = PROOF_TAIL_RE.sub(":=", text)
    if text.endswith(":="):
        return text
    return ANY_PROOF_TAIL_RE.sub(":=", text)


def normalize_statement(statement):
    """Normalize whitespace so statement equality ignores formatting only."""
    return re.sub(r"\s+", " ", strip_proof(statement)).strip()


def fingerprint(paths):
    """Return a stable digest of the immutable inputs handed to one harness session."""
    digest = hashlib.sha256()
    for path in sorted(Path(part) for part in paths):
        digest.update(path.name.encode("utf-8"))
        digest.update(path.read_bytes() if path.is_file() else b"")
    return digest.hexdigest()


def attach_shared_packages(project_root, mathlib_root):
    """Link the shared prebuilt Mathlib and its dependencies into a Lake project."""
    mathlib_root = Path(mathlib_root)
    packages = Path(project_root) / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    links = {"mathlib": mathlib_root}
    shared = mathlib_root / ".lake" / "packages"
    if shared.is_dir():
        links.update({path.name: path for path in shared.iterdir() if path.is_dir()})
    for name, source in links.items():
        destination = packages / name
        if destination.is_symlink() or destination.exists():
            continue
        destination.symlink_to(source, target_is_directory=True)


def _write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _lakefile(source, lean_jobs):
    """Rewrite the published Lake configuration to compile with the requested concurrency."""
    replaced, count = re.subn(
        r'(?m)^moreLeanArgs\s*=.*$', f'moreLeanArgs = ["-j", "{lean_jobs}"]', source
    )
    if count:
        return replaced
    return source.rstrip() + f'\n\nmoreLeanArgs = ["-j", "{lean_jobs}"]\n'


def _check_script(lean_root, target, lean_jobs, strict):
    strict_flags = " -Dwarn.sorry=true -DwarningAsError=true" if strict else ""
    return (
        "#!/bin/bash\n"
        "# Type-check the Lean file of this task. Run it as often as you need.\n"
        "set -uo pipefail\n"
        f'export LEAN_ROOT="{lean_root}"\n'
        'export PATH="$LEAN_ROOT/bin:$PATH"\n'
        'cd "$(dirname "$0")/project"\n'
        f'exec lake env lean -j {lean_jobs}{strict_flags} -- {target}\n'
    )


def _lean_project(workspace, item, lean_root, mathlib_root, lean_jobs, sources):
    project = workspace / "project"
    project.mkdir(parents=True, exist_ok=True)
    for name in DATASET_FILES[1:]:
        source = item["theorem_dir"] / name
        target = project / name
        if name == "lakefile.toml":
            _write(target, _lakefile(source.read_text(encoding="utf-8"), lean_jobs))
        else:
            shutil.copyfile(source, target)
    for name, content in sources.items():
        _write(project / name, content)
    attach_shared_packages(project, mathlib_root)
    return project


def prepare_workspace(config, item, task, workspace, *, instructions):
    """Materialize the immutable inputs, the empty output slot, and the task brief."""
    workspace = Path(workspace)
    inputs = workspace / "input"
    if inputs.is_dir():
        shutil.rmtree(inputs)
    inputs.mkdir(parents=True)
    (workspace / "output").mkdir(parents=True, exist_ok=True)
    lean_root = config["lean_root"]
    lean_jobs = int(config["lean_jobs"])
    if task == "cc2nc":
        _write(inputs / "core_claim.md", item["core_claim"].strip() + "\n")
    elif task == "nc2ft":
        imports = import_block(item["header"])
        _write(inputs / "nl_claim.md", item["nl_theorem"].strip() + "\n")
        _write(inputs / "imports.lean", imports)
        _lean_project(
            workspace,
            item,
            lean_root,
            config["mathlib_root"],
            lean_jobs,
            {"candidate.lean": imports + "\n-- Write your definitions and theorem statement here.\n"},
        )
        _write(workspace / "check.sh", _check_script(lean_root, "candidate.lean", lean_jobs, False))
        (workspace / "check.sh").chmod(0o755)
    elif task == "c2np":
        _write(inputs / "nl_claim.md", item["nl_theorem"].strip() + "\n")
        _write(inputs / "theorem.lean", item["theorem_source"])
    elif task == "ft2fp":
        _write(inputs / "theorem.lean", item["theorem_source"])
        _lean_project(
            workspace,
            item,
            lean_root,
            config["mathlib_root"],
            lean_jobs,
            {"theorem.lean": item["theorem_source"]},
        )
        _write(workspace / "check.sh", _check_script(lean_root, "theorem.lean", lean_jobs, True))
        (workspace / "check.sh").chmod(0o755)
    else:
        raise DatasetError(f"unknown task: {task}")
    _write(workspace / "TASK.md", instructions)
    return fingerprint([path for path in sorted(inputs.iterdir()) if path.is_file()])


def output_path(workspace, task):
    """Return the deliverable this task requires the model to write."""
    return Path(workspace) / OUTPUT_FILES[task]


def clear_output(workspace):
    """Empty the output slot so a stale deliverable cannot be mistaken for a fresh answer."""
    directory = Path(workspace) / "output"
    if directory.is_dir():
        shutil.rmtree(directory)
    directory.mkdir(parents=True)


def read_output(workspace, task):
    """Return the deliverable content, or None when the model produced nothing usable."""
    path = output_path(workspace, task)
    if not path.is_file():
        return None
    content = path.read_text(encoding="utf-8", errors="replace").strip()
    return content or None
