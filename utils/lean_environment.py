"""Shared Lean library discovery and cache-facade helpers."""

from pathlib import Path


def project_lean_paths(project_root, include_packages=True):
    """Return existing compiled Lean library paths for one Lake project."""
    root = Path(project_root)
    paths = [root / ".lake" / "build" / "lib" / "lean"]
    packages = root / ".lake" / "packages"
    if include_packages and packages.is_dir():
        paths.extend(sorted(path / ".lake" / "build" / "lib" / "lean" for path in packages.iterdir()))
    return [path.resolve() for path in paths if path.is_dir()]


def reusable_lean_paths(mathlib_root, additional_projects=()):
    """Collect unique compiled Lean paths shared across pipeline projects."""
    candidates = project_lean_paths(mathlib_root)
    for project in additional_projects:
        candidates.extend(project_lean_paths(project))
    paths = []
    seen = set()
    for path in candidates:
        resolved = path.resolve()
        if resolved not in seen:
            paths.append(resolved)
            seen.add(resolved)
    return paths


def ensure_lean_facade(target, sources, package_name, write_text, error_type=RuntimeError):
    """Create a Lake package that links to shared compiled Lean artifacts."""
    target = Path(target)
    lean = target / ".lake" / "build" / "lib" / "lean"
    lakefile = target / "lakefile.lean"
    content = f"import Lake\nopen Lake DSL\n\npackage {package_name}\n"
    if not lakefile.is_file() or lakefile.read_text(encoding="utf-8") != content:
        write_text(lakefile, content)
    lean.mkdir(parents=True, exist_ok=True)
    for source_root in sources:
        for source in Path(source_root).iterdir():
            destination = lean / source.name
            if not destination.exists():
                destination.symlink_to(source, target_is_directory=source.is_dir())
            elif destination.is_symlink() and destination.resolve() != source.resolve():
                destination.unlink()
                destination.symlink_to(source, target_is_directory=source.is_dir())
            elif destination.resolve() != source.resolve():
                raise error_type(f"Conflicting shared Lean artifact: {destination}")
    return target.resolve()
