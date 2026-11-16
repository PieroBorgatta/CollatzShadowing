#!/usr/bin/env python3
"""Export the standalone Lean snapshot or verify its recorded bytes.

The research repository is authoritative. This tool copies a narrow allowlist;
it never copies build caches, credentials, experiments, or external projects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import posixpath
import re
import subprocess
from pathlib import Path

DEST = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/PieroBorgatta/Collatz"
MANIFEST = DEST / "SOURCE_MANIFEST.json"
AUDITS = {
    "notes/research_sprint_2026-11-13/verification/AllNewDependencyAudit.lean":
        "verification/November13DependencyAudit.lean",
    "notes/research_sprint_2026-11-15/verification/AllNewDependencyAudit.lean":
        "verification/November15DependencyAudit.lean",
    "notes/research_sprint_2026-11-15_three_hours/verification/AllNewDependencyAudit.lean":
        "verification/FiniteCatalogueDependencyAudit.lean",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rewrite_links(data: bytes, source: str, commit: str) -> bytes:
    """Keep library-local links; pin links outside lean/ to canonical history."""
    text = data.decode("utf-8")

    def replace(match: re.Match[str]) -> str:
        target = match.group(1)
        if not target.startswith("../"):
            return match.group(0)
        path, marker, anchor = target.partition("#")
        resolved = posixpath.normpath(posixpath.join(posixpath.dirname(source), path))
        if resolved.startswith("lean/"):
            return match.group(0)
        if resolved.startswith("../"):
            raise ValueError(f"Link escapes canonical repository: {source}: {target}")
        suffix = f"#{anchor}" if marker else ""
        return f"]({REPOSITORY}/blob/{commit}/{resolved}{suffix})"

    return re.sub(r"\]\(([^)]+)\)", replace, text).encode("utf-8")


def export(source: Path) -> None:
    source = source.resolve()
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=source, text=True
    ).strip()
    mapping = {
        "lean/CollatzShadowing.lean": "CollatzShadowing.lean",
        "lean/lakefile.toml": "lakefile.toml",
        "lean/lake-manifest.json": "lake-manifest.json",
        "lean/lean-toolchain": "lean-toolchain",
        "lean/STATUS.md": "STATUS.md",
        "LICENSE": "LICENSE",
        **AUDITS,
    }
    for file in sorted((source / "lean/CollatzShadowing").rglob("*")):
        if file.is_file() and file.suffix in {".lean", ".md"}:
            rel = str(file.relative_to(source))
            mapping[rel] = str(file.relative_to(source / "lean"))

    proof_paths = [key for key in mapping if key.endswith(".lean")]
    dirty = subprocess.check_output(
        ["git", "status", "--porcelain", "--", *mapping.keys()],
        cwd=source, text=True,
    ).splitlines()
    dirty_proofs = [line for line in dirty if any(line.endswith(p) for p in proof_paths)]
    if dirty_proofs:
        raise RuntimeError("Commit canonical Lean/audit changes before export: " + repr(dirty_proofs))

    records = []
    for original, target in sorted(mapping.items()):
        original_data = (source / original).read_bytes()
        data = rewrite_links(original_data, original, commit) if target.endswith(".md") else original_data
        dest = DEST / target
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        records.append({
            "source": original, "path": target,
            "source_sha256": sha(original_data), "sha256": sha(data),
            "bytes": len(data),
            "transformation": "external documentation links pinned to canonical commit"
                if data != original_data else "byte-for-byte copy",
        })
    manifest = {
        "schema": 1,
        "snapshot": "v7 standalone library",
        "canonical_repository": REPOSITORY,
        "canonical_commit": commit,
        "canonical_proof_files_clean": True,
        "canonical_uncommitted_exported_documents": dirty,
        "license": "CC-BY-4.0",
        "historical_license_notice": "LICENSE-MIT preserves the earlier MIT grant; it is not revoked.",
        "library_lean_modules": sum(x["path"].startswith("CollatzShadowing/")
                                    and x["path"].endswith(".lean") for x in records),
        "standalone_prototypes_included": False,
        "files": records,
    }
    MANIFEST.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    print(f"Exported {len(records)} files from {commit}; {manifest['library_lean_modules']} library modules.")


def verify() -> None:
    manifest = json.loads(MANIFEST.read_text())
    expected = {item["path"] for item in manifest["files"]
                if item["path"].endswith(".lean")}
    actual = {"CollatzShadowing.lean"}
    actual.update(str(f.relative_to(DEST)) for f in
                  (DEST / "CollatzShadowing").rglob("*.lean"))
    actual.update(str(f.relative_to(DEST)) for f in
                  (DEST / "verification").rglob("*.lean"))
    if actual != expected:
        raise RuntimeError(f"Lean source inventory mismatch: missing={expected-actual}, extra={actual-expected}")
    for item in manifest["files"]:
        file = DEST / item["path"]
        if not file.is_file() or sha(file.read_bytes()) != item["sha256"]:
            raise RuntimeError("Snapshot byte mismatch: " + item["path"])
    print(f"Verified {len(manifest['files'])} exported files against SOURCE_MANIFEST.json.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="Canonical Collatz checkout; required for export")
    parser.add_argument("--check", action="store_true", help="Verify local bytes only")
    args = parser.parse_args()
    if args.check:
        verify()
    elif args.source:
        export(args.source)
        verify()
    else:
        parser.error("Provide --source or --check")
