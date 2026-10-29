#!/usr/bin/env python3
"""Read-only Brief 07 evidence index; no imports/execution of donor code.

Only writes the requested JSON output in the lab. Names/signatures and archived
axiom output are an index, not proof replay or a semantic proof audit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import zipfile

ROOT = Path('/mnt/c/code/ecc-formal-toolset')
SKIP = {'build', '.lake', 'target', '__pycache__', 'node_modules', '.git'}


def walk(path):
    for base, dirs, files in os.walk(path):
        dirs[:] = sorted(d for d in dirs if d not in SKIP)
        for name in sorted(files):
            yield Path(base) / name


def sha(data):
    return hashlib.sha256(data).hexdigest()


def describe(origin, data):
    s = data.decode('utf-8', errors='replace')
    # Preserve theorem premises, not just attractive theorem names.
    signatures = []
    for match in re.finditer(r'(?m)^(?:private |protected )?(?:theorem|lemma)\s+', s):
        tail = s[match.start():]
        end = tail.find(':=')
        signatures.append(tail[:end if end >= 0 else 1000].strip())
    return dict(path=origin, sha256=sha(data), bytes=len(data),
                theorem_signatures=signatures,
                declared_axioms=re.findall(r'(?m)^\s*axiom\s+(\S+)', s),
                native_shortcuts=re.findall(r'\b(?:native_decide|bv_decide)\b', s),
                header=s[:s.find('namespace')] if 'namespace' in s else s[:1600])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    result = dict(scope='Source inspection and archived receipts; no new Lean/Z3/TLC replay.',
                  root=str(ROOT), routes=[], artifacts=[], axiom_logs=[])
    routes = [p for p in sorted((ROOT/'routes').iterdir()) if p.is_dir() and
              p.name.startswith(('gold-', 'ecdlp-1626q-', 'ecdlp-1669q-'))]
    for route in routes:
        row = dict(route=route.name, records={})
        for rel in ['route.json', 'contracts.json', 'validation/expected.json',
                    'evidence/seal.json', 'evidence/canonical-native-records.json',
                    'evidence/acceptance.json', 'evidence/server-acceptance.json']:
            p = route/rel
            if p.exists():
                row['records'][rel] = json.loads(p.read_text())
        result['routes'].append(row)
        for p in walk(route/'formal'):
            if p.suffix in {'.lean', '.tla', '.smt2', '.py'}:
                result['artifacts'].append(describe(str(p), p.read_bytes()))
        for p in walk(route/'evidence'):
            if p.suffix != '.log' or p.stat().st_size > 2_000_000:
                continue
            s = p.read_text(errors='replace')
            entries = []
            for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*(\[[^\]]*\])|does not depend on any axioms)", s):
                entries.append(dict(theorem=m[1], axioms=re.findall(r'[\w.]+', m[2] or '')))
            if entries:
                result['axiom_logs'].append(dict(path=str(p), entries=entries))
        # The two later sealed routes put their formal source inside ZIPs.
        for rel, prefix in [('provenance/source-inputs.zip', 'formal/'),
                            ('provenance/frozen-inputs.zip', 'route/formal/')]:
            p = route/rel
            if not p.exists():
                continue
            with zipfile.ZipFile(p) as z:
                for name in sorted(z.namelist()):
                    if name.startswith(prefix) and name.endswith(('.lean', '.tla', '.smt2', '.py')):
                        result['artifacts'].append(describe(str(p)+'!'+name, z.read(name)))
    for folder in ['formal/lean/EccFormal', 'formal/lean429', 'formal/z3', 'formal/tla', 'formal/pantograph']:
        for p in walk(ROOT/folder):
            if p.suffix in {'.lean', '.tla', '.smt2', '.py'}:
                result['artifacts'].append(describe(str(p), p.read_bytes()))
    for p in [ROOT/'formal/lean/lean-toolchain', ROOT/'README.md', ROOT/'routes/README.md']:
        result.setdefault('pins', []).append(dict(path=str(p), sha256=sha(p.read_bytes())))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(routes=len(routes), indexed_formal_files=len(result['artifacts']),
                          axiom_logs=len(result['axiom_logs']), output=str(args.output)), indent=2))


if __name__ == '__main__':
    main()
