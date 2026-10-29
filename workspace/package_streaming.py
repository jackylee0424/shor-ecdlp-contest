#!/usr/bin/env python3
"""Package the modular port into the four already tracked Entrant Lean files.

The official source gate requires a fixed Git-tracked file set. This script
topologically orders the port, scopes each original module's local attributes
and options in a section, and replaces the old entrant files without Git writes.
Save a modular snapshot before running; the Streaming directory is removed.
"""
import argparse
from pathlib import Path
import re
import shutil


HEADER = '''/-!
Construction and proofs from VerifiedQC/ShorECDLP,
lamport/challenge-final-certificate @ b46e337 (Apache-2.0).
The round count is reduced from 56 to 26 using the upstream per-round
0.163 acceptance bound. The entry and decoder share streamingRounds.
Packaged into existing tracked files for the official source policy;
workspace/port_upstream.py and workspace/package_streaming.py reproduce it.
-/
'''

EXPORTS = '''namespace ShorECDLP.Entrant
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def entry := streamingEntry
def layout := batchedOuterPlan.layoutForStreaming
def bounds := streamingBounds

theorem certificate : Certificate officialLimits layout entry bounds :=
  streamingEntry_certificate_unconditional

end ShorECDLP.Entrant
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bench', type=Path, default=Path.home() / 'shorecdlp')
    parser.add_argument('--source', type=Path, help='Saved modular Streaming/ tree; preserved if supplied')
    args = parser.parse_args()
    entrant = args.bench / 'ShorECDLP/Submission/Entrant'
    source = args.source or entrant / 'Streaming'
    files = sorted(source.rglob('*.lean'))
    if not files:
        parser.error('Run workspace/port_upstream.py --rounds 26 first.')
    modules = {'ShorECDLP.Submission.Entrant.Streaming.' +
               str(p.relative_to(source).with_suffix('')).replace('/', '.'): p for p in files}
    imports = {}
    bodies = {}
    for mod, path in modules.items():
        text = path.read_text()
        imports[mod] = re.findall(r'(?m)^import\s+(\S+)\s*$', text)
        bodies[mod] = re.sub(r'(?m)^import\s+\S+\s*\n', '', text).strip()
        # Lean private aliases are file-scoped, so separate original modules may
        # reuse a private name. Give each bare private identifier a unique name;
        # qualified references to unrelated protected declarations stay intact.
        private_names = re.findall(r'\bprivate\s+(?:theorem|lemma|def|abbrev)\s+([\w\']+)',
                                   bodies[mod])
        short = mod.rsplit('.', 1)[1]
        for private in private_names:
            bodies[mod] = re.sub(r'(?<![\w\'.])' + re.escape(private) + r'(?![\w\'])',
                                 f'port_{short}_{private}', bodies[mod])
    order = []
    seen = set()
    active = set()

    def visit(mod):
        if mod in seen:
            return
        if mod in active:
            raise ValueError(f'Import cycle at {mod}')
        active.add(mod)
        for dep in imports[mod]:
            if dep in modules:
                visit(dep)
        active.remove(mod)
        seen.add(mod)
        order.append(mod)

    for mod in modules:
        visit(mod)
    # Preserve whole modules and balance source lengths along a dependency chain.
    chunks = [[] for _ in range(4)]
    total = sum(len(bodies[mod].splitlines()) for mod in order)
    assigned = 0
    chunk = 0
    for mod in order:
        if chunk < 3 and assigned >= total * (chunk + 1) / 4:
            chunk += 1
        chunks[chunk].append(mod)
        assigned += len(bodies[mod].splitlines())
    names = ('Trial', 'Success', 'WindowMass', 'Main')
    for index, (name, group) in enumerate(zip(names, chunks)):
        external = sorted({dep for mod in group for dep in imports[mod] if dep not in modules})
        if index:
            external.insert(0, f'ShorECDLP.Submission.Entrant.{names[index - 1]}')
        output = '\n'.join('import ' + dep for dep in external) + '\n\n' + HEADER
        for mod in group:
            short = mod.rsplit('.', 1)[1]
            output += f'\n/-! Upstream module: {mod} -/\nsection Port_{short}\n\n'
            output += bodies[mod] + f'\n\nend Port_{short}\n'
        if name == 'Main':
            output += '\n' + EXPORTS
        (entrant / f'{name}.lean').write_text(output)
        print(f'{name}.lean: {len(group)} modules, {len(output.splitlines())} lines')
    if args.source is None:
        shutil.rmtree(source)
    print(f'Packaged {len(order)} modules into existing tracked files.')


if __name__ == '__main__':
    main()
