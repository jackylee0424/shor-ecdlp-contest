from pathlib import Path
parts = [Path('workspace') / f'Acceptance{x}.lean' for x in ('Analytic', 'Residues', 'Peak', 'Mass')]
parts = [p for p in parts if p.exists()]
imports = list(dict.fromkeys(line for p in parts for line in p.read_text().splitlines() if line.startswith('import ')))
body = '\n\n'.join('\n'.join(line for line in p.read_text().splitlines() if not line.startswith('import ')) for p in parts)
Path('workspace/AcceptanceCheck.lean').write_text('\n'.join(imports)+'\n'+body)
