# workspace — scratch that never goes into the bench

- `*.lean` scratch: elaborate with `formal-tools/check.sh workspace/<file>.lean`. Files may import any
  built bench module, e.g. `import ShorECDLP.Submission.Entrant.Main`.
- `*.py` calculators: resource arithmetic (qubits, T counts, success-probability margins). Run them
  before proving anything.
- Name files `<topic>_<what>.lean/py`. Delete stale scratch freely, but keep anything referenced from work-notes.
- When a lemma is ready, move it into `bench/ShorECDLP/Submission/Entrant/` (the only editable bench path).
