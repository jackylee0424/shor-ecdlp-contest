# Lean tips for this codebase (append what you learn)

- Elaborate a single file quickly: `formal-tools/check.sh <file>`. Use `build.sh` only to produce oleans
  for downstream modules or before scoring.
- Scratch files in `workspace/` can `import ShorECDLP.Submission.Entrant.Main` (or any bench module), as long as
  the module has been built.
- Metrics are **kernel-reduced** by the judge, so `bounds` must be numeric literals, and resource proofs
  must not rely on `native_decide`/`#eval`. The baseline marks `tableE progE Straight.WellFormed`
  `[local irreducible]` to keep the certificate term cheap. Copy that pattern.
- Large numerals: `set_option exponentiation.threshold 300 in`, as in `Entrant/Main.lean` `hwinE`.
- Deep terms: `set_option maxRecDepth 100000 in`.
