# Brief 10 flag855 WIP

This is the preserved modular `Entrant/Streaming/` tree from the stopped Brief 10
attempt. It is not an entrant snapshot and is not scored. Its Lean imports still use
`ShorECDLP.Submission.Entrant.Streaming.*`; copy the needed files back under that module
prefix before checking them.

The following flag-correction modules were checked individually in the bench:

- `FlagCorrection/{Zero,Query,Program,Model,Pure,EndpointLogic,StateModel,Correctness,Window}.lean`
- `FlagCorrection/Pipeline.lean`
- `FlagCorrection/Counts.lean` (one harmless unused-tactic warning remains)
- `Dirty/DirtyMCX.lean`

The checked implementation is deliberately conservative: 24 unary QROM traversals and
a unitary split comparator (2,042 CCX/test). It proves the full classical endpoint action
and the prepared/actual-window semantic seam, but it is not the Brief 10 circuit.

The blocking exact circuit must interleave a 257-bit clean v-chain with the dirty 257-control
MCX and then measurement-uncompute the clean v-chain. That costs 256 + 1,020 = 1,276 CCX
and 256 measurements per zero test. The existing `computeEqConstAdaptive` cannot be used as
a black box here because it clears its scratch before the dirty chain can consume its output.
The proof should generalize `mcxVChainTailAdaptive_coherent` to admit a continuation at the
deepest conjunction, then erase the conjunction chain on return.
