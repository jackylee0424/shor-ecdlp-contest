# Patch 10 — measurement-assisted Toffoli compiler on spariev's 30-window entrant

- Owner: Brief 17.
- Base: spariev `070b740`, bench commit `a72f4af` (not the current leader tip).
- Donor: dadon `bcad5b2`, bench commit `7bc69a7`; generic temporary-AND compiler and exact certificate transport.
- Packaging: compiler and concrete counting proof are consolidated into the already-tracked `Main.lean`; no new Entrant file is created.
- Projected certified resources: 856 qubits, 11,513,899,424 T-model, 8,551,122,464 measurements, score 9,855,897,906,944.
- Projected cut versus leader dadon `bcad5b2` score 10,911,667,846,832: 9.6756055509%.
- Leader behavior: `apply.sh` exits 3 on `7bc69a7`, because that base already contains the compiler.

Verification status: pending build, axioms, boundary, official score, snapshot, and fresh-base/leader-tip apply tests.
