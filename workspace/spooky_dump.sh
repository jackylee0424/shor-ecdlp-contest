#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
O=/mnt/c/code/shor-ecdlp-contest/workspace/spooky_src
for f in BatchedEndpoint EndpointTransposition BatchState BatchExecution BatchCost BatchPlacement BatchQuery BatchTemplate EndpointLoad EndpointQROM EndpointSwap EndpointSandwich PreparedBatch PlacedBatch BatchSupport BatchBoundary WindowBody FixedMatching FixedNetwork FixedWord RegisterEquality VChain BatchCoherent BatchFrame BatchPhysical Endpoint EndpointEncoding SharedTable; do
  git show $R:ShorECDLP/Submission/2607_13816/Challenge/$f.lean > $O/$f.lean 2>/dev/null
done
cp ShorECDLP/Framework/Quantum/MeasurementUncompute.lean $O/
wc -l $O/*.lean
