#!/bin/bash
cd ~/shorecdlp
grep -n -A12 "inductive TemplateGate" ShorECDLP/Challenge/Template.lean
grep -n -A8 "inductive PointField" -r ShorECDLP/Challenge/ | head -30
grep -n "ConstantBit" ShorECDLP/Challenge/Template.lean | head -5
