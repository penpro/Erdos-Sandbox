import Ep488.Basic
/-!
Axiom audit: each core lemma depends only on the three standard Lean/Mathlib
axioms (`propext`, `Classical.choice`, `Quot.sound`) and NOT on `sorryAx`.
The captured output is in `../axioms-check.txt`.
-/
open Erdos488
#print axioms floor_bound
#print axioms ratio_bounds
#print axioms odd_cofactor
#print axioms parity_dichotomy
