import Ep488.CB

/-!
# Axiom audit for the C-B (finite-`n` Bonferroni) covering theorem

`#print axioms` for the machine-checked C-B bound and its covering criterion. Must
depend only on the three standard Mathlib axioms — no `sorryAx`, no `native_decide`.
-/

open Erdos488

#print axioms bonf_bool
#print axioms cb_bonferroni5
#print axioms floor_bound5
#print axioms cb_cover5
