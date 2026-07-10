import Ep488.Density

/-!
# Axiom audit for the density reduction (`2δ > S`, floor-free form)

`#print axioms` for the machine-checked second-order-charge reduction. The reduction
(`sum_terms_eq_Q` + `Q_pos_of_E4_bounds`) must depend only on the three standard
Mathlib axioms — no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).

`Q_pos_of_E4_bounds` is *conditional*: it takes the finite kernel `E4 ≥ 157/300`
(as `157/300 ≤ x · brX` per element) as an explicit hypothesis. That kernel is
exhaustively computationally verified and proved on paper (see
`../../quintuple_density_notes.md`); here Lean certifies the reduction around it.
-/

open Erdos488.Density

#print axioms sum_terms_eq_Q
#print axioms term_ge
#print axioms term_pos
#print axioms Q_pos_of_E4_bounds
#print axioms Q_ge_margin
