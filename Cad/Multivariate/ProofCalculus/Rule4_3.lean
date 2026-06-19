import Cad.Multivariate.ProofCalculus.Basic

namespace ProofCalculus

-- Note that MvPolynomial (Fin 0) ℝ is isomorphic to ℝ:
/- variable (p : MvPolynomial (Fin 0) ℝ) -/

/- def empty_assign : Fin 0 → ℝ := by -/
/-   intro abs -/
/-   cases abs -/
/-   linarith -/

/- #check MvPolynomial.eval empty_assign p -- ℝ -/

theorem nalbach_4_3_part1 (p : MvPolynomial (Fin 0) ℝ) : sgn_inv 0 Set.univ p := by
  intros a ha b hb
  have : a = b := List.ofFn_inj.mp rfl
  rw [this]

theorem nalbach_4_3_part2 (p : MvPolynomial (Fin 0) ℝ) : ord_inv 0 Set.univ p := by
  intros a ha b hb
  have : a = b := List.ofFn_inj.mp rfl
  rw [this]

end ProofCalculus
