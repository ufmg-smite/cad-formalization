import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Analytic submanifolds of `ℝⁿ`

McCallum's (p.20) definition of an analytic `s`-dimensional submanifold of `ℝⁿ`,
expressed via the regular value theorem (zero set of an analytic submersion).
-/

noncomputable section

open Set

variable {n : ℕ}

/-- `S` is an analytic `s`-dimensional submanifold of `ℝⁿ` (McCallum, Definition
p.20). For each `p ∈ S` there exist an open neighborhood `W` of `p` and an
analytic map `F : ℝⁿ → ℝ^{n-s}` for which `p` is a regular point (the Fréchet
derivative of `F` at `p` is surjective), such that `S ∩ W` is exactly the zero
set of `F` inside `W`. -/
def IsAnalyticSubmanifold (S : Set (Fin n → ℝ)) : Prop :=
  S.Nonempty ∧
  ∃ s : ℕ, s ≤ n ∧
    ∀ p ∈ S, ∃ W : Set (Fin n → ℝ), IsOpen W ∧ p ∈ W ∧
      ∃ F : (Fin n → ℝ) → (Fin (n - s) → ℝ),
        AnalyticOnNhd ℝ F W ∧
        Function.Surjective (fderiv ℝ F p) ∧
        (∀ x ∈ W, x ∈ S ↔ F x = 0)

end

#min_imports
