import Cad.Multivariate.ProjectionTheorem.Generalized.MonodromyDeform
import Cad.Multivariate.ProjectionTheorem.Generalized.HyperplaneExtension
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# M5 (e=1, sub-lemma A) — the punctured ball is preconnected

`punctBall δ = ball 0 δ ∩ {z | z 0 ≠ 0}` in `Fin (n+1) → ℂ` is preconnected: under the coordinate split
`coord0Equiv : (Fin n → ℂ) × ℂ ≃L Fin (n+1) → ℂ` it is the product of the convex base ball with the
*punctured complex disc* `ball 0 δ \ {0}` (path-connected since `rank_ℝ ℂ = 2 > 1`), and a product of
preconnected sets is preconnected (transported through the homeomorphism).
-/

noncomputable section

open Polynomial Filter Metric Set
open scoped Topology

namespace MonodromyDeform

variable {n : ℕ}

/-- The pi-norm of `z` is `< δ` iff both the `0`-th coordinate and the tail have pi-norm `< δ`. -/
private lemma norm_lt_iff_tail {δ : ℝ} (hδ : 0 < δ) (z : Fin (n + 1) → ℂ) :
    ‖z‖ < δ ↔ ‖Fin.tail z‖ < δ ∧ ‖z 0‖ < δ := by
  rw [pi_norm_lt_iff hδ, pi_norm_lt_iff hδ, Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, hsucc⟩; exact ⟨hsucc, h0⟩
  · rintro ⟨hsucc, h0⟩; exact ⟨h0, hsucc⟩

/-- **(A) The punctured ball is preconnected.** -/
theorem punctBall_isPreconnected {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected (punctBall (n := n) δ) := by
  -- the base ball (convex) times the punctured complex disc (path-connected)
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hP : IsPreconnected
      ((ball (0 : Fin n → ℂ) δ) ×ˢ ((ball (0 : ℂ) δ) \ {0})) :=
    (convex_ball _ _).isPreconnected.prod
      (isPathConnected_ball_diff_singleton hrank hδ).isConnected.isPreconnected
  have himg := hP.image _ (coord0Equiv (n := n)).continuous.continuousOn
  -- the image is exactly `punctBall δ`
  have hset : coord0Equiv (n := n) ''
      ((ball (0 : Fin n → ℂ) δ) ×ˢ ((ball (0 : ℂ) δ) \ {0})) = punctBall (n := n) δ := by
    ext z
    constructor
    · rintro ⟨⟨v, w⟩, ⟨hv, hw, hw0⟩, rfl⟩
      rw [mem_punctBall]
      refine ⟨?_, ?_⟩
      · rw [coord0Equiv_apply, norm_lt_iff_tail hδ]
        refine ⟨?_, ?_⟩
        · rw [Fin.tail_cons]; exact mem_ball_zero_iff.mp hv
        · rw [Fin.cons_zero]; exact mem_ball_zero_iff.mp hw
      · rw [coord0Equiv_apply, Fin.cons_zero]; exact hw0
    · intro hz
      rw [mem_punctBall] at hz
      refine ⟨(Fin.tail z, z 0), ⟨?_, ?_, ?_⟩, ?_⟩
      · exact mem_ball_zero_iff.mpr ((norm_lt_iff_tail hδ z).mp hz.1).1
      · exact mem_ball_zero_iff.mpr ((norm_lt_iff_tail hδ z).mp hz.1).2
      · exact hz.2
      · rw [coord0Equiv_apply, Fin.cons_self_tail]
  rwa [hset] at himg

end MonodromyDeform
