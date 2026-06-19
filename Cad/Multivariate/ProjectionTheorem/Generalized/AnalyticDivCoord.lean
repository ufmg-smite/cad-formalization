import Cad.Multivariate.ProjectionTheorem.Generalized.HyperplaneExtension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# M5a, brick 1 — analytic division by a coordinate

If `D` is analytic at `x₀` (with `x₀ 0 = 0`) and **vanishes on the hyperplane** `{x 0 = 0}` near `x₀`,
then `D = z₀ · G` with `G` analytic: `D z = z 0 * G z` near `x₀`. The quotient `D / z₀` is analytic off
`{z 0 = 0}` and **bounded** there (mean-value inequality: `D` vanishes on the hyperplane, so
`‖D z‖ ≤ C‖z 0‖`), hence extends analytically across the hyperplane by the removable-singularity
extension `exists_analyticAt_extend_funCoord0` (G1). This is the foundational brick for the discriminant
normal form `disc = z₀^r · N`.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace AnalyticDivCoord

variable {n : ℕ}

/-- **Analytic division by the coordinate `z 0`.** An analytic function vanishing on the hyperplane
`{z 0 = 0}` near `x₀` (with `x₀ 0 = 0`) factors as `z 0 · G` with `G` analytic at `x₀`. -/
theorem analytic_div_coord0 {D : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ} (hx0 : x₀ 0 = 0)
    (hDan : AnalyticAt ℂ D x₀)
    (hDvanish : ∀ᶠ z in 𝓝 x₀, z 0 = 0 → D z = 0) :
    ∃ G : (Fin (n + 1) → ℂ) → ℂ, AnalyticAt ℂ G x₀ ∧ (∀ᶠ z in 𝓝 x₀, D z = z 0 * G z) := by
  classical
  obtain ⟨ρ₁, hρ₁, hvanish⟩ := Metric.eventually_nhds_iff.mp hDvanish
  obtain ⟨ρ₀, hρ₀, hball_an⟩ := Metric.eventually_nhds_iff.mp hDan.eventually_analyticAt
  set ρ : ℝ := min ρ₀ ρ₁ / 2 with hρdef
  have hρ : 0 < ρ := by have := lt_min hρ₀ hρ₁; positivity
  have hρρ₀ : ρ < ρ₀ := by rw [hρdef]; have : min ρ₀ ρ₁ ≤ ρ₀ := min_le_left _ _; linarith
  have hρρ₁ : ρ < ρ₁ := by rw [hρdef]; have : min ρ₀ ρ₁ ≤ ρ₁ := min_le_right _ _; linarith
  have hDan_cb : ∀ z ∈ closedBall x₀ ρ, AnalyticAt ℂ D z := fun z hz =>
    hball_an (show dist z x₀ < ρ₀ from by have := mem_closedBall.mp hz; linarith)
  -- `fderiv D` is bounded by some `C` on the (compact) closed ball
  have hfd_cont : ContinuousOn (fderiv ℂ D) (closedBall x₀ ρ) :=
    fun z hz => ((hDan_cb z hz).fderiv.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ ρ).exists_bound_of_continuousOn hfd_cont
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ (mem_closedBall_self hρ.le))
  -- `‖D z‖ ≤ C‖z 0‖` on `ball x₀ ρ` (mean-value, `D` vanishing on the hyperplane)
  have hbound : ∀ z ∈ ball x₀ ρ, ‖D z‖ ≤ C * ‖z 0‖ := by
    intro z hz
    have hzn : ‖z - x₀‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hz
    have hfoot_le : ‖Function.update z 0 0 - x₀‖ ≤ ‖z - x₀‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      rcases eq_or_ne i 0 with h | h
      · subst h; simp only [Pi.sub_apply, Function.update_self, hx0, sub_zero, norm_zero]; positivity
      · simp only [Pi.sub_apply, Function.update_of_ne h]; exact norm_le_pi_norm (z - x₀) i
    have hfoot_cb : Function.update z 0 0 ∈ closedBall x₀ ρ := by
      rw [mem_closedBall, dist_eq_norm]; exact le_of_lt (lt_of_le_of_lt hfoot_le hzn)
    have hz_cb : z ∈ closedBall x₀ ρ := ball_subset_closedBall hz
    have hDfoot : D (Function.update z 0 0) = 0 :=
      hvanish (by rw [dist_eq_norm]; exact lt_of_le_of_lt hfoot_le (lt_trans hzn hρρ₁))
        (Function.update_self 0 0 z)
    have hmvt : ‖D z - D (Function.update z 0 0)‖ ≤ C * ‖z - Function.update z 0 0‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun x hx => (hDan_cb x hx).differentiableAt) hC
        (convex_closedBall x₀ ρ) hfoot_cb hz_cb
    have hdiff : z - Function.update z 0 0 = Pi.single 0 (z 0) := by
      funext i
      rcases eq_or_ne i 0 with h | h
      · subst h; simp [Function.update_self]
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
    rw [hDfoot, sub_zero, hdiff, Pi.norm_single] at hmvt
    exact hmvt
  -- the bounded quotient and its analyticity off the hyperplane
  have hball_nhds : ball x₀ ρ ∈ 𝓝 x₀ := isOpen_ball.mem_nhds (mem_ball_self hρ)
  have hFan : ∀ᶠ x in 𝓝 x₀, x 0 ≠ 0 → AnalyticAt ℂ (fun z => D z / z 0) x := by
    filter_upwards [hball_nhds] with x hx hx0'
    exact (hball_an (show dist x x₀ < ρ₀ from by rw [mem_ball] at hx; linarith)).div
      ((ContinuousLinearMap.proj 0 : (Fin (n + 1) → ℂ) →L[ℂ] ℂ).analyticAt x) hx0'
  have hbd : ∀ᶠ x in 𝓝 x₀, ‖(fun z => D z / z 0) x‖ ≤ C := by
    filter_upwards [hball_nhds] with x hx
    show ‖D x / x 0‖ ≤ C
    rcases eq_or_ne (x 0) 0 with h | h
    · rw [h, div_zero, norm_zero]; exact hC0
    · rw [norm_div, div_le_iff₀ (by positivity)]
      exact le_trans (hbound x hx) (by rw [mul_comm])
  obtain ⟨G, hGan, hGeq⟩ := exists_analyticAt_extend_funCoord0 hx0 hFan hbd
  refine ⟨G, hGan, ?_⟩
  filter_upwards [hGeq, hDvanish] with z hz hzv
  rcases eq_or_ne (z 0) 0 with h | h
  · rw [h, zero_mul]; exact hzv h
  · rw [hz h]; field_simp

end AnalyticDivCoord
