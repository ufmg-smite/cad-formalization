import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Brick: differentiating a parametric circle integral

`circleIntegral_hasDerivAt`: if `Φ` and its `z`-derivative `Φ'` are jointly continuous on
`closedBall z₀ δ × sphere c R` and `Φ(·, ζ)` has derivative `Φ'(z, ζ)` in `z` there, then
`z ↦ ∮_{C(c,R)} Φ(z, ζ) dζ` has derivative `∮_{C(c,R)} Φ'(z₀, ζ) dζ` at `z₀` (differentiate under the
integral sign). Foundational brick of the Cauchy-integral proof of `weierstrass_division`.
-/

noncomputable section

open Complex Metric MeasureTheory intervalIntegral Filter Topology Set Real

/-! ## Multi-parameter version (parameter in a complex normed space `H`)

`HasFDerivAt` of `z ↦ ∮ Φ(z,ζ) dζ` for `z ∈ H`. This gives `DifferentiableOn` of the keystone
integrand on an open set of `ℂⁿ` — isolating the remaining gap to *exactly* the several-variable
holomorphy⇒analyticity bridge (`DifferentiableOn ℂ ⇒ AnalyticOnNhd ℂ`, `CBridge.osgood`). -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H]

/-- **Differentiate (Fréchet) under a parametric circle integral**, parameter in `H`. -/
theorem circleIntegral_hasFDerivAt
    {Φ : H → ℂ → ℂ} {Φ' : H → ℂ → (H →L[ℂ] ℂ)} {c : ℂ} {R : ℝ} {z₀ : H} {δ : ℝ}
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hΦ : ContinuousOn (fun p : H × ℂ => Φ p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hΦ' : ContinuousOn (fun p : H × ℂ => Φ' p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hderiv : ∀ z ∈ ball z₀ δ, ∀ ζ ∈ sphere c R, HasFDerivAt (fun w => Φ w ζ) (Φ' z ζ) z) :
    HasFDerivAt (fun z => ∮ ζ in C(c, R), Φ z ζ) (∮ ζ in C(c, R), Φ' z₀ ζ) z₀ := by
  set K : Set (H × ℂ) := closedBall z₀ δ ×ˢ sphere c R with hK
  have hK_compact : IsCompact K := (isCompact_closedBall z₀ δ).prod (isCompact_sphere c R)
  obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn hΦ'.norm
  have hmemK : ∀ z ∈ ball z₀ δ, ∀ θ : ℝ, ((z, circleMap c R θ) : H × ℂ) ∈ K :=
    fun z hz θ => ⟨ball_subset_closedBall hz, circleMap_mem_sphere c hR θ⟩
  have hslice : ∀ z ∈ ball z₀ δ, Continuous (fun θ : ℝ => Φ z (circleMap c R θ)) := by
    intro z hz
    have hc : ContinuousOn (fun ζ : ℂ => Φ z ζ) (sphere c R) :=
      hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun ζ hζ => ⟨ball_subset_closedBall hz, hζ⟩)
    exact hc.comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR θ)
  have hslice' : ∀ z ∈ ball z₀ δ, Continuous (fun θ : ℝ => Φ' z (circleMap c R θ)) := by
    intro z hz
    have hc : ContinuousOn (fun ζ : ℂ => Φ' z ζ) (sphere c R) :=
      hΦ'.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun ζ hζ => ⟨ball_subset_closedBall hz, hζ⟩)
    exact hc.comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR θ)
  set F : H → ℝ → ℂ := fun z θ => deriv (circleMap c R) θ • Φ z (circleMap c R θ) with hF
  set F' : H → ℝ → (H →L[ℂ] ℂ) := fun z θ => deriv (circleMap c R) θ • Φ' z (circleMap c R θ) with hF'
  have hderiv_cont : Continuous (deriv (circleMap c R)) := by
    rw [show deriv (circleMap c R) = fun θ => circleMap 0 R θ * I from funext (deriv_circleMap c R)]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hFcont : ∀ z ∈ ball z₀ δ, Continuous (F z) :=
    fun z hz => hderiv_cont.smul (hslice z hz)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := F') (x₀ := z₀) (s := ball z₀ δ) (bound := fun _ => R * M) (μ := volume)
    (a := 0) (b := 2 * π)
    (ball_mem_nhds z₀ hδ)
    (eventually_of_mem (ball_mem_nhds z₀ hδ) (fun z hz => (hFcont z hz).aestronglyMeasurable))
    ((hFcont z₀ (mem_ball_self hδ)).intervalIntegrable 0 (2 * π))
    (hderiv_cont.smul (hslice' z₀ (mem_ball_self hδ))).aestronglyMeasurable
    (ae_of_all _ fun θ _ z hz => by
      have hnorm : ‖F' z θ‖ = R * ‖Φ' z (circleMap c R θ)‖ := by
        rw [hF']
        simp only [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one,
          abs_of_nonneg hR]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hM _ (hmemK z hz θ))) hR)
    (intervalIntegrable_const)
    (ae_of_all _ fun θ _ z hz =>
      (hderiv z hz (circleMap c R θ) (circleMap_mem_sphere c hR θ)).const_smul
        (deriv (circleMap c R) θ))

/-- **Differentiability on a neighborhood** (multi-parameter). The keystone integrand is
`DifferentiableOn ℂ` on an open ball of the parameter space `H`. The *only* thing now standing
between this and the multi-parameter keystone (`AnalyticAt`) is the several-variable
holomorphy⇒analyticity bridge `DifferentiableOn ℂ ⇒ AnalyticOnNhd ℂ` (`CBridge.osgood`). -/
theorem circleIntegral_differentiableOn_multi
    {Φ : H → ℂ → ℂ} {Φ' : H → ℂ → (H →L[ℂ] ℂ)} {c : ℂ} {R : ℝ} {z₀ : H} {δ : ℝ}
    (hR : 0 ≤ R) (hΦ : ContinuousOn (fun p : H × ℂ => Φ p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hΦ' : ContinuousOn (fun p : H × ℂ => Φ' p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hderiv : ∀ z ∈ ball z₀ δ, ∀ ζ ∈ sphere c R, HasFDerivAt (fun w => Φ w ζ) (Φ' z ζ) z) :
    DifferentiableOn ℂ (fun z => ∮ ζ in C(c, R), Φ z ζ) (ball z₀ δ) := by
  intro z hz
  have hr_lt : dist z z₀ < δ := mem_ball.mp hz
  set δ' := (δ - dist z z₀) / 2 with hδ'
  have hδ'pos : 0 < δ' := by rw [hδ']; linarith
  have hsubc : closedBall z δ' ⊆ closedBall z₀ δ := by
    intro w hw
    have h1 : dist w z ≤ δ' := mem_closedBall.mp hw
    have h2 : dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
    rw [mem_closedBall, hδ'] at *; linarith
  have hsubb : ball z δ' ⊆ ball z₀ δ := by
    intro w hw
    have h1 : dist w z < δ' := mem_ball.mp hw
    have h2 : dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
    rw [mem_ball, hδ'] at *; linarith
  exact (circleIntegral_hasFDerivAt hδ'pos hR (hΦ.mono (Set.prod_mono hsubc le_rfl))
    (hΦ'.mono (Set.prod_mono hsubc le_rfl))
    (fun w hw ζ hζ => hderiv w (hsubb hw) ζ hζ)).differentiableAt.differentiableWithinAt

/-- **Multi-parameter keystone, modulo the bridge (sorry-free).** Given the several-variable
holomorphy⇒analyticity bridge as a hypothesis (`DifferentiableOn ℂ ⇒ AnalyticOnNhd ℂ` on `H`, which
`CBridge.osgood` yields by induction on dimension), the parametric circle integral
`z ↦ ∮ Φ(z,ζ) dζ` is `AnalyticAt` in the multi-dimensional parameter `z ∈ H`. This makes the reduction
"multi-parameter keystone ⟸ (proved differentiability) + bridge" machine-checked: the *only* missing
input is `hbridge`. -/
theorem circleIntegral_analyticAt_multi
    (hbridge : ∀ (f : H → ℂ) (U : Set H), IsOpen U → DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U)
    {Φ : H → ℂ → ℂ} {Φ' : H → ℂ → (H →L[ℂ] ℂ)} {c : ℂ} {R : ℝ} {z₀ : H} {δ : ℝ}
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hΦ : ContinuousOn (fun p : H × ℂ => Φ p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hΦ' : ContinuousOn (fun p : H × ℂ => Φ' p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hderiv : ∀ z ∈ ball z₀ δ, ∀ ζ ∈ sphere c R, HasFDerivAt (fun w => Φ w ζ) (Φ' z ζ) z) :
    AnalyticAt ℂ (fun z => ∮ ζ in C(c, R), Φ z ζ) z₀ :=
  hbridge _ _ isOpen_ball (circleIntegral_differentiableOn_multi hR hΦ hΦ' hderiv)
    z₀ (mem_ball_self hδ)
