import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVBridge
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# `bridge_step` — Phase 2 assembly (WIP)

Assembles `bridge_step : HoloBridge E' → HoloBridge (ℂ × E')` (the inductive step of the `ℂⁿ`
holomorphy⇒analyticity bridge) from the analytic core `combination_analyticAt`. This file builds the
free/tractable pieces; the one remaining hard input is `Bₖ` analytic in `w` (multivariable regularity).
-/

noncomputable section

open Complex Metric
open scoped Real Topology

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- The `z`-coefficient `Bₖ(w) = (2πI)⁻¹ ∮_ζ (ζ−z₀)^{-(k+1)} f(ζ,w)` of the slice power series. -/
noncomputable def stepB (f : ℂ × E' → ℂ) (z₀ : ℂ) (rz : ℝ) (k : ℕ) (w : E') : ℂ :=
  (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (k + 1))⁻¹ • f (ζ, w)

/-- **The `z`-series (`hC`):** `f(z,w) = ∑ₖ (z−z₀)ᵏ • Bₖ(w)`, the 1-variable Cauchy power-series
expansion of the holomorphic `z`-slice `f(·,w)` (reuses `hasSum_w_expansion`). -/
theorem stepB_hasSum {f : ℂ × E' → ℂ} {z₀ : ℂ} {rz : ℝ} (hrz : 0 < rz) (w : E')
    (hcont : ContinuousOn (fun ζ => f (ζ, w)) (closedBall z₀ rz))
    (hdiff : ∀ ζ ∈ ball z₀ rz, DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ)
    {z : ℂ} (hz : ‖z - z₀‖ < rz) :
    HasSum (fun k => (z - z₀) ^ k • stepB f z₀ rz k w) (f (z, w)) := by
  have h := (hasSum_w_expansion (g := fun ζ => f (ζ, w)) (w₀ := z₀) (r := rz) hrz
    hcont hdiff hz).const_smul (2 * π * I : ℂ)⁻¹
  rw [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul] at h
  have hfun : (fun k => (2 * π * I : ℂ)⁻¹ • ((z - z₀) ^ k •
        ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (k + 1))⁻¹ • f (ζ, w)))
      = fun k => (z - z₀) ^ k • stepB f z₀ rz k w := by
    funext k; rw [stepB]; exact smul_comm _ _ _
  rwa [hfun] at h

/-- **Uniform bound on the `w`-Fréchet-partial** (the `E'`-analog of the `slicePartial` estimate). If
`f` is differentiable and bounded by `Mf` on the closed polydisc ball `closedBall p ρ ⊆ ℂ × E'`, then
the `w`-restricted derivative is bounded: `‖(fderiv ℂ f p).comp inr‖ ≤ Mf/ρ`. Proof: along each
complex line `h ↦ f(p + h·(0,v))` the 1-variable Cauchy derivative estimate gives
`‖∂f·(0,v)‖ ≤ (Mf/ρ)‖v‖`. -/
theorem norm_partialFDeriv_le {f : ℂ × E' → ℂ} {p : ℂ × E'} {ρ Mf : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ q ∈ closedBall p ρ, DifferentiableAt ℂ f q)
    (hbound : ∀ q ∈ closedBall p ρ, ‖f q‖ ≤ Mf) :
    ‖(fderiv ℂ f p).comp (ContinuousLinearMap.inr ℂ ℂ E')‖ ≤ Mf / ρ := by
  have hMf : 0 ≤ Mf := (norm_nonneg _).trans (hbound p (mem_closedBall_self hρ.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp only [map_zero, norm_zero, mul_zero, le_refl]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvne : (‖v‖ : ℝ) ≠ 0 := ne_of_gt hvpos
  set R : ℝ := ρ / ‖v‖ with hR_def
  have hRpos : 0 < R := by positivity
  set g : ℂ → ℂ := fun h => f (p + h • (0, v)) with hg_def
  have hLd : ∀ h : ℂ, HasDerivAt (fun h : ℂ => p + h • ((0 : ℂ), v)) ((0 : ℂ), v) h := fun h => by
    simpa using ((hasDerivAt_id h).smul_const ((0 : ℂ), v)).const_add p
  -- membership of the line in the polydisc ball
  have hmem : ∀ h : ℂ, ‖h‖ ≤ R → p + h • ((0 : ℂ), v) ∈ closedBall p ρ := by
    intro h hh
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      show ‖((0 : ℂ), v)‖ = ‖v‖ by simp [Prod.norm_def]]
    calc ‖h‖ * ‖v‖ ≤ R * ‖v‖ := by gcongr
      _ = ρ := by rw [hR_def]; field_simp
  have hnorm_le : ∀ h : ℂ, h ∈ closedBall (0 : ℂ) R → ‖h‖ ≤ R := fun h hh => by
    simpa [dist_eq_norm] using mem_closedBall.mp hh
  -- `g` is holomorphic up to the boundary circle
  have hgdiff : DifferentiableOn ℂ g (closedBall 0 R) := fun h hh =>
    (((hdiff _ (hmem h (hnorm_le h hh))).hasFDerivAt).comp_hasDerivAt h
      (hLd h)).differentiableAt.differentiableWithinAt
  have hgcl : DiffContOnCl ℂ g (ball 0 R) :=
    ⟨hgdiff.mono ball_subset_closedBall, hgdiff.continuousOn.mono closure_ball_subset_closedBall⟩
  have hgbound : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ Mf := fun z hz =>
    hbound _ (hmem z (le_of_eq (by simpa [dist_eq_norm] using mem_sphere.mp hz)))
  -- the directional derivative is `∂f·(0,v)`
  have hderiv : deriv g 0 = (fderiv ℂ f p) (0, v) := by
    have := ((hdiff p (mem_closedBall_self hρ.le)).hasFDerivAt).comp_hasDerivAt_of_eq 0
      (hLd 0) (by simp)
    exact this.deriv
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hgcl hgbound
  rw [hderiv] at hest
  calc ‖(fderiv ℂ f p) (ContinuousLinearMap.inr ℂ ℂ E' v)‖
      = ‖(fderiv ℂ f p) (0, v)‖ := by rw [ContinuousLinearMap.inr_apply]
    _ ≤ Mf / R := hest
    _ = Mf / ρ * ‖v‖ := by rw [hR_def]; field_simp

/-- The `w`-slice `w' ↦ f(ζ,w')` has Fréchet derivative `(fderiv ℂ f (ζ,w)).comp inr` (the full joint
derivative restricted to the `E'` direction). The pointwise-derivative input for the parametric FDeriv. -/
theorem slice_hasFDerivAt {f : ℂ × E' → ℂ} {ζ : ℂ} {w : E'} (hf : DifferentiableAt ℂ f (ζ, w)) :
    HasFDerivAt (fun w' => f (ζ, w'))
      ((fderiv ℂ f (ζ, w)).comp (ContinuousLinearMap.inr ℂ ℂ E')) w := by
  have hL : HasFDerivAt (fun w' : E' => (ζ, w')) (ContinuousLinearMap.inr ℂ ℂ E') w := by
    simpa [ContinuousLinearMap.inr] using (hasFDerivAt_const (ζ : ℂ) w).prodMk (hasFDerivAt_id w)
  exact hf.hasFDerivAt.comp w hL

open MeasureTheory in
/-- **`Bₖ` has a Fréchet derivative in `w`** (differentiate under the circle integral). Adapts
`circleIntegral_hasFDerivAt`, but obtains the derivative bound from `norm_partialFDeriv_le` (rather than
continuity of the `w`-partial — which is the regularity we're proving) and measurability from
`measurable_fderiv`. `FiniteDimensional ℂ E'` (true throughout the `ℂⁿ` induction) supplies the
second-countability for strong measurability. -/
theorem stepB_hasFDerivAt [FiniteDimensional ℂ E'] [MeasurableSpace E'] [BorelSpace E']
    {f : ℂ × E' → ℂ} {z₀ : ℂ} {w₀ : E'}
    {rz Rz Rw Mf : ℝ} (k : ℕ) (hrz : 0 < rz) (hrzRz : rz < Rz) (hRw : 0 < Rw)
    (hdiff : ∀ q ∈ closedBall (z₀ : ℂ) Rz ×ˢ closedBall w₀ Rw, DifferentiableAt ℂ f q)
    (hbound : ∀ q ∈ closedBall (z₀ : ℂ) Rz ×ˢ closedBall w₀ Rw, ‖f q‖ ≤ Mf) :
    HasFDerivAt (fun w => ∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (k + 1))⁻¹ • f (ζ, w))
      (∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (k + 1))⁻¹ •
        ((fderiv ℂ f (ζ, w₀)).comp (ContinuousLinearMap.inr ℂ ℂ E'))) w₀ := by
  set ρ : ℝ := min ((Rz - rz) / 2) (Rw / 2) with hρ_def
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρRw : ρ ≤ Rw := le_trans (min_le_right _ _) (by linarith)
  have hwR : ∀ w ∈ ball w₀ ρ, w ∈ closedBall w₀ Rw := fun w hw =>
    closedBall_subset_closedBall hρRw (ball_subset_closedBall hw)
  have hfc : ContinuousOn f (closedBall (z₀ : ℂ) Rz ×ˢ closedBall w₀ Rw) := fun q hq =>
    (hdiff q hq).continuousAt.continuousWithinAt
  have hdζ : ∀ θ : ℝ, dist (circleMap z₀ rz θ) z₀ = rz :=
    fun θ => mem_sphere.mp (circleMap_mem_sphere z₀ hrz.le θ)
  have hζne : ∀ θ : ℝ, circleMap z₀ rz θ - z₀ ≠ 0 := fun θ h => by
    have := hdζ θ; rw [dist_eq_norm, h, norm_zero] at this; exact (ne_of_lt hrz) this
  -- the inflated closed ball around `(ζθ, w)` stays inside the big polydisc
  have hsub : ∀ (θ : ℝ) (w : E'), dist w w₀ < ρ →
      closedBall (circleMap z₀ rz θ, w) ρ ⊆ closedBall (z₀ : ℂ) Rz ×ˢ closedBall w₀ Rw := by
    rintro θ w hw ⟨a, b⟩ hq
    rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hq
    have hmr : ρ ≤ (Rz - rz) / 2 := min_le_left _ _
    have hmw : ρ ≤ Rw / 2 := min_le_right _ _
    refine Set.mk_mem_prod (mem_closedBall.2 ?_) (mem_closedBall.2 ?_)
    · calc dist a z₀ ≤ dist a (circleMap z₀ rz θ) + dist (circleMap z₀ rz θ) z₀ := dist_triangle _ _ _
        _ ≤ Rz := by rw [hdζ]; linarith [hq.1]
    · calc dist b w₀ ≤ dist b w + dist w w₀ := dist_triangle _ _ _
        _ ≤ Rw := by linarith [hq.2]
  -- continuity of the two scalar factors of the integrand
  have hcm : Continuous (fun θ : ℝ => deriv (circleMap z₀ rz) θ) := by
    rw [show deriv (circleMap z₀ rz) = fun θ => circleMap 0 rz θ * I from funext (deriv_circleMap z₀ rz)]
    exact (continuous_circleMap 0 rz).mul continuous_const
  have hinv : Continuous (fun θ : ℝ => ((circleMap z₀ rz θ - z₀) ^ (k + 1))⁻¹) :=
    (((continuous_circleMap z₀ rz).sub continuous_const).pow _).inv₀ fun θ => pow_ne_zero _ (hζne θ)
  have hnd : ∀ θ : ℝ, ‖deriv (circleMap z₀ rz) θ‖ = rz := fun θ => by
    rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hrz]
  have hni : ∀ θ : ℝ, ‖((circleMap z₀ rz θ - z₀) ^ (k + 1))⁻¹‖ = (rz ^ (k + 1))⁻¹ := fun θ => by
    rw [norm_inv, norm_pow, show ‖circleMap z₀ rz θ - z₀‖ = rz from by rw [← dist_eq_norm]; exact hdζ θ]
  set F : E' → ℝ → ℂ := fun w θ =>
    deriv (circleMap z₀ rz) θ • (((circleMap z₀ rz θ - z₀) ^ (k + 1))⁻¹ • f (circleMap z₀ rz θ, w))
    with hF_def
  set F' : E' → ℝ → (E' →L[ℂ] ℂ) := fun w θ =>
    deriv (circleMap z₀ rz) θ • (((circleMap z₀ rz θ - z₀) ^ (k + 1))⁻¹ •
      ((fderiv ℂ f (circleMap z₀ rz θ, w)).comp (ContinuousLinearMap.inr ℂ ℂ E'))) with hF'_def
  have hmemθ : ∀ (θ : ℝ) (w : E'), w ∈ closedBall w₀ Rw →
      (circleMap z₀ rz θ, w) ∈ closedBall (z₀ : ℂ) Rz ×ˢ closedBall w₀ Rw := fun θ w hw =>
    Set.mk_mem_prod (mem_closedBall.2 (by rw [hdζ]; linarith [hrzRz.le])) hw
  have hFcont : ∀ w ∈ closedBall w₀ Rw, Continuous (F w) := fun w hw =>
    hcm.smul (hinv.smul (hfc.comp_continuous
      ((continuous_circleMap z₀ rz).prodMk continuous_const) fun θ => hmemθ θ w hw))
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := F') (μ := volume) (bound := fun _ => (rz ^ k)⁻¹ * (Mf / ρ)) (s := ball w₀ ρ)
    (ball_mem_nhds w₀ hρpos)
    (Filter.eventually_of_mem (ball_mem_nhds w₀ hRw)
      fun w hw => (hFcont w (ball_subset_closedBall hw)).aestronglyMeasurable)
    ((hFcont w₀ (mem_closedBall_self hRw.le)).intervalIntegrable 0 (2 * π))
    ?_ ?_ intervalIntegrable_const ?_
  · -- `F' w₀` ae-strongly-measurable (via `measurable_fderiv` + finite-dimensionality)
    have h1 : Measurable (fun θ => fderiv ℂ f (circleMap z₀ rz θ, w₀)) :=
      (measurable_fderiv ℂ f).comp
        ((continuous_circleMap z₀ rz).measurable.prodMk measurable_const)
    have hOp : Measurable (fun θ => (fderiv ℂ f (circleMap z₀ rz θ, w₀)).comp
        (ContinuousLinearMap.inr ℂ ℂ E')) :=
      (((ContinuousLinearMap.compL ℂ E' (ℂ × E') ℂ).flip
        (ContinuousLinearMap.inr ℂ ℂ E')).continuous.measurable).comp h1
    exact (hcm.measurable.smul (hinv.measurable.smul hOp)).aestronglyMeasurable
  · -- domination
    refine ae_of_all _ fun θ _ w hw => ?_
    rw [hF'_def, norm_smul, norm_smul, hnd, hni]
    have hOp_le : ‖(fderiv ℂ f (circleMap z₀ rz θ, w)).comp (ContinuousLinearMap.inr ℂ ℂ E')‖
        ≤ Mf / ρ := norm_partialFDeriv_le (f := f) (p := (circleMap z₀ rz θ, w)) (ρ := ρ) hρpos
      (fun q hq => hdiff q (hsub θ w (mem_ball.1 hw) hq))
      (fun q hq => hbound q (hsub θ w (mem_ball.1 hw) hq))
    calc rz * ((rz ^ (k + 1))⁻¹ * ‖_‖)
        ≤ rz * ((rz ^ (k + 1))⁻¹ * (Mf / ρ)) := by gcongr
      _ = (rz ^ k)⁻¹ * (Mf / ρ) := by rw [pow_succ]; field_simp
  · -- pointwise `w`-derivative
    refine ae_of_all _ fun θ _ w hw => ?_
    exact (((slice_hasFDerivAt (hdiff _ (hmemθ θ w (hwR w hw)))).const_smul
      (((circleMap z₀ rz θ - z₀) ^ (k + 1))⁻¹)).const_smul (deriv (circleMap z₀ rz) θ))

end

