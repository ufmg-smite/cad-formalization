import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Normed.Module.Connected
import Cad.Multivariate.ProjectionTheorem.Generalized.CDivisionAlgebra

/-!
# Scalar Cauchy division by a polynomial (Layer B core, one complex variable)

The one-variable heart of the Cauchy-integral proof of Weierstrass division. For a polynomial `P`
non-vanishing on a circle `|ζ| = R`, and `F` holomorphic on the closed disc, the Cauchy reproducing
formula plus the difference-quotient brick give an explicit **division with polynomial remainder**

  `F t = q · P(t) + ∑_{k < deg P} ρ_k · t^k`     (for `|t| < R`),

where the quotient `q` and the remainder coefficients `ρ_k` are the contour integrals

  `q   = (2πi)⁻¹ ∮_{|ζ|=R} F(ζ) / (P(ζ)·(ζ − t)) dζ`,
  `ρ_k = (2πi)⁻¹ ∮_{|ζ|=R} F(ζ)·c_k(ζ) / P(ζ) dζ`,   `c_k(ζ) = ∑_{k < j ≤ deg P} P_j·ζ^{j-1-k}`.

The remainder is a genuine degree `< deg P` polynomial in `t` (that is the content of
`diffQuotient_eq_poly`). This is the per-parameter statement; the parametric Layer-B lemma applies it
at each `z` and upgrades `q, ρ_k` to analytic functions of `z` via the keystone. No argument principle.
-/

noncomputable section

open Complex Polynomial MeasureTheory Metric Finset
open scoped Real Topology

/-- **Scalar Cauchy division by a polynomial.** With `P(ζ) ≠ 0` on the circle `|ζ| = R` and `F`
holomorphic on the closed disc, `F t = q·P(t) + ∑_{k<deg P} ρ_k t^k` for `|t| < R`, with `q` and the
`ρ_k` the explicit Cauchy contour integrals. -/
theorem cauchy_division_scalar (P : Polynomial ℂ) {R : ℝ} (hR : 0 < R)
    {F : ℂ → ℂ} (hFc : ContinuousOn F (closedBall 0 R))
    (hFd : ∀ ζ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ F ζ)
    (hPsphere : ∀ ζ ∈ sphere (0 : ℂ) R, P.eval ζ ≠ 0)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) R) :
    F t = ((2 * π * I : ℂ)⁻¹ * ∮ ζ in C(0, R), F ζ / (P.eval ζ * (ζ - t))) * P.eval t
      + ∑ k ∈ range P.natDegree,
          ((2 * π * I : ℂ)⁻¹ *
            ∮ ζ in C(0, R), F ζ *
              (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ)
          * t ^ k := by
  classical
  -- `t` is strictly inside the disc; the circle avoids `t`
  have htR : ‖t‖ < R := by simpa [mem_ball, dist_eq_norm, sub_zero] using ht
  have hst : ∀ ζ ∈ sphere (0 : ℂ) R, ζ - t ≠ 0 := by
    intro ζ hζ h
    rw [sub_eq_zero] at h
    rw [h, mem_sphere_zero_iff_norm] at hζ
    exact absurd hζ (ne_of_lt htR)
  -- continuity building blocks on the circle
  have hF_s : ContinuousOn F (sphere (0 : ℂ) R) := hFc.mono sphere_subset_closedBall
  have hP_s : ContinuousOn (fun ζ : ℂ => P.eval ζ) (sphere (0 : ℂ) R) := P.continuousOn
  have hsub_s : ContinuousOn (fun ζ : ℂ => ζ - t) (sphere (0 : ℂ) R) :=
    (continuous_id.sub continuous_const).continuousOn
  have hden_s : ContinuousOn (fun ζ : ℂ => P.eval ζ * (ζ - t)) (sphere (0 : ℂ) R) := hP_s.mul hsub_s
  have hden_ne : ∀ ζ ∈ sphere (0 : ℂ) R, P.eval ζ * (ζ - t) ≠ 0 :=
    fun ζ hζ => mul_ne_zero (hPsphere ζ hζ) (hst ζ hζ)
  have hC_s : ∀ k, ContinuousOn
      (fun ζ : ℂ => ∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k))
      (sphere (0 : ℂ) R) := by
    intro k
    exact continuousOn_finset_sum _ fun j _ =>
      (continuous_const.mul (continuous_pow _)).continuousOn
  -- integrability of the pieces
  have hAint : CircleIntegrable
      (fun ζ : ℂ => P.eval t * (F ζ / (P.eval ζ * (ζ - t)))) 0 R :=
    (continuousOn_const.mul (hF_s.div hden_s hden_ne)).circleIntegrable hR.le
  have hBint : CircleIntegrable
      (fun ζ : ℂ => F ζ * (P.eval ζ - P.eval t) / (P.eval ζ * (ζ - t))) 0 R :=
    ((hF_s.mul (hP_s.sub continuousOn_const)).div hden_s hden_ne).circleIntegrable hR.le
  have hKint : ∀ k ∈ range P.natDegree, CircleIntegrable
      (fun ζ : ℂ => F ζ *
        (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ
        * t ^ k) 0 R := by
    intro k _
    exact (((hF_s.mul (hC_s k)).div hP_s hPsphere).mul continuousOn_const).circleIntegrable hR.le
  -- Cauchy reproducing formula
  have hcauchy : F t = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - t)⁻¹ • F ζ :=
    (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty ht hFc (fun ζ hζ => hFd ζ hζ.1)).symm
  -- split the Cauchy integrand pointwise on the circle into the `A` and `B` parts
  have hsplit : Set.EqOn (fun ζ : ℂ => (ζ - t)⁻¹ • F ζ)
      (fun ζ : ℂ => P.eval t * (F ζ / (P.eval ζ * (ζ - t)))
        + F ζ * (P.eval ζ - P.eval t) / (P.eval ζ * (ζ - t))) (sphere (0 : ℂ) R) := by
    intro ζ hζ
    have hPζ := hPsphere ζ hζ
    have hζt := hst ζ hζ
    show (ζ - t)⁻¹ • F ζ = P.eval t * (F ζ / (P.eval ζ * (ζ - t)))
        + F ζ * (P.eval ζ - P.eval t) / (P.eval ζ * (ζ - t))
    rw [smul_eq_mul]
    field_simp
    ring
  -- the `B` part equals the explicit degree-`<n` polynomial in `t`, pointwise on the circle
  have hBpoly : Set.EqOn
      (fun ζ : ℂ => F ζ * (P.eval ζ - P.eval t) / (P.eval ζ * (ζ - t)))
      (fun ζ : ℂ => ∑ k ∈ range P.natDegree,
        F ζ * (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ
          * t ^ k) (sphere (0 : ℂ) R) := by
    intro ζ hζ
    have hPζ := hPsphere ζ hζ
    have hζt := hst ζ hζ
    show F ζ * (P.eval ζ - P.eval t) / (P.eval ζ * (ζ - t))
        = ∑ k ∈ range P.natDegree,
          F ζ * (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ
            * t ^ k
    rw [eval_sub_eval_eq_mul P ζ t, diffQuotient_eq_poly P ζ t, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  -- pull `t^k` out of each remainder integral
  have hpull : ∀ k ∈ range P.natDegree,
      (∮ ζ in C(0, R), F ζ *
          (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ
          * t ^ k)
        = (∮ ζ in C(0, R), F ζ *
            (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ)
          * t ^ k := by
    intro k _
    rw [show (fun ζ : ℂ => F ζ *
          (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ
          * t ^ k)
        = (fun ζ : ℂ => t ^ k * (F ζ *
            (∑ j ∈ Finset.Ico (k + 1) (P.natDegree + 1), P.coeff j * ζ ^ (j - 1 - k)) / P.eval ζ))
        from funext fun ζ => by ring,
      circleIntegral.integral_const_mul, mul_comm]
  -- assemble the integral identity
  rw [hcauchy, circleIntegral.integral_congr hR.le hsplit,
    circleIntegral.integral_add hAint hBint, circleIntegral.integral_const_mul,
    circleIntegral.integral_congr hR.le hBpoly, circleIntegral.integral_fun_sum hKint,
    Finset.sum_congr rfl hpull, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun k _ => by ring

open Filter in
/-- **Residue at infinity vanishes (the uniqueness input).** If `g` is holomorphic on the closed
exterior `{|z| ≥ R}` and decays like `‖g z‖ ≤ C/‖z‖²` there, then `∮_{|z|=R} g = 0`. Proof: the
annulus Cauchy–Goursat theorem gives `∮_{|z|=R} g = ∮_{|z|=R'} g` for every `R' ≥ R`, and the right
side is `O(1/R') → 0`. This is exactly the fact that makes the Cauchy quotient formula *recover* the
quotient (hence Weierstrass-division uniqueness): the proper rational `r(ζ)/(W(ζ)(ζ−t))` (all poles
inside the contour, by the Lagrange root bound) integrates to `0`. -/
theorem circleIntegral_eq_zero_of_decay {g : ℂ → ℂ} {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R ≤ R₀) (C : ℝ)
    (hg : ∀ z, R ≤ ‖z‖ → DifferentiableAt ℂ g z)
    (hbound : ∀ z, R₀ ≤ ‖z‖ → ‖g z‖ ≤ C / ‖z‖ ^ 2) :
    (∮ z in C(0, R), g z) = 0 := by
  -- annulus deformation: `∮_{R'} g = ∮_R g` for every `R' ≥ R`
  have heq : ∀ R' : ℝ, R ≤ R' → (∮ z in C(0, R'), g z) = ∮ z in C(0, R), g z := by
    intro R' hR'
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hR hR'
      Set.countable_empty (fun z hz => ?_) (fun z hz => ?_)
    · have : R ≤ ‖z‖ := by
        have := hz.2; rw [mem_ball_zero_iff, not_lt] at this; exact this
      exact (hg z this).continuousAt.continuousWithinAt
    · have : R ≤ ‖z‖ := by
        have := hz.1.2; rw [mem_closedBall_zero_iff, not_le] at this; exact this.le
      exact hg z this
  -- norm bound `‖∮_{R'} g‖ ≤ 2πC/R'` for `R' ≥ R₀` (decay regime)
  have hnb : ∀ R' : ℝ, R₀ ≤ R' → ‖∮ z in C(0, R'), g z‖ ≤ 2 * π * C / R' := by
    intro R' hR'
    have hR'0 : (0 : ℝ) ≤ R' := le_trans (le_trans hR.le hRR₀) hR'
    have h := circleIntegral.norm_integral_le_of_norm_le_const (c := 0) (f := g) (C := C / R' ^ 2)
      hR'0 (fun z hz => by
        rw [mem_sphere_zero_iff_norm] at hz
        have h2 := hbound z (by rw [hz]; exact hR')
        rwa [hz] at h2)
    calc ‖∮ z in C(0, R'), g z‖ ≤ 2 * π * R' * (C / R' ^ 2) := h
      _ = 2 * π * C / R' := by field_simp
  -- `‖∮_R g‖ ≤ 0`, hence `= 0`
  have hle0 : ‖∮ z in C(0, R), g z‖ ≤ 0 := by
    have htend : Tendsto (fun R' : ℝ => 2 * π * C / R') atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 * π * C)
    refine ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop R₀] with R' hR'
    rw [← heq R' (le_trans hRR₀ hR')]; exact hnb R' hR'
  exact norm_le_zero_iff.mp hle0

/-- **Scalar quotient recovery (uniqueness core).** If `Q·P + r = 0` on the circle `|ζ| = R`
(`P ≠ 0` there) and the proper-rational remainder integral vanishes (the residue-at-infinity input),
then the Cauchy quotient formula recovers `Q(t) = 0` for `|t| < R`. This packages the recovery
computation: `Q(t) = (2πi)⁻¹∮ Q(ζ)/(ζ−t) = (2πi)⁻¹∮ -r(ζ)/(P(ζ)(ζ−t)) = 0`. Per-parameter; the
parametric uniqueness applies it at each `z` (with `Q·P + r = 0` on the contour from the identity
theorem, and the residue integral `= 0` from `circleIntegral_eq_zero_of_decay`). -/
theorem cauchy_recovery_zero (P : Polynomial ℂ) {R : ℝ} (hR : 0 < R)
    {Q : ℂ → ℂ} (hQc : ContinuousOn Q (closedBall 0 R))
    (hQd : ∀ ζ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ Q ζ)
    (hP_sphere : ∀ ζ ∈ sphere (0 : ℂ) R, P.eval ζ ≠ 0)
    {r : Polynomial ℂ} {t : ℂ} (ht : t ∈ ball (0 : ℂ) R)
    (hHzero : ∀ ζ ∈ sphere (0 : ℂ) R, Q ζ * P.eval ζ + r.eval ζ = 0)
    (hres : (∮ ζ in C(0, R), r.eval ζ / (P.eval ζ * (ζ - t))) = 0) :
    Q t = 0 := by
  have htR : ‖t‖ < R := by simpa [mem_ball, dist_eq_norm, sub_zero] using ht
  have hst : ∀ ζ ∈ sphere (0 : ℂ) R, ζ - t ≠ 0 := by
    intro ζ hζ h
    rw [sub_eq_zero] at h
    rw [h, mem_sphere_zero_iff_norm] at hζ
    exact absurd hζ (ne_of_lt htR)
  have hcauchy : Q t = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - t)⁻¹ • Q ζ :=
    (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty ht hQc (fun ζ hζ => hQd ζ hζ.1)).symm
  have hcongr : Set.EqOn (fun ζ => (ζ - t)⁻¹ • Q ζ)
      (fun ζ => (-1 : ℂ) * (r.eval ζ / (P.eval ζ * (ζ - t)))) (sphere (0 : ℂ) R) := by
    intro ζ hζ
    have hPζ := hP_sphere ζ hζ
    have hζt := hst ζ hζ
    have hQP : Q ζ * P.eval ζ = -r.eval ζ := eq_neg_of_add_eq_zero_left (hHzero ζ hζ)
    simp only [smul_eq_mul]
    field_simp
    linear_combination hQP
  rw [hcauchy, circleIntegral.integral_congr hR.le hcongr, circleIntegral.integral_const_mul,
    hres, mul_zero, smul_zero]

open Filter in
/-- **Scalar Weierstrass-division uniqueness (per parameter).** If `Q` is holomorphic on an open disc
`ball 0 R'` with `R' > R`, `P ≠ 0` on the circle `|ζ| = R`, the germ `Q·P + r` vanishes near `0`, and
the remainder integral vanishes (residue-at-infinity input), then `Q(t) = 0` for `|t| < R`. The
identity theorem propagates `Q·P + r = 0` from a neighborhood of `0` to the whole disc (hence to the
contour), feeding `cauchy_recovery_zero`. -/
theorem cauchy_uniqueness_scalar (P : Polynomial ℂ) {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    {Q : ℂ → ℂ} (hQ_an : AnalyticOnNhd ℂ Q (ball 0 R'))
    (hP_sphere : ∀ ζ ∈ sphere (0 : ℂ) R, P.eval ζ ≠ 0)
    {r : Polynomial ℂ} (hHeq : (fun t => Q t * P.eval t + r.eval t) =ᶠ[𝓝 (0 : ℂ)] 0)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) R)
    (hres : (∮ ζ in C(0, R), r.eval ζ / (P.eval ζ * (ζ - t))) = 0) :
    Q t = 0 := by
  have hR'pos : 0 < R' := lt_trans hR hRR'
  have hpoly : ∀ (p : Polynomial ℂ) (ζ : ℂ), AnalyticAt ℂ (fun x => p.eval x) ζ :=
    fun p ζ => AnalyticOnNhd.eval_polynomial p ζ (Set.mem_univ ζ)
  -- `H := Q·P + r` is analytic on the disc
  have hH_an : AnalyticOnNhd ℂ (fun t => Q t * P.eval t + r.eval t) (ball 0 R') :=
    fun ζ hζ => ((hQ_an ζ hζ).mul (hpoly P ζ)).add (hpoly r ζ)
  -- identity theorem: `H = 0` on the whole disc
  have hH0 : Set.EqOn (fun t => Q t * P.eval t + r.eval t) 0 (ball 0 R') :=
    hH_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball
      (mem_ball_self hR'pos) hHeq
  -- in particular on the contour `|ζ| = R`
  have hHzero : ∀ ζ ∈ sphere (0 : ℂ) R, Q ζ * P.eval ζ + r.eval ζ = 0 := by
    intro ζ hζ
    have hmem : ζ ∈ ball (0 : ℂ) R' := by
      rw [mem_ball_zero_iff]; rw [mem_sphere_zero_iff_norm] at hζ; rw [hζ]; exact hRR'
    simpa using hH0 hmem
  -- `Q` continuous/differentiable on the closed disc `|ζ| ≤ R ⊂ ball 0 R'`
  have hsub : ∀ ζ : ℂ, ‖ζ‖ ≤ R → ζ ∈ ball (0 : ℂ) R' := fun ζ hζ =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt hζ hRR')
  have hQc : ContinuousOn Q (closedBall 0 R) := fun ζ hζ =>
    (hQ_an ζ (hsub ζ (mem_closedBall_zero_iff.mp hζ))).continuousAt.continuousWithinAt
  have hQd : ∀ ζ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ Q ζ := fun ζ hζ =>
    (hQ_an ζ (hsub ζ (le_of_lt (mem_ball_zero_iff.mp hζ)))).differentiableAt
  exact cauchy_recovery_zero P hR hQc hQd hP_sphere ht hHzero hres

/-- **Polynomial growth (upper bound).** `‖p.eval ζ‖ ≤ A·‖ζ‖^{deg p}` for `‖ζ‖ ≥ 1`, with
`A = ∑ⱼ ‖p_j‖`. Building block for the `O(1/ζ²)` decay of the proper rational `r/(W(ζ−t))`. -/
theorem norm_eval_le (p : Polynomial ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → ‖p.eval ζ‖ ≤ A * ‖ζ‖ ^ p.natDegree := by
  refine ⟨∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun ζ hζ => ?_⟩
  rw [eval_eq_sum_range]
  calc ‖∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * ζ ^ j‖
      ≤ ∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j * ζ ^ j‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖ * ‖ζ‖ ^ j := by
        simp only [norm_mul, norm_pow]
    _ ≤ ∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖ * ‖ζ‖ ^ p.natDegree :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hζ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) (norm_nonneg _)
    _ = (∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖) * ‖ζ‖ ^ p.natDegree := by
        rw [Finset.sum_mul]

/-- **Decay of the proper rational `r/(W(ζ−t))`.** With `W` monic of degree `m ≥ 1` and `deg r < m`,
for all large `ζ` we have `‖r(ζ)/(W(ζ)(ζ−t))‖ ≤ C/‖ζ‖²`. The proof: `‖r‖ ≤ A_r‖ζ‖^{m-1}` (upper),
`‖W‖ ≥ ‖ζ‖^m/2` (monic, leading-term dominance), `‖ζ−t‖ ≥ ‖ζ‖/2` — combining to `4A_r/‖ζ‖²`. This is
the input that discharges the residue-at-infinity hypothesis for Weierstrass-division uniqueness. -/
theorem rational_decay (W r : Polynomial ℂ) (hm : 0 < W.natDegree) (hWmonic : W.Monic)
    (hrdeg : r.natDegree < W.natDegree) (t : ℂ) :
    ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ ∀ ζ : ℂ, R₀ ≤ ‖ζ‖ →
      ‖r.eval ζ / (W.eval ζ * (ζ - t))‖ ≤ C / ‖ζ‖ ^ 2 := by
  set m := W.natDegree with hm_def
  obtain ⟨Ar, hAr0, hAr⟩ := norm_eval_le r
  obtain ⟨Aw, hAw0, hAw⟩ := norm_eval_le (W - X ^ m)
  -- degree of `W - X^m` is `< m`
  have hWXdeg : (W - X ^ m).natDegree ≤ m - 1 := by
    have hdW : W.degree = (m : WithBot ℕ) := degree_eq_natDegree hWmonic.ne_zero
    have hdX : (X ^ m : Polynomial ℂ).degree = (m : WithBot ℕ) := degree_X_pow m
    have hlt : (W - X ^ m).degree < (m : WithBot ℕ) := by
      have := degree_sub_lt (hdW.trans hdX.symm) hWmonic.ne_zero
        (hWmonic.leadingCoeff.trans (monic_X_pow m).leadingCoeff.symm)
      rwa [hdW] at this
    rcases eq_or_ne (W - X ^ m) 0 with h0 | h0
    · rw [h0, natDegree_zero]; omega
    · exact Nat.le_sub_one_of_lt ((natDegree_lt_iff_degree_lt h0).mpr hlt)
  refine ⟨max 1 (max (2 * Aw) (2 * ‖t‖)), 4 * Ar, le_max_left _ _, fun ζ hζ => ?_⟩
  have hx1 : 1 ≤ ‖ζ‖ := le_trans (le_max_left _ _) hζ
  have hxpos : 0 < ‖ζ‖ := lt_of_lt_of_le one_pos hx1
  have hAw2 : 2 * Aw ≤ ‖ζ‖ := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hζ
  have ht2 : 2 * ‖t‖ ≤ ‖ζ‖ := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hζ
  have hpm : ‖ζ‖ ^ m = ‖ζ‖ * ‖ζ‖ ^ (m - 1) := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hm]
  -- `r` upper bound
  have hr : ‖r.eval ζ‖ ≤ Ar * ‖ζ‖ ^ (m - 1) :=
    le_trans (hAr ζ hx1) (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hx1 (Nat.le_sub_one_of_lt hrdeg)) hAr0)
  -- `W - X^m` upper bound
  have hWX : ‖(W - X ^ m).eval ζ‖ ≤ Aw * ‖ζ‖ ^ (m - 1) :=
    le_trans (hAw ζ hx1) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hWXdeg) hAw0)
  -- `W` lower bound `‖ζ‖^m/2 ≤ ‖W(ζ)‖`
  have hWeval : W.eval ζ = ζ ^ m + (W - X ^ m).eval ζ := by
    rw [eval_sub, eval_pow, eval_X]; ring
  have hWlow : ‖ζ‖ ^ m / 2 ≤ ‖W.eval ζ‖ := by
    have hrev : ‖ζ‖ ^ m - ‖(W - X ^ m).eval ζ‖ ≤ ‖W.eval ζ‖ := by
      rw [hWeval]
      calc ‖ζ‖ ^ m - ‖(W - X ^ m).eval ζ‖
          = ‖ζ ^ m‖ - ‖(W - X ^ m).eval ζ‖ := by rw [norm_pow]
        _ ≤ ‖ζ ^ m + (W - X ^ m).eval ζ‖ := by
            have h := norm_add_le (ζ ^ m + (W - X ^ m).eval ζ) (-(W - X ^ m).eval ζ)
            rw [add_neg_cancel_right, norm_neg] at h
            linarith
    have hAwbound : Aw * ‖ζ‖ ^ (m - 1) ≤ ‖ζ‖ ^ m / 2 := by
      rw [hpm]
      have hPnn : (0 : ℝ) ≤ ‖ζ‖ ^ (m - 1) := by positivity
      nlinarith [hAw2, hPnn, mul_nonneg (by linarith [hAw2] : (0 : ℝ) ≤ ‖ζ‖ - 2 * Aw) hPnn]
    linarith [hWX]
  -- `ζ - t` lower bound
  have htlow : ‖ζ‖ / 2 ≤ ‖ζ - t‖ := by
    have := norm_sub_norm_le ζ t
    linarith [this, ht2]
  -- assemble
  have hWpos : 0 < ‖W.eval ζ‖ := lt_of_lt_of_le (by positivity) hWlow
  have htpos : 0 < ‖ζ - t‖ := lt_of_lt_of_le (by positivity) htlow
  rw [norm_div, norm_mul, div_le_div_iff₀ (mul_pos hWpos htpos) (by positivity)]
  calc ‖r.eval ζ‖ * ‖ζ‖ ^ 2
      ≤ (Ar * ‖ζ‖ ^ (m - 1)) * ‖ζ‖ ^ 2 := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = Ar * ‖ζ‖ ^ (m + 1) := by
          rw [mul_assoc, ← pow_add, show m - 1 + 2 = m + 1 from by omega]
    _ = 4 * Ar * (‖ζ‖ ^ m / 2 * (‖ζ‖ / 2)) := by
          rw [show ‖ζ‖ ^ (m + 1) = ‖ζ‖ ^ m * ‖ζ‖ from by rw [pow_succ]]; ring
    _ ≤ 4 * Ar * (‖W.eval ζ‖ * ‖ζ - t‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hWlow htlow (by positivity) (norm_nonneg _))
            (mul_nonneg (by norm_num) hAr0)
