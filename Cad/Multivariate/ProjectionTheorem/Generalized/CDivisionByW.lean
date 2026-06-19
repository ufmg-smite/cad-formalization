import Cad.Multivariate.ProjectionTheorem.Generalized.CCauchyDivision
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs
import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassAssembly

/-!
# Layer B parametric packaging: division by a Weierstrass polynomial (WIP)

Bridges the scalar Cauchy division identity `cauchy_division_scalar` (one complex variable) to the
parametric `division by W` statement consumed by Layer A. The first, self-contained pieces:

* `weierstrassPoly_monic`, `weierstrassPoly_natDegree`: a Weierstrass polynomial
  `W = X^m + ∑_{i<m} a_i·X^i` is monic of degree exactly `m`. This is what aligns the scalar lemma's
  `∑_{k < deg P}` remainder with the target's `∑ i : Fin m`.
-/

noncomputable section

open Polynomial Filter Complex
open scoped Topology

variable {s e : ℕ}

/-- The evaluation `(z, ζ) ↦ W(z, ζ)` of a Weierstrass polynomial is jointly analytic at any point
`p` whose `z`-component is one where the coefficients are analytic (coefficients analytic ⟹ the
polynomial value is analytic; the `ζ`-dependence is polynomial, hence entire). -/
theorem weierstrassEval_analyticAt (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (p : CParam s e × ℂ) (ha_an : ∀ i, AnalyticAt ℂ (a i) p.1) :
    AnalyticAt ℂ (fun zζ : CParam s e × ℂ => (weierstrassPoly m a zζ.1).eval zζ.2) p := by
  have heq : (fun zζ : CParam s e × ℂ => (weierstrassPoly m a zζ.1).eval zζ.2)
      = fun zζ => zζ.2 ^ m + ∑ i : Fin m, a i zζ.1 * zζ.2 ^ (i : ℕ) := by
    funext zζ
    simp only [weierstrassPoly, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]
  rw [heq]
  have hsnd : AnalyticAt ℂ (fun zζ : CParam s e × ℂ => zζ.2) p := analyticAt_snd
  have hfst : AnalyticAt ℂ (fun zζ : CParam s e × ℂ => zζ.1) p := analyticAt_fst
  refine (hsnd.pow m).add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
  exact ((ha_an i).comp_of_eq hfst rfl).mul (hsnd.pow (i : ℕ))

/-- On the section `z = 0`, a Weierstrass polynomial (`a_i(0) = 0`) evaluates to `ζ^m`. -/
theorem weierstrassEval_zero (m : ℕ) (a : Fin m → (CParam s e → ℂ)) (ha0 : ∀ i, a i 0 = 0)
    (ζ : ℂ) : (weierstrassPoly m a (0 : CParam s e)).eval ζ = ζ ^ m := by
  simp only [weierstrassPoly, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C, ha0,
    zero_mul, Finset.sum_const_zero, add_zero]

/-- **Joint analyticity of the Cauchy quotient integrand** at a contour point `((0,0), ζ₀)`
(`ζ₀ ≠ 0`). The integrand `(z,t,ζ) ↦ F(z,ζ) / (W(z,ζ)·(ζ − t))` is analytic there: `F` is analytic at
`(0, ζ₀)`, `W(0, ζ₀) = ζ₀^m ≠ 0`, and `ζ₀ − 0 = ζ₀ ≠ 0`. This is the keystone input for `Q`. -/
theorem qIntegrand_analyticAt (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (F : CParam s e × ℂ → ℂ) (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0) (hF : AnalyticAt ℂ F (0, ζ₀)) :
    AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ =>
        F (x.1.1, x.2) / ((weierstrassPoly m a x.1.1).eval x.2 * (x.2 - x.1.2)))
      ((0, 0), ζ₀) := by
  -- analytic projections of the ambient variable `x = ((z,t), ζ)`
  have hx11 : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ => x.1.1) ((0, 0), ζ₀) :=
    analyticAt_fst.comp analyticAt_fst
  have hx12 : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ => x.1.2) ((0, 0), ζ₀) :=
    analyticAt_snd.comp analyticAt_fst
  have hx2 : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ => x.2) ((0, 0), ζ₀) := analyticAt_snd
  -- `F (x.1.1, x.2)`
  have hg : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ => (x.1.1, x.2)) ((0, 0), ζ₀) := hx11.prod hx2
  have hFc : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ => F (x.1.1, x.2)) ((0, 0), ζ₀) :=
    hF.comp_of_eq hg rfl
  -- `W (x.1.1, x.2)`
  have hW : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ =>
      (weierstrassPoly m a x.1.1).eval x.2) ((0, 0), ζ₀) :=
    (weierstrassEval_analyticAt m a (0, ζ₀) ha_an).comp_of_eq hg rfl
  -- `ζ - t`
  have hsub : AnalyticAt ℂ (fun x : (CParam s e × ℂ) × ℂ => x.2 - x.1.2) ((0, 0), ζ₀) :=
    hx2.sub hx12
  -- denominator nonzero at the point: `ζ₀^m · ζ₀ ≠ 0`
  have hden_ne : (weierstrassPoly m a ((((0 : CParam s e), (0 : ℂ)), ζ₀).1.1)).eval
      (((0 : CParam s e), (0 : ℂ)), ζ₀).2 *
      ((((0 : CParam s e), (0 : ℂ)), ζ₀).2 - (((0 : CParam s e), (0 : ℂ)), ζ₀).1.2) ≠ 0 := by
    simp only
    rw [weierstrassEval_zero m a ha0, sub_zero]
    exact mul_ne_zero (pow_ne_zero m hζ₀) hζ₀
  exact hFc.div (hW.mul hsub) hden_ne


/-- Each coefficient `z ↦ W(z, ·).coeff j` of a Weierstrass polynomial is **analytic** in `z`
(`coeff j` is `1`/`0` for `j = m`/`j > m` and `a_j(z)` for `j < m` — in all cases a constant plus a
linear combination of the analytic coefficients). -/
theorem weierstrassPoly_coeff_analyticAt (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (z₀ : CParam s e) (ha_an : ∀ i, AnalyticAt ℂ (a i) z₀) (j : ℕ) :
    AnalyticAt ℂ (fun z => (weierstrassPoly m a z).coeff j) z₀ := by
  have heq : (fun z : CParam s e => (weierstrassPoly m a z).coeff j)
      = fun z => (X ^ m : Polynomial ℂ).coeff j
          + ∑ i : Fin m, a i z * (X ^ (i : ℕ) : Polynomial ℂ).coeff j := by
    funext z
    rw [weierstrassPoly, coeff_add]
    congr 1
    rw [finset_sum_coeff]
    exact Finset.sum_congr rfl fun i _ => by rw [coeff_C_mul]
  rw [heq]
  refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
  exact (ha_an i).mul analyticAt_const

/-- **Joint analyticity of the Cauchy remainder integrand** at a contour point `(0, ζ₀)` (`ζ₀ ≠ 0`).
The integrand `(z, ζ) ↦ F(z,ζ)·c_k(z,ζ) / W(z,ζ)`, with `c_k(z,ζ) = ∑_{k<j≤m} W(z,·).coeff j·ζ^{j-1-k}`,
is analytic there. This is the keystone input for the remainder coefficients `ρ_k`. -/
theorem rhoIntegrand_analyticAt (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (F : CParam s e × ℂ → ℂ) (k : ℕ) (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0) (hF : AnalyticAt ℂ F (0, ζ₀)) :
    AnalyticAt ℂ (fun x : CParam s e × ℂ =>
        F x *
          (∑ j ∈ Finset.Ico (k + 1) (m + 1), (weierstrassPoly m a x.1).coeff j * x.2 ^ (j - 1 - k))
          / (weierstrassPoly m a x.1).eval x.2) (0, ζ₀) := by
  have hx2 : AnalyticAt ℂ (fun x : CParam s e × ℂ => x.2) (0, ζ₀) := analyticAt_snd
  have hx1 : AnalyticAt ℂ (fun x : CParam s e × ℂ => x.1) (0, ζ₀) := analyticAt_fst
  -- the remainder coefficient `c_k` is analytic
  have hc : AnalyticAt ℂ (fun x : CParam s e × ℂ =>
      ∑ j ∈ Finset.Ico (k + 1) (m + 1), (weierstrassPoly m a x.1).coeff j * x.2 ^ (j - 1 - k))
      (0, ζ₀) := by
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((weierstrassPoly_coeff_analyticAt m a 0 ha_an j).comp_of_eq hx1 rfl).mul (hx2.pow _)
  -- the divisor `W` is analytic and nonzero at the point
  have hW : AnalyticAt ℂ (fun x : CParam s e × ℂ => (weierstrassPoly m a x.1).eval x.2) (0, ζ₀) :=
    weierstrassEval_analyticAt m a (0, ζ₀) ha_an
  have hWne : (weierstrassPoly m a (0 : CParam s e)).eval ζ₀ ≠ 0 := by
    rw [weierstrassEval_zero m a ha0]; exact pow_ne_zero m hζ₀
  exact (hF.mul hc).div hW hWne

open Metric Set Topology in
/-- **Contour extraction.** For a Weierstrass polynomial (`a_i(0) = 0`) and any radius `R > 0`, the
divisor `W(z, ·)` is nonvanishing on the circle `|ζ| = R` for all `z` near `0`. On the section
`W(0, ζ) = ζ^m ≠ 0`; jointly `W` is analytic (hence continuous) near `{0} × sphere`, so a tube-lemma
argument propagates non-vanishing to a neighborhood of `0`. (We run the tube on the open
"analytic-and-nonzero" set, since the coefficients are only analytic at `0`, not globally continuous.) -/
theorem weierstrass_contour (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ ζ ∈ sphere (0 : ℂ) R, (weierstrassPoly m a z).eval ζ ≠ 0 := by
  have hWan : ∀ ζ : ℂ,
      AnalyticAt ℂ (fun zζ : CParam s e × ℂ => (weierstrassPoly m a zζ.1).eval zζ.2) (0, ζ) :=
    fun ζ => weierstrassEval_analyticAt m a (0, ζ) ha_an
  set S : Set (CParam s e × ℂ) :=
    {p | AnalyticAt ℂ (fun zζ : CParam s e × ℂ => (weierstrassPoly m a zζ.1).eval zζ.2) p ∧
      (weierstrassPoly m a p.1).eval p.2 ≠ 0} with hS
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨hpA, hpne⟩
    exact hpA.eventually_analyticAt.and (hpA.continuousAt.eventually_ne hpne)
  have hsub : ({(0 : CParam s e)} : Set (CParam s e)) ×ˢ sphere (0 : ℂ) R ⊆ S := by
    rintro ⟨z, ζ⟩ ⟨hz, hζ⟩
    rw [mem_singleton_iff] at hz; subst hz
    have hζ0 : ζ ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hζ
      intro h; rw [h, norm_zero] at hζ; exact absurd hζ (ne_of_lt hR)
    exact ⟨hWan ζ, by rw [weierstrassEval_zero m a ha0]; exact pow_ne_zero m hζ0⟩
  obtain ⟨u, v, hu, _, hz₀u, hsphv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere (0 : ℂ) R) hS_open hsub
  filter_upwards [hu.mem_nhds (hz₀u rfl)] with z hz ζ hζ
  exact (huv (Set.mk_mem_prod hz (hsphv hζ))).2

/-- A slice `w ↦ F(z, w)` of a jointly-analytic function is analytic in `w`. -/
theorem analyticAt_slice (F : CParam s e × ℂ → ℂ) {z : CParam s e} {ζ : ℂ}
    (hF : AnalyticAt ℂ F (z, ζ)) : AnalyticAt ℂ (fun w => F (z, w)) ζ := by
  have hmap : AnalyticAt ℂ (fun w : ℂ => (z, w)) ζ := analyticAt_const.prod analyticAt_id
  exact hF.comp_of_eq hmap rfl

/-- **Slice-domain extraction.** From `F` analytic at `0`, the slices `F(z, ·)` are analytic on a
common polydisc `‖z‖, ‖ζ‖ < ρ` (so on a closed `ζ`-disc of any radius `R < ρ` for every `‖z‖ < ρ`,
giving the continuity/differentiability hypotheses the scalar Cauchy lemma needs). -/
theorem exists_slice_analytic (F : CParam s e × ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ ρ > 0, ∀ z : CParam s e, ‖z‖ < ρ → ∀ ζ : ℂ, ‖ζ‖ < ρ →
      AnalyticAt ℂ (fun w => F (z, w)) ζ := by
  obtain ⟨ρ, hρ, hFan⟩ := hF.exists_ball_analyticOnNhd
  refine ⟨ρ, hρ, fun z hz ζ hζ => analyticAt_slice F (hFan (z, ζ) ?_)⟩
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
  exact max_lt hz hζ

open Complex MeasureTheory Metric Finset in
open scoped Real Topology in
/-- **Capstone (existence): parametric Weierstrass division by `W`.** Given the keystone
(contour integrals of jointly-analytic integrands are analytic — modulo `osgood`) as a hypothesis,
every analytic `F` divides as `F = Q·W + ∑_{i<m} ρ_i t^i` near `0`, with `Q`, `ρ_i` analytic. This is
exactly Layer A's `hdivW_exist`. Assembled from `cauchy_division_scalar` (per-`z`),
`weierstrass_contour` + `exists_slice_analytic` (domain), `qIntegrand_analyticAt` /
`rhoIntegrand_analyticAt` (keystone inputs), and `weierstrassPoly_natDegree` (`range m`↔`Fin m`). -/
theorem weierstrass_division_W_exists
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (keystone : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
      (Φ : H × ℂ → ℂ) {r : ℝ} {p₀ : H}, 0 < r →
      (∀ ζ ∈ sphere (0 : ℂ) r, AnalyticAt ℂ Φ (p₀, ζ)) →
      AnalyticAt ℂ (fun p : H => ∮ ζ in C(0, r), Φ (p, ζ)) p₀)
    (F : CParam s e × ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ (Q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ Q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
      F =ᶠ[𝓝 0] fun wt => Q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ) := by
  obtain ⟨ρ, hρ, hFan⟩ := hF.exists_ball_analyticOnNhd
  set R := ρ / 2 with hRdef
  have hRpos : 0 < R := half_pos hρ
  have hR_lt : R < ρ := by rw [hRdef]; linarith
  have hF0 : ∀ ζ : ℂ, ‖ζ‖ < ρ → AnalyticAt ℂ F (0, ζ) := fun ζ hζ => hFan (0, ζ) (by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg ζ)]
    exact hζ)
  have hsphere : ∀ ζ ∈ sphere (0 : ℂ) R, ζ ≠ 0 ∧ ‖ζ‖ < ρ := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    refine ⟨fun h => ?_, by rw [hζ]; exact hR_lt⟩
    rw [h, norm_zero] at hζ; exact absurd hζ.symm (ne_of_gt hRpos)
  refine ⟨fun wt => (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
        F (wt.1, ζ) / ((weierstrassPoly m a wt.1).eval ζ * (ζ - wt.2)),
      fun i z => (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
        F (z, ζ) *
          (∑ j ∈ Finset.Ico ((i : ℕ) + 1) (m + 1), (weierstrassPoly m a z).coeff j *
            ζ ^ (j - 1 - (i : ℕ))) / (weierstrassPoly m a z).eval ζ,
      ?_, ?_, ?_⟩
  · -- `Q` analytic
    refine analyticAt_const.mul (keystone
      (fun x : (CParam s e × ℂ) × ℂ =>
        F (x.1.1, x.2) / ((weierstrassPoly m a x.1.1).eval x.2 * (x.2 - x.1.2))) hRpos ?_)
    intro ζ hζ
    exact qIntegrand_analyticAt m a ha_an ha0 F ζ (hsphere ζ hζ).1 (hF0 ζ (hsphere ζ hζ).2)
  · -- `ρ_i` analytic
    intro i
    refine analyticAt_const.mul (keystone
      (fun x : CParam s e × ℂ =>
        F x * (∑ j ∈ Finset.Ico ((i : ℕ) + 1) (m + 1), (weierstrassPoly m a x.1).coeff j *
          x.2 ^ (j - 1 - (i : ℕ))) / (weierstrassPoly m a x.1).eval x.2) hRpos ?_)
    intro ζ hζ
    exact rhoIntegrand_analyticAt m a ha_an ha0 F (i : ℕ) ζ (hsphere ζ hζ).1 (hF0 ζ (hsphere ζ hζ).2)
  · -- the `=ᶠ[𝓝 0]` division identity
    have ec := (continuous_fst.tendsto' (0 : CParam s e × ℂ) 0 rfl).eventually
      (weierstrass_contour m a ha_an ha0 hRpos)
    have ez := (continuous_fst.tendsto' (0 : CParam s e × ℂ) 0 rfl).eventually
      (Metric.ball_mem_nhds (0 : CParam s e) hρ)
    have et := (continuous_snd.tendsto' (0 : CParam s e × ℂ) 0 rfl).eventually
      (Metric.ball_mem_nhds (0 : ℂ) hRpos)
    filter_upwards [ec, ez, et] with wt hcon hzb htb
    have hz_lt : ‖wt.1‖ < ρ := mem_ball_zero_iff.mp hzb
    have hslice_an : ∀ ζ : ℂ, ‖ζ‖ ≤ R → AnalyticAt ℂ (fun w => F (wt.1, w)) ζ := fun ζ hζ =>
      analyticAt_slice F (hFan (wt.1, ζ) (mem_ball_zero_iff.mpr (by
        rw [Prod.norm_mk]; exact max_lt hz_lt (lt_of_le_of_lt hζ hR_lt))))
    have hFc : ContinuousOn (fun w => F (wt.1, w)) (closedBall 0 R) := fun ζ hζ =>
      (hslice_an ζ (mem_closedBall_zero_iff.mp hζ)).continuousAt.continuousWithinAt
    have hFd : ∀ ζ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ (fun w => F (wt.1, w)) ζ := fun ζ hζ =>
      (hslice_an ζ (le_of_lt (mem_ball_zero_iff.mp hζ))).differentiableAt
    have key := cauchy_division_scalar (weierstrassPoly m a wt.1) hRpos hFc hFd hcon htb
    rw [weierstrassPoly_natDegree m a wt.1] at key
    have hsum : (∑ i : Fin m, ((2 * π * I)⁻¹ * ∮ ζ in C(0, R), F (wt.1, ζ) *
          (∑ j ∈ Finset.Ico ((i : ℕ) + 1) (m + 1), (weierstrassPoly m a wt.1).coeff j *
            ζ ^ (j - 1 - (i : ℕ))) / (weierstrassPoly m a wt.1).eval ζ) * wt.2 ^ (i : ℕ))
        = ∑ k ∈ range m, ((2 * π * I)⁻¹ * ∮ ζ in C(0, R), F (wt.1, ζ) *
          (∑ j ∈ Finset.Ico (k + 1) (m + 1), (weierstrassPoly m a wt.1).coeff j *
            ζ ^ (j - 1 - k)) / (weierstrassPoly m a wt.1).eval ζ) * wt.2 ^ k :=
      Fin.sum_univ_eq_sum_range (fun k => ((2 * π * I)⁻¹ * ∮ ζ in C(0, R), F (wt.1, ζ) *
          (∑ j ∈ Finset.Ico (k + 1) (m + 1), (weierstrassPoly m a wt.1).coeff j *
            ζ ^ (j - 1 - k)) / (weierstrassPoly m a wt.1).eval ζ) * wt.2 ^ k) m
    show F (wt.1, wt.2) = _
    rw [key, hsum]

open Metric in
/-- **Lagrange-type root bound (elementary; no argument principle).** For a Weierstrass polynomial
(`a_i(0) = 0`, `a_i` analytic hence continuous) and any `R > 0`, *all* roots of `W(z, ·)` lie in
`|ζ| < R` for `z` near `0`. The roots tend to `0` as `z → 0`: a root `α` satisfies
`|α|^m ≤ ∑_{i<m} |a_i(z)|·|α|^i`, so if `|a_i(z)| ≤ δ` then (forcing `|α| < 1` for `δm < 1`)
`|α|^m ≤ δm`, which is `< R^m` once `δ` is small. This is the input that makes Weierstrass-division
*uniqueness* independent of the argument principle. -/
theorem weierstrass_roots_eventually_in_ball (m : ℕ) (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ α : ℂ, (weierstrassPoly m a z).IsRoot α → ‖α‖ < R := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := min 1 (R ^ m) / (m + 1) with hδdef
  have hmin_pos : 0 < min 1 (R ^ m) := lt_min one_pos (by positivity)
  have hδpos : 0 < δ := div_pos hmin_pos (by positivity)
  have hδm_lt : δ * (m : ℝ) < min 1 (R ^ m) := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left (by linarith) hmin_pos
  have hδm1 : δ * (m : ℝ) < 1 := lt_of_lt_of_le hδm_lt (min_le_left 1 (R ^ m))
  have hδmR : δ * (m : ℝ) < R ^ m := lt_of_lt_of_le hδm_lt (min_le_right 1 (R ^ m))
  have hev : ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ i, ‖a i z‖ ≤ δ := by
    rw [eventually_all]
    intro i
    refine (((ha_an i).continuousAt.norm).eventually_lt continuousAt_const ?_).mono fun z h => h.le
    rw [ha0 i]; simpa using hδpos
  filter_upwards [hev] with z hz α hα
  -- root equation `α^m = -∑ a_i(z) α^i`
  have h0 : α ^ m + ∑ i : Fin m, a i z * α ^ (i : ℕ) = 0 := by
    have he : (weierstrassPoly m a z).eval α = 0 := hα
    simpa only [weierstrassPoly, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]
      using he
  -- norm inequality `‖α‖^m ≤ δ·∑ ‖α‖^i`
  have hnorm : ‖α‖ ^ m ≤ δ * ∑ i : Fin m, ‖α‖ ^ (i : ℕ) := by
    have hαm : α ^ m = -∑ i : Fin m, a i z * α ^ (i : ℕ) := eq_neg_of_add_eq_zero_left h0
    have he : ‖α‖ ^ m = ‖∑ i : Fin m, a i z * α ^ (i : ℕ)‖ := by
      rw [← norm_pow, hαm, norm_neg]
    rw [he]
    calc ‖∑ i : Fin m, a i z * α ^ (i : ℕ)‖
        ≤ ∑ i : Fin m, ‖a i z * α ^ (i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ i : Fin m, ‖a i z‖ * ‖α‖ ^ (i : ℕ) := by simp only [norm_mul, norm_pow]
      _ ≤ ∑ i : Fin m, δ * ‖α‖ ^ (i : ℕ) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hz i) (by positivity)
      _ = δ * ∑ i : Fin m, ‖α‖ ^ (i : ℕ) := by rw [Finset.mul_sum]
  -- bound argument
  rcases le_total 1 ‖α‖ with hr1 | hr1
  · exfalso
    have hsum_le : ∑ i : Fin m, ‖α‖ ^ (i : ℕ) ≤ (m : ℝ) * ‖α‖ ^ (m - 1) := by
      calc ∑ i : Fin m, ‖α‖ ^ (i : ℕ)
          ≤ ∑ _i : Fin m, ‖α‖ ^ (m - 1) :=
            Finset.sum_le_sum fun i _ => pow_le_pow_right₀ hr1 (Nat.le_pred_of_lt i.isLt)
        _ = (m : ℝ) * ‖α‖ ^ (m - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow_pos : 0 < ‖α‖ ^ (m - 1) := pow_pos (lt_of_lt_of_le one_pos hr1) _
    have hrm_eq : ‖α‖ ^ m = ‖α‖ * ‖α‖ ^ (m - 1) := by
      rw [mul_comm ‖α‖ (‖α‖ ^ (m - 1)), ← pow_succ, Nat.sub_add_cancel hm]
    have hrm : ‖α‖ * ‖α‖ ^ (m - 1) ≤ (δ * (m : ℝ)) * ‖α‖ ^ (m - 1) := by
      rw [← hrm_eq, mul_assoc]
      exact le_trans hnorm (mul_le_mul_of_nonneg_left hsum_le hδpos.le)
    have hr_le : ‖α‖ ≤ δ * (m : ℝ) := le_of_mul_le_mul_right hrm hpow_pos
    linarith
  · have hsum_le : ∑ i : Fin m, ‖α‖ ^ (i : ℕ) ≤ (m : ℝ) := by
      calc ∑ i : Fin m, ‖α‖ ^ (i : ℕ)
          ≤ ∑ _i : Fin m, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => pow_le_one₀ (norm_nonneg α) hr1
        _ = (m : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hrm : ‖α‖ ^ m ≤ δ * (m : ℝ) := le_trans hnorm (mul_le_mul_of_nonneg_left hsum_le hδpos.le)
    exact lt_of_pow_lt_pow_left₀ m hR.le (lt_of_le_of_lt hrm hδmR)

/-- The **remainder polynomial** `r(z, ·) = ∑_{i<m} ρ_i(z)·X^i` (degree `< m`), whose evaluation is
the `∑ ρ_i(z) t^i` remainder. -/
def remPoly (m : ℕ) (ρ : Fin m → (CParam s e → ℂ)) (z : CParam s e) : Polynomial ℂ :=
  ∑ i : Fin m, C (ρ i z) * X ^ (i : ℕ)

theorem remPoly_eval (m : ℕ) (ρ : Fin m → (CParam s e → ℂ)) (z : CParam s e) (t : ℂ) :
    (remPoly m ρ z).eval t = ∑ i : Fin m, ρ i z * t ^ (i : ℕ) := by
  simp only [remPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

theorem remPoly_natDegree_lt (m : ℕ) (hm : 0 < m) (ρ : Fin m → (CParam s e → ℂ))
    (z : CParam s e) : (remPoly m ρ z).natDegree < m := by
  have hdeg : (remPoly m ρ z).degree < (m : WithBot ℕ) := degree_sum_fin_lt (fun i => ρ i z)
  rcases eq_or_ne (remPoly m ρ z) 0 with h0 | h0
  · rw [h0, natDegree_zero]; exact hm
  · exact (natDegree_lt_iff_degree_lt h0).mpr hdeg

theorem remPoly_coeff (m : ℕ) (ρ : Fin m → (CParam s e → ℂ)) (z : CParam s e) (j : Fin m) :
    (remPoly m ρ z).coeff (j : ℕ) = ρ j z := by
  rw [remPoly, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hij (Fin.ext h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

open Complex MeasureTheory Metric Filter in
open scoped Real Topology in
/-- **Capstone (uniqueness): parametric Weierstrass division by `W`.** This is exactly Layer A's
`hdivW_uniq`, proved from the uniqueness cores. For `Q·W + r =ᶠ 0` (with `r = ∑ρ_i t^i`): at each `z`
near `0`, the Lagrange root bound puts all roots of `W(z,·)` inside `|ζ| < R`, so `rational_decay` +
`circleIntegral_eq_zero_of_decay` discharge the residue integral, and `cauchy_uniqueness_scalar`
(identity theorem + Cauchy recovery) gives `Q(z,·) ≡ 0`; hence `Q =ᶠ 0`. Then `r =ᶠ 0`, and since a
degree-`<m` polynomial vanishing on a `t`-disc is `0`, `ρ_i =ᶠ 0`. No argument principle. -/
theorem weierstrass_division_W_unique (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (Q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ))
    (hQ : AnalyticAt ℂ Q 0) (hρ : ∀ i, AnalyticAt ℂ (ρ i) 0)
    (hH : (fun wt => Q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0) :
    Q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0 := by
  -- the joint germ, split into slices via `Eventually.curry`
  have hHcurry : ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ᶠ t in 𝓝 (0 : ℂ),
      Q (z, t) * (weierstrassPoly m a z).eval t + ∑ i : Fin m, ρ i z * t ^ (i : ℕ) = 0 := by
    have h2 : ∀ᶠ wt in (𝓝 (0 : CParam s e)) ×ˢ (𝓝 (0 : ℂ)),
        Q wt * (weierstrassPoly m a wt.1).eval wt.2
          + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ) = 0 := by rw [← nhds_prod_eq]; exact hH
    exact h2.curry
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- `m = 0`: `W = 1`, no remainder; `Q =ᶠ 0` directly, `ρ` is vacuous
    subst hm0
    refine ⟨?_, fun i => i.elim0⟩
    filter_upwards [hH] with wt h
    simpa [weierstrassPoly] using h
  -- `m > 0`
  obtain ⟨ρQ, hρQ, hsliceQ⟩ := exists_slice_analytic Q hQ
  set R := ρQ / 2 with hRdef
  have hRpos : 0 < R := half_pos hρQ
  have hRR' : R < ρQ := by rw [hRdef]; linarith
  have hzball : ∀ᶠ z in 𝓝 (0 : CParam s e), ‖z‖ < ρQ :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : CParam s e) hρQ) fun z hz => mem_ball_zero_iff.mp hz
  have hroots := weierstrass_roots_eventually_in_ball m hm_pos a ha_an ha0 hRpos
  -- **Q =ᶠ 0**
  have hQ0 : Q =ᶠ[𝓝 (0 : CParam s e × ℂ)] 0 := by
    show ∀ᶠ wt in 𝓝 (0 : CParam s e × ℂ), Q wt = (0 : CParam s e × ℂ → ℂ) wt
    rw [show (0 : CParam s e × ℂ) = ((0 : CParam s e), (0 : ℂ)) from rfl, nhds_prod_eq,
      eventually_prod_iff]
    refine ⟨fun z => ‖z‖ < ρQ ∧ (∀ α : ℂ, (weierstrassPoly m a z).IsRoot α → ‖α‖ < R) ∧
        (∀ᶠ t in 𝓝 (0 : ℂ), Q (z, t) * (weierstrassPoly m a z).eval t
          + ∑ i : Fin m, ρ i z * t ^ (i : ℕ) = 0),
      (hzball.and (hroots.and hHcurry)).mono (fun z h => ⟨h.1, h.2.1, h.2.2⟩),
      fun t => ‖t‖ < R,
      Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) hRpos) fun t ht => mem_ball_zero_iff.mp ht, ?_⟩
    intro z hzprop t htprop
    obtain ⟨hzρ, hzroots, hzH⟩ := hzprop
    -- slice holomorphy
    have hslice_an : AnalyticOnNhd ℂ (fun w => Q (z, w)) (ball 0 ρQ) :=
      fun ζ hζ => hsliceQ z hzρ ζ (mem_ball_zero_iff.mp hζ)
    -- `W ≠ 0` on the contour (roots inside)
    have hPsphere : ∀ ζ ∈ sphere (0 : ℂ) R, (weierstrassPoly m a z).eval ζ ≠ 0 := by
      intro ζ hζ hcontra
      have hlt := hzroots ζ hcontra
      rw [mem_sphere_zero_iff_norm] at hζ; rw [hζ] at hlt; exact lt_irrefl R hlt
    -- the slice germ `Q(z,·)·W + r =ᶠ 0`
    have hHeq : (fun w => Q (z, w) * (weierstrassPoly m a z).eval w + (remPoly m ρ z).eval w)
        =ᶠ[𝓝 0] 0 := by
      filter_upwards [hzH] with w hw; rw [remPoly_eval]; exact hw
    -- residue input from decay + root bound
    have hres : (∮ ζ in C(0, R),
        (remPoly m ρ z).eval ζ / ((weierstrassPoly m a z).eval ζ * (ζ - t))) = 0 := by
      have hWne : ∀ ζ : ℂ, R ≤ ‖ζ‖ → (weierstrassPoly m a z).eval ζ ≠ 0 := by
        intro ζ hζR hcontra; have := hzroots ζ hcontra; linarith
      have hζtne : ∀ ζ : ℂ, R ≤ ‖ζ‖ → ζ - t ≠ 0 := by
        intro ζ hζR h; rw [sub_eq_zero] at h; rw [h] at hζR; linarith [htprop]
      obtain ⟨R₀, C, _, hdecay⟩ := rational_decay (weierstrassPoly m a z) (remPoly m ρ z)
        (by rw [weierstrassPoly_natDegree]; exact hm_pos) (weierstrassPoly_monic m a z)
        (by rw [weierstrassPoly_natDegree]; exact remPoly_natDegree_lt m hm_pos ρ z) t
      refine circleIntegral_eq_zero_of_decay hRpos (le_max_left R R₀) C (fun ζ hζR => ?_)
        (fun ζ hζR => hdecay ζ (le_trans (le_max_right R R₀) hζR))
      exact (((AnalyticOnNhd.eval_polynomial (remPoly m ρ z) ζ (Set.mem_univ ζ)).differentiableAt).div
        (((AnalyticOnNhd.eval_polynomial (weierstrassPoly m a z) ζ
          (Set.mem_univ ζ)).differentiableAt).mul (differentiableAt_id.sub_const t))
        (mul_ne_zero (hWne ζ hζR) (hζtne ζ hζR)))
    exact cauchy_uniqueness_scalar (weierstrassPoly m a z) hRpos hRR' hslice_an hPsphere hHeq
      (mem_ball_zero_iff.mpr htprop) hres
  refine ⟨hQ0, fun i => ?_⟩
  -- **ρ_i =ᶠ 0**: the remainder slice is `=ᶠ 0`, so `remPoly z = 0`, so `ρ_i z = 0`
  have hQcurry : ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ᶠ t in 𝓝 (0 : ℂ), Q (z, t) = 0 := by
    have h2 : ∀ᶠ wt in (𝓝 (0 : CParam s e)) ×ˢ (𝓝 (0 : ℂ)), Q wt = 0 := by
      rw [← nhds_prod_eq]; exact hQ0
    exact h2.curry
  have hr0 : ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ j : Fin m, ρ j z = 0 := by
    filter_upwards [hHcurry, hQcurry] with z hzH hzQ
    have hsum : ∀ᶠ t in 𝓝 (0 : ℂ), ∑ i : Fin m, ρ i z * t ^ (i : ℕ) = 0 := by
      filter_upwards [hzH, hzQ] with t htH htQ
      rw [htQ, zero_mul, zero_add] at htH; exact htH
    have hrem0 : remPoly m ρ z = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot _ (infinite_of_mem_nhds (0 : ℂ) ?_)
      filter_upwards [hsum] with t ht
      show (remPoly m ρ z).eval t = 0
      rw [remPoly_eval]; exact ht
    intro j; rw [← remPoly_coeff m ρ z j, hrem0, coeff_zero]
  filter_upwards [hr0] with z hz; exact hz i


open Complex MeasureTheory Metric in
open scoped Real Topology in
/-- **Full chain (Layer A ∘ Layer B): `weierstrass_division ⟸ {preparation, keystone}`.** The complete
`weierstrass_division` conclusion (existence **and uniqueness**) for a `t`-regular germ `G` follows from
just a preparation `G = u·W` (Layer C's job) and the **keystone** (modulo `osgood`). Existence is the
capstone `weierstrass_division_W_exists`; **uniqueness is now fully discharged** by
`weierstrass_division_W_unique` (no longer a hypothesis); Layer A (`weierstrass_division_of_prep_div`)
moves the unit. So the only remaining inputs to the entire Cauchy proof of `weierstrass_division` are
preparation (Layer C) and the keystone (= `osgood`). -/
theorem weierstrass_division_via_cauchy
    (G : CParam s e × ℂ → ℂ) (m : ℕ)
    (u : CParam s e × ℂ → ℂ) (a : Fin m → (CParam s e → ℂ))
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hGW : G =ᶠ[𝓝 0] fun wt => u wt * (weierstrassPoly m a wt.1).eval wt.2)
    (keystone : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
      (Φ : H × ℂ → ℂ) {r : ℝ} {p₀ : H}, 0 < r →
      (∀ ζ ∈ sphere (0 : ℂ) r, AnalyticAt ℂ Φ (p₀, ζ)) →
      AnalyticAt ℂ (fun p : H => ∮ ζ in C(0, r), Φ (p, ζ)) p₀) :
    (∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) ∧
    (∀ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0) :=
  weierstrass_division_of_prep_div G m u a hu hu0 hGW
    (fun F hF => weierstrass_division_W_exists m a ha_an ha0 keystone F hF)
    (fun Q ρ hQ hρ hHeq => weierstrass_division_W_unique m a ha_an ha0 Q ρ hQ hρ hHeq)

end
