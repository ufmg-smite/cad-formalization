import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVPackage
import Cad.Multivariate.ProjectionTheorem.Puiseux.Connectedness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# G1 — Multivariable removable singularity across a coordinate hyperplane

The `Fin 1 → ℂ` connectedness kernel extends a bounded, separable-locus-analytic factor coefficient
across the *isolated* discriminant point `0` (one-variable Riemann removable singularity). To lift the
kernel to a general base `H × ℂ` (`H` the section parameters, `ℂ` the distinguished transverse
coordinate, the normal-form setting `disc = w^r·N`), the singular set becomes the **coordinate
hyperplane** `{w = 0}`, and the extension is the *parameter Cauchy integral*

  `G(y, w) = (2πi)⁻¹ ∮_{|ζ|=r} (ζ − w)⁻¹ · F(y, ζ) dζ`,

jointly analytic in `(y, w)` by the project's parametric-analyticity keystone
`circleIntegral_analyticAt_fiber` (the same SCV infrastructure that powers `weierstrass_division`),
and equal to `F` off `{w = 0}` by the one-variable Cauchy integral formula on each Riemann-extended
fibre.

**Status (axiom-clean, not yet imported):**
* **G1** — `exists_analyticAt_extend_hyperplane` over `H × ℂ` (analyticity `cauchyExtend_analyticAt` +
  agreement `cauchyExtend_eq_fiber`), and its filter form `exists_analyticAt_extend_hyperplane_nhds`.
* **G2a** — `exists_analyticAt_extend_funCoord0`: G1 transported to `Fin (n+1) → ℂ` (extension across
  `{coord 0 = 0}`) through the coordinate-split CLE `coord0Equiv`.

Consumed by the generalized connectedness kernel (task G2b/c, see `MONODROMY_PLAN.md`).
-/

noncomputable section

open Complex Metric Topology Filter Set
open scoped Real

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The parameter Cauchy integral `G(y,w) = (2πi)⁻¹ ∮_{|ζ|=r} (ζ−w)⁻¹·F(y,ζ) dζ`, the candidate
analytic extension of `F : H × ℂ → ℂ` across the hyperplane `{w = 0}`. -/
def cauchyExtend (F : H × ℂ → ℂ) (r : ℝ) : H × ℂ → ℂ :=
  fun p => ∮ ζ in C(0, r), (2 * π * I)⁻¹ * (ζ - p.2)⁻¹ * F (p.1, ζ)

/-- **Analyticity of the parameter Cauchy extension.** If `F` is analytic at `(y₀, ζ)` for every `ζ`
on the circle `|ζ| = r`, then `cauchyExtend F r` is analytic at `(y₀, 0)`. Direct application of the
parametric-analyticity keystone `circleIntegral_analyticAt_fiber`. -/
theorem cauchyExtend_analyticAt [FiniteDimensional ℂ H] {F : H × ℂ → ℂ} {y₀ : H} {r : ℝ}
    (hr : 0 < r) (hFan : ∀ ζ ∈ sphere (0 : ℂ) r, AnalyticAt ℂ F (y₀, ζ)) :
    AnalyticAt ℂ (cauchyExtend F r) (y₀, 0) := by
  refine circleIntegral_analyticAt_fiber
    (fun q : (H × ℂ) × ℂ => (2 * π * I)⁻¹ * (q.2 - q.1.2)⁻¹ * F (q.1.1, q.2)) hr ?_
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mem_sphere_iff_norm, sub_zero, norm_zero] at hζ
    exact hr.ne' hζ.symm
  -- `q ↦ q.2 - q.1.2`, analytic, nonzero (`= ζ - 0 = ζ ≠ 0`) at `((y₀,0), ζ)`
  have hsub : AnalyticAt ℂ (fun q : (H × ℂ) × ℂ => q.2 - q.1.2) (((y₀, 0), ζ)) :=
    analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)
  have hsub_ne : (fun q : (H × ℂ) × ℂ => q.2 - q.1.2) ((y₀, 0), ζ) ≠ 0 := by
    simpa using hζ0
  -- `q ↦ F (q.1.1, q.2)`, analytic at `((y₀,0), ζ)` since `F` is analytic at `(y₀, ζ)`
  have hg : AnalyticAt ℂ (fun q : (H × ℂ) × ℂ => (q.1.1, q.2)) (((y₀, 0), ζ)) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hF : AnalyticAt ℂ (fun q : (H × ℂ) × ℂ => F (q.1.1, q.2)) (((y₀, 0), ζ)) :=
    (hFan ζ hζ).comp_of_eq hg rfl
  exact (analyticAt_const.mul (hsub.inv hsub_ne)).mul hF

/-- **The parameter Cauchy extension agrees with `F` off the hyperplane, fibrewise.** For a fixed
section point `y`, if `F(y, ·)` is analytic and bounded on the punctured disc `0 < |ζ| < R`, then for
`0 < |w| < r < R`, `cauchyExtend F r (y, w) = F (y, w)`. (Riemann-extend `F(y,·)` across `0`, apply the
one-variable Cauchy integral formula, and use that `F` and the extension agree on the circle.) -/
theorem cauchyExtend_eq_fiber {F : H × ℂ → ℂ} {y : H} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hFan : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < R → AnalyticAt ℂ F (y, ζ))
    {M : ℝ} (hFbd : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < R → ‖F (y, ζ)‖ ≤ M)
    {w : ℂ} (hw0 : 0 < ‖w‖) (hwr : ‖w‖ < r) :
    cauchyExtend F r (y, w) = F (y, w) := by
  have hR : (0 : ℝ) < R := lt_trans hr hrR
  set g : ℂ → ℂ := fun ζ => F (y, ζ) with hgdef
  have hgan : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < R → AnalyticAt ℂ g ζ := fun ζ h0 hR' =>
    (hFan ζ h0 hR').comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  set L := limUnder (𝓝[≠] (0 : ℂ)) g with hLdef
  set gext : ℂ → ℂ := Function.update g 0 L with hgextdef
  -- `gext` is analytic on `ball 0 R`
  have hgext_an : ∀ ζ ∈ Metric.ball (0 : ℂ) R, AnalyticAt ℂ gext ζ := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_zero_right] at hζ
    rcases eq_or_ne ζ 0 with rfl | hζ0
    · refine analyticAt_update_limUnder_of_bddUnder ?_ ?_
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hR)] with z hz0 hzR
        rw [mem_compl_iff, mem_singleton_iff] at hz0
        rw [Metric.mem_ball, dist_zero_right] at hzR
        exact (hgan z (norm_pos_iff.mpr hz0) hzR).differentiableAt
      · refine ⟨M + ‖g 0‖, ?_⟩
        rw [Filter.eventually_map]
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hR)] with z hz0 hzR
        rw [mem_compl_iff, mem_singleton_iff] at hz0
        rw [Metric.mem_ball, dist_zero_right] at hzR
        calc ‖g z - g 0‖ ≤ ‖g z‖ + ‖g 0‖ := norm_sub_le _ _
          _ ≤ M + ‖g 0‖ := by linarith [hFbd z (norm_pos_iff.mpr hz0) hzR]
    · have heq : gext =ᶠ[𝓝 ζ] g := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hζ0] with z hz
        exact Function.update_of_ne (by simpa using hz) L g
      exact (hgan ζ (norm_pos_iff.mpr hζ0) hζ).congr heq.symm
  -- `gext` differentiable on `closedBall 0 r`
  have hgext_diff : DifferentiableOn ℂ gext (Metric.closedBall (0 : ℂ) r) := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    exact (hgext_an ζ (by rw [Metric.mem_ball, dist_zero_right]; linarith)).differentiableAt
      |>.differentiableWithinAt
  have hwball : w ∈ Metric.ball (0 : ℂ) r := by rw [Metric.mem_ball, dist_zero_right]; exact hwr
  have hcauchy : (∮ z in C(0, r), (z - w)⁻¹ • gext z) = (2 * π * I : ℂ) • gext w :=
    hgext_diff.circleIntegral_sub_inv_smul hwball
  -- the circle integrals of `g` and `gext` coincide (they differ only at `0`, off the circle)
  have hcong : (∮ z in C(0, r), (z - w)⁻¹ • g z) = ∮ z in C(0, r), (z - w)⁻¹ • gext z := by
    rw [circleIntegral, circleIntegral]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hne : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
    rw [show gext (circleMap 0 r θ) = g (circleMap 0 r θ) from Function.update_of_ne hne L g]
  -- assemble
  have hgextw : gext w = g w := Function.update_of_ne (norm_pos_iff.mp hw0) L g
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  show (∮ ζ in C(0, r), (2 * π * I)⁻¹ * (ζ - w)⁻¹ * F (y, ζ)) = F (y, w)
  have hrw : ∀ ζ : ℂ, (2 * π * I)⁻¹ * (ζ - w)⁻¹ * F (y, ζ)
      = (2 * π * I)⁻¹ • ((ζ - w)⁻¹ • g ζ) := by
    intro ζ; simp [smul_eq_mul, hgdef, mul_assoc]
  rw [show (fun ζ => (2 * π * I)⁻¹ * (ζ - w)⁻¹ * F (y, ζ))
        = (fun ζ => (2 * π * I)⁻¹ • ((ζ - w)⁻¹ • g ζ)) from funext hrw,
    circleIntegral.integral_smul, hcong, hcauchy, hgextw, smul_smul, inv_mul_cancel₀ h2pi, one_smul,
    hgdef]

/-- **G1 — multivariable removable singularity across the coordinate hyperplane `{w = 0}`.** If
`F : H × ℂ → ℂ` is analytic and uniformly bounded on the punctured tube `{(y,ζ) : dist y y₀ < R,
0 < |ζ| < R}`, then it extends to a function `G` analytic at `(y₀, 0)` that agrees with `F` off the
hyperplane (for `dist y y₀ < R`, `0 < |w| < r`). The extension is the parameter Cauchy integral
`cauchyExtend F r`. This is the `Fin n` replacement for the one-variable removable singularity
`exists_analyticAt_extend_funUnique`. -/
theorem exists_analyticAt_extend_hyperplane [FiniteDimensional ℂ H]
    {F : H × ℂ → ℂ} {y₀ : H} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hFan : ∀ y, dist y y₀ < R → ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < R → AnalyticAt ℂ F (y, ζ))
    {M : ℝ} (hFbd : ∀ y, dist y y₀ < R → ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < R → ‖F (y, ζ)‖ ≤ M) :
    ∃ G : H × ℂ → ℂ, AnalyticAt ℂ G (y₀, 0) ∧
      (∀ y, dist y y₀ < R → ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r → G (y, w) = F (y, w)) := by
  have hR : (0 : ℝ) < R := lt_trans hr hrR
  refine ⟨cauchyExtend F r, ?_, ?_⟩
  · refine cauchyExtend_analyticAt hr (fun ζ hζ => ?_)
    rw [mem_sphere_iff_norm, sub_zero] at hζ
    exact hFan y₀ (by rw [dist_self]; exact hR) ζ (by rw [hζ]; exact hr) (by rw [hζ]; exact hrR)
  · intro y hy w hw0 hwr
    exact cauchyExtend_eq_fiber hr hrR (fun ζ => hFan y hy ζ) (fun ζ => hFbd y hy ζ) hw0 hwr


/-- **G1, neighbourhood form.** The filter-based restatement consumed by the generalized kernel: if `F`
is analytic off the hyperplane on a *neighbourhood* of `(y₀,0)` and bounded there, it extends to a
function analytic at `(y₀,0)` agreeing with `F` off `{w=0}` near `(y₀,0)`. (Product balls in `H × ℂ`
are tubes `{dist y y₀ < ρ} × {|ζ| < ρ}`, so the explicit-radius form applies after extracting a ball.) -/
theorem exists_analyticAt_extend_hyperplane_nhds [FiniteDimensional ℂ H]
    {F : H × ℂ → ℂ} {y₀ : H}
    (hFan : ∀ᶠ p in 𝓝 ((y₀, 0) : H × ℂ), p.2 ≠ 0 → AnalyticAt ℂ F p)
    {M : ℝ} (hbd : ∀ᶠ p in 𝓝 ((y₀, 0) : H × ℂ), ‖F p‖ ≤ M) :
    ∃ G : H × ℂ → ℂ, AnalyticAt ℂ G (y₀, 0) ∧
      (∀ᶠ p in 𝓝 ((y₀, 0) : H × ℂ), p.2 ≠ 0 → G p = F p) := by
  rw [Metric.eventually_nhds_iff] at hFan hbd
  obtain ⟨ε₁, hε₁, hFan'⟩ := hFan
  obtain ⟨ε₂, hε₂, hbd'⟩ := hbd
  have hρ : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  set r := min ε₁ ε₂ / 4 with hrdef
  set R := min ε₁ ε₂ / 2 with hRdef
  have hr : 0 < r := by positivity
  have hrR : r < R := by rw [hrdef, hRdef]; linarith
  have hdist : ∀ (y : H) (ζ : ℂ), dist ((y, ζ) : H × ℂ) (y₀, 0) = max (dist y y₀) ‖ζ‖ := by
    intro y ζ; rw [Prod.dist_eq]; simp [dist_zero_right]
  have hRε₁ : R < ε₁ := by rw [hRdef]; have := min_le_left ε₁ ε₂; linarith
  have hRε₂ : R < ε₂ := by rw [hRdef]; have := min_le_right ε₁ ε₂; linarith
  obtain ⟨G, hGan, hGeq⟩ := exists_analyticAt_extend_hyperplane (F := F) (y₀ := y₀) hr hrR
    (fun y hy ζ h0 hζR => hFan' (by rw [hdist]; exact lt_trans (max_lt hy hζR) hRε₁)
      (norm_pos_iff.mp h0))
    (M := M) (fun y hy ζ h0 hζR => hbd' (by rw [hdist]; exact lt_trans (max_lt hy hζR) hRε₂))
  refine ⟨G, hGan, ?_⟩
  rw [Metric.eventually_nhds_iff]
  refine ⟨r, hr, fun p hp hp2 => ?_⟩
  rw [show p = (p.1, p.2) from rfl, hdist] at hp
  exact hGeq p.1 (lt_trans (lt_of_le_of_lt (le_max_left _ _) hp) hrR) p.2 (norm_pos_iff.mpr hp2)
    (lt_of_le_of_lt (le_max_right _ _) hp)

section Coord0

variable {n : ℕ}

/-- The continuous linear equivalence splitting off coordinate `0`: `(v, w) ↦ Fin.cons w v`, with
`w` becoming coordinate `0`. Built from `Fin.consLinearEquiv` (finite-dimensional, so continuous). -/
def coord0Equiv : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
  ((LinearEquiv.prodComm ℂ (Fin n → ℂ) ℂ).trans
    (Fin.consLinearEquiv ℂ (fun _ : Fin (n + 1) => ℂ))).toContinuousLinearEquiv

@[simp] theorem coord0Equiv_apply (v : Fin n → ℂ) (w : ℂ) :
    coord0Equiv (v, w) = Fin.cons w v := rfl

@[simp] theorem coord0Equiv_symm_apply (x : Fin (n + 1) → ℂ) :
    coord0Equiv.symm x = (Fin.tail x, x 0) := rfl

end Coord0

/-- **G2a — G1 over `Fin (n+1) → ℂ`, extending across `{coord 0 = 0}`.** If `F` is analytic off the
coordinate hyperplane `{x 0 = 0}` on a neighbourhood of `x₀` (with `x₀ 0 = 0`) and bounded there, it
extends to `G` analytic at `x₀` agreeing with `F` off `{x 0 = 0}`. Transport of
`exists_analyticAt_extend_hyperplane_nhds` (G1) through the coordinate-split CLE `coord0Equiv`. -/
theorem exists_analyticAt_extend_funCoord0 {n : ℕ} {F : (Fin (n + 1) → ℂ) → ℂ}
    {x₀ : Fin (n + 1) → ℂ} (hx0 : x₀ 0 = 0)
    (hFan : ∀ᶠ x in 𝓝 x₀, x 0 ≠ 0 → AnalyticAt ℂ F x)
    {M : ℝ} (hbd : ∀ᶠ x in 𝓝 x₀, ‖F x‖ ≤ M) :
    ∃ G : (Fin (n + 1) → ℂ) → ℂ, AnalyticAt ℂ G x₀ ∧
      (∀ᶠ x in 𝓝 x₀, x 0 ≠ 0 → G x = F x) := by
  set e := coord0Equiv (n := n) with hedef
  set y₀ := Fin.tail x₀ with hy₀def
  have hsymm : e.symm x₀ = (y₀, (0 : ℂ)) := by
    rw [hedef, coord0Equiv_symm_apply, hy₀def, hx0]
  have he_y₀0 : e (y₀, (0 : ℂ)) = x₀ := by rw [← hsymm, ContinuousLinearEquiv.apply_symm_apply]
  have hcoord : ∀ p : (Fin n → ℂ) × ℂ, (e p) 0 = p.2 := by
    rintro ⟨v, w⟩; rw [hedef, coord0Equiv_apply, Fin.cons_zero]
  have htend : Tendsto e (𝓝 ((y₀, (0 : ℂ)) : (Fin n → ℂ) × ℂ)) (𝓝 x₀) := by
    rw [← he_y₀0]; exact e.continuous.continuousAt
  have hFan' : ∀ᶠ p in 𝓝 ((y₀, (0 : ℂ)) : (Fin n → ℂ) × ℂ), p.2 ≠ 0 → AnalyticAt ℂ (F ∘ e) p := by
    filter_upwards [htend.eventually hFan] with p hp hp2
    exact (hp ((hcoord p) ▸ hp2)).comp
      ((e : (Fin n → ℂ) × ℂ →L[ℂ] (Fin (n + 1) → ℂ)).analyticAt p)
  have hbd' : ∀ᶠ p in 𝓝 ((y₀, (0 : ℂ)) : (Fin n → ℂ) × ℂ), ‖(F ∘ e) p‖ ≤ M := by
    filter_upwards [htend.eventually hbd] with p hp using hp
  obtain ⟨G', hG'an, hG'eq⟩ := exists_analyticAt_extend_hyperplane_nhds hFan' hbd'
  refine ⟨G' ∘ e.symm, ?_, ?_⟩
  · have hG'x₀ : AnalyticAt ℂ G' (e.symm x₀) := hsymm ▸ hG'an
    exact hG'x₀.comp
      ((e.symm : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) × ℂ).analyticAt x₀)
  · have htend' : Tendsto e.symm (𝓝 x₀) (𝓝 ((y₀, (0 : ℂ)) : (Fin n → ℂ) × ℂ)) := by
      rw [← hsymm]; exact e.symm.continuous.continuousAt
    filter_upwards [htend'.eventually hG'eq] with x hx hx0'
    have hcoord' : (e.symm x).2 = x 0 := by rw [hedef, coord0Equiv_symm_apply]
    have h := hx (hcoord' ▸ hx0')
    show G' (e.symm x) = F x
    rw [h]; show F (e (e.symm x)) = F x; rw [ContinuousLinearEquiv.apply_symm_apply]

