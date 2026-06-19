import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Covering.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Complex analytic root section — the local section of the branched root-covering (M2)

This file ports the real `analytic_root_section` (`Cad.Multivariate.ProjectionTheorem.Generalized.SimpleRoots`) to the **complex**
setting: at a *simple* root of a holomorphic family of complex polynomials, the implicit function
theorem yields a unique local **holomorphic** root function. This is the local building block of the
branched root-covering used in the monodromy proof of `irreducible_section_single_root` (the A4 core).

* `analytic_root_section_complex` — the complex analytic IFT for a scalar equation: if `F` is
  ℂ-analytic at `(y₀, t₀)`, `F(y₀,t₀)=0`, and `∂F/∂t ≠ 0`, then `F(y,t)=0` has a unique local
  holomorphic solution `t = φ(y)`.

The proof is the complex analytic inverse function theorem applied to `G(y,t) = (y, F(y,t))`, exactly
as in the real case; only the uniqueness window `|t-t₀| < ε` is restated as `dist t t₀ < ε`.
-/

noncomputable section

open Polynomial Set
open scoped Topology

variable {n : ℕ}

/-- **Complex analytic IFT for a scalar equation** (generic holomorphic root section).

If `F : (ℂⁿ × ℂ) → ℂ` is analytic at `(y₀, t₀)`, `F(y₀, t₀) = 0`, and the partial derivative
`∂F/∂t` at `(y₀, t₀)` (i.e. `fderiv F (y₀,t₀) (0,1)`) is nonzero, then `F(y, t) = 0` has a unique
local holomorphic solution `t = φ(y)`: there are a neighborhood `U ∋ y₀`, an analytic `φ` with
`φ(y₀) = t₀`, and `ε > 0` such that `F(y, φ y) = 0` on `U`, and `φ(y)` is the unique root within
distance `ε` of `t₀`. -/
theorem analytic_root_section_complex
    (F : (Fin n → ℂ) × ℂ → ℂ) (y₀ : Fin n → ℂ) (t₀ : ℂ)
    (hF_an : AnalyticAt ℂ F (y₀, t₀))
    (hroot : F (y₀, t₀) = 0)
    (hsimple : fderiv ℂ F (y₀, t₀) (0, 1) ≠ 0) :
    ∃ (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℂ) (ε : ℝ),
      IsOpen U ∧ y₀ ∈ U ∧
      AnalyticOn ℂ φ U ∧
      φ y₀ = t₀ ∧
      0 < ε ∧
      (∀ y ∈ U, F (y, φ y) = 0) ∧
      (∀ y ∈ U, ∀ t, F (y, t) = 0 → dist t t₀ < ε → t = φ y) := by
  let Ep := (Fin n → ℂ) × ℂ
  let G : Ep → Ep := fun p => (p.1, F p)
  set c := fderiv ℂ F (y₀, t₀) (0, 1) with hc_def
  have hc_ne : c ≠ 0 := hsimple
  have hF_diff : DifferentiableAt ℂ F (y₀, t₀) := hF_an.differentiableAt
  have hF_partial : ∀ k : ℂ, fderiv ℂ F (y₀, t₀) (0, k) = c * k := by
    intro k
    have hk : ((0 : Fin n → ℂ), k) = k • ((0 : Fin n → ℂ), (1 : ℂ)) := by
      ext i <;> simp
    rw [hk, map_smul, ← hc_def, smul_eq_mul, mul_comm]
  have hG_an : AnalyticAt ℂ G (y₀, t₀) := analyticAt_fst.prod hF_an
  have hG_fderiv_eq : fderiv ℂ G (y₀, t₀) =
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).prod (fderiv ℂ F (y₀, t₀)) := by
    show fderiv ℂ (fun x : Ep => (x.1, F x)) (y₀, t₀) = _
    rw [DifferentiableAt.fderiv_prodMk differentiableAt_fst hF_diff, fderiv_fst]
  have hDG_val : ∀ u : Ep, fderiv ℂ G (y₀, t₀) u = (u.1, fderiv ℂ F (y₀, t₀) u) := by
    intro u; rw [hG_fderiv_eq]; rfl
  have hDG_bij : Function.Bijective (fderiv ℂ G (y₀, t₀)) := by
    constructor
    · intro v w hvw
      rw [hDG_val v, hDG_val w] at hvw
      have h1 : v.1 = w.1 := (Prod.mk.inj hvw).1
      have h2 : fderiv ℂ F (y₀, t₀) v = fderiv ℂ F (y₀, t₀) w := (Prod.mk.inj hvw).2
      have h3 : fderiv ℂ F (y₀, t₀) (0, v.2 - w.2) = 0 := by
        rw [show ((0 : Fin n → ℂ), v.2 - w.2) = v - w from
          Prod.ext (sub_eq_zero.mpr h1).symm rfl, map_sub, sub_eq_zero.mpr h2]
      rw [hF_partial] at h3
      exact Prod.ext h1 (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc_ne))
    · intro ⟨v, w⟩
      refine ⟨(v, (w - fderiv ℂ F (y₀, t₀) (v, 0)) / c), ?_⟩
      rw [hDG_val]; exact Prod.ext rfl (by
        show fderiv ℂ F (y₀, t₀) (v, (w - fderiv ℂ F (y₀, t₀) (v, 0)) / c) = w
        rw [show (v, (w - fderiv ℂ F (y₀, t₀) (v, 0)) / c) =
          ((v : Fin n → ℂ), (0 : ℂ)) + ((0 : Fin n → ℂ),
            (w - fderiv ℂ F (y₀, t₀) (v, 0)) / c) from Prod.ext (by simp) (by simp),
          map_add, hF_partial]
        field_simp; ring)
  let i : Ep ≃L[ℂ] Ep :=
    (LinearEquiv.ofBijective (fderiv ℂ G (y₀, t₀)).toLinearMap hDG_bij).toContinuousLinearEquiv
  have hi : fderiv ℂ G (y₀, t₀) = i.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun _ => rfl
  have hG_strict : HasStrictFDerivAt G (i : Ep →L[ℂ] Ep) (y₀, t₀) :=
    hi ▸ hG_an.hasStrictFDerivAt
  let R := hG_strict.toOpenPartialHomeomorph G
  have hR_source : (y₀, t₀) ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hG_val : G (y₀, t₀) = (y₀, (0 : ℂ)) := Prod.ext rfl hroot
  have hR_target_mem : (y₀, (0 : ℂ)) ∈ R.target := by
    have : G (y₀, t₀) ∈ R.target := R.map_source hR_source
    rwa [hG_val] at this
  have hR_an_symm : AnalyticAt ℂ R.symm (y₀, (0 : ℂ)) := by
    have : AnalyticAt ℂ R.symm (G (y₀, t₀)) := R.analyticAt_symm' hR_source hG_an hi
    rwa [hG_val] at this
  obtain ⟨r_an, hr_an_pos, hR_ball_an⟩ := hR_an_symm.exists_ball_analyticOnNhd
  obtain ⟨δ_a, δ_y, hδ_a, hδ_y, hball_src⟩ : ∃ δ_a δ_y : ℝ, 0 < δ_a ∧ 0 < δ_y ∧
      Metric.ball y₀ δ_a ×ˢ Metric.ball t₀ δ_y ⊆ R.source := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp R.open_source (y₀, t₀) hR_source
    exact ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, fun ⟨a, y⟩ ⟨ha, hy⟩ => hball (
      max_lt (lt_trans (Metric.mem_ball.mp ha) (half_lt_self hδ))
             (lt_trans (Metric.mem_ball.mp hy) (half_lt_self hδ)))⟩
  obtain ⟨δ_ta, δ_t0, hδ_ta, hδ_t0, hball_tgt⟩ : ∃ δ_ta δ_t0 : ℝ, 0 < δ_ta ∧ 0 < δ_t0 ∧
      Metric.ball y₀ δ_ta ×ˢ Metric.ball (0 : ℂ) δ_t0 ⊆ R.target := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp R.open_target (y₀, 0) hR_target_mem
    exact ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, fun ⟨a, y⟩ ⟨ha, hy⟩ => hball (
      max_lt (lt_trans (Metric.mem_ball.mp ha) (half_lt_self hδ))
             (lt_trans (Metric.mem_ball.mp hy) (half_lt_self hδ)))⟩
  let φ₀ : (Fin n → ℂ) → ℂ := fun a => (R.symm (a, 0)).2
  let U₀ := Metric.ball y₀ (min (min δ_ta δ_a) r_an)
  have hφ₀_val : φ₀ y₀ = t₀ := by
    show (R.symm (y₀, 0)).2 = t₀
    have h : R.symm (G (y₀, t₀)) = (y₀, t₀) := R.left_inv hR_source
    rw [hG_val] at h; exact congrArg Prod.snd h
  have hφ₀_root : ∀ a, (a, (0 : ℂ)) ∈ R.target → F (a, φ₀ a) = 0 := by
    intro a hmem
    have hright : G (R.symm (a, 0)) = (a, 0) := R.right_inv hmem
    have h1 : (R.symm (a, 0)).1 = a := congrArg Prod.fst hright
    have h2 : F (R.symm (a, 0)) = 0 := congrArg Prod.snd hright
    show F (a, (R.symm (a, 0)).2) = 0
    rw [show (a, (R.symm (a, 0)).2) = R.symm (a, 0) from Prod.ext h1.symm rfl]; exact h2
  have hφ₀_an : AnalyticOn ℂ φ₀ U₀ := by
    intro a ha
    have ha_r : dist a y₀ < r_an :=
      lt_of_lt_of_le (Metric.mem_ball.mp ha) (min_le_right _ _)
    have hR_an_local : AnalyticAt ℂ R.symm (a, (0 : ℂ)) := by
      apply hR_ball_an; rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt ha_r (by rw [dist_self]; exact hr_an_pos)
    have hpair : AnalyticAt ℂ (fun x : Fin n → ℂ => (x, (0 : ℂ))) a :=
      (analyticAt_id (𝕜 := ℂ)).prod analyticAt_const
    exact (analyticAt_snd.comp (hR_an_local.comp_of_eq' hpair rfl)).analyticWithinAt
  have hφ₀_unique : ∀ a ∈ U₀, ∀ y, F (a, y) = 0 →
      dist y t₀ < δ_y → y = φ₀ a := by
    intro a ha y hy_root hy_close
    have ha_ball : a ∈ Metric.ball y₀ δ_a :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (lt_of_lt_of_le (Metric.mem_ball.mp ha)
        (min_le_left _ _)) (min_le_right _ _))
    have hy_ball : y ∈ Metric.ball t₀ δ_y := Metric.mem_ball.mpr hy_close
    have ha_source : (a, y) ∈ R.source := hball_src ⟨ha_ball, hy_ball⟩
    have hGay : G (a, y) = (a, (0 : ℂ)) := Prod.ext rfl hy_root
    show y = (R.symm (a, 0)).2
    have hinv : R.symm (G (a, y)) = (a, y) := R.left_inv ha_source
    rw [hGay] at hinv; exact (congrArg Prod.snd hinv).symm
  exact ⟨U₀, φ₀, δ_y, Metric.isOpen_ball,
    Metric.mem_ball_self (lt_min (lt_min hδ_ta hδ_a) hr_an_pos),
    hφ₀_an, hφ₀_val, hδ_y,
    fun a ha => hφ₀_root a (hball_tgt ⟨Metric.mem_ball.mpr (lt_of_lt_of_le
      (lt_of_lt_of_le (Metric.mem_ball.mp ha) (min_le_left _ _)) (min_le_left _ _)),
      Metric.mem_ball_self hδ_t0⟩),
    hφ₀_unique⟩

/-- **Local disjoint root sections** (the analytic "evenly covered" data).

If `F` is analytic at each `(y₁, t j)` for a family of `d` *distinct simple* roots `t : Fin d → ℂ`
of the scalar equation `F(y₁, ·) = 0`, then on a common neighborhood `U ∋ y₁` there are holomorphic
sections `φ j : U → ℂ` with `φ j y₁ = t j`, each solving `F(y, φ j y) = 0`, whose graphs are pairwise
**disjoint** over `U` (`φ i y ≠ φ j y` for `i ≠ j`). These `d` disjoint analytic sheets are exactly
the local trivialization of the branched root-covering away from the discriminant locus. -/
theorem local_disjoint_root_sections
    (F : (Fin n → ℂ) × ℂ → ℂ) (y₁ : Fin n → ℂ) (d : ℕ) (t : Fin d → ℂ)
    (ht_inj : Function.Injective t)
    (hF_an : ∀ j, AnalyticAt ℂ F (y₁, t j))
    (hroot : ∀ j, F (y₁, t j) = 0)
    (hsimple : ∀ j, fderiv ℂ F (y₁, t j) (0, 1) ≠ 0) :
    ∃ (U : Set (Fin n → ℂ)) (φ : Fin d → (Fin n → ℂ) → ℂ),
      IsOpen U ∧ y₁ ∈ U ∧
      (∀ j, AnalyticOn ℂ (φ j) U) ∧
      (∀ j, φ j y₁ = t j) ∧
      (∀ j, ∀ y ∈ U, F (y, φ j y) = 0) ∧
      (∀ i j, i ≠ j → ∀ y ∈ U, φ i y ≠ φ j y) := by
  choose U φ ε hUopen hy₁U hφan hφval _hεpos hφroot _hφuniq using
    fun j => analytic_root_section_complex F y₁ (t j) (hF_an j) (hroot j) (hsimple j)
  -- continuity of each section at `y₁`
  have hcont : ∀ j, ContinuousAt (φ j) y₁ := fun j =>
    (hφan j).continuousOn.continuousAt ((hUopen j).mem_nhds (hy₁U j))
  -- pairwise disjointness holds on a neighborhood of `y₁`
  have hdisj_nhds : ∀ᶠ y in 𝓝 y₁, ∀ p : Fin d × Fin d, p.1 ≠ p.2 → φ p.1 y ≠ φ p.2 y := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun y hne => absurd hp hne
    · have hval : φ p.1 y₁ - φ p.2 y₁ ≠ 0 := by
        rw [hφval p.1, hφval p.2, sub_ne_zero]
        exact fun h => hp (ht_inj h)
      have hne := ((hcont p.1).sub (hcont p.2)).eventually_ne hval
      filter_upwards [hne] with y hy _
      exact sub_ne_zero.mp hy
  -- shrink to a ball inside every `U j` and the disjointness locus
  have hUall_nhds : (⋂ j, U j) ∈ 𝓝 y₁ :=
    (Filter.iInter_mem.mpr fun j => (hUopen j).mem_nhds (hy₁U j))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hUall_nhds hdisj_nhds)
  refine ⟨Metric.ball y₁ r, φ, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_, hφval, ?_, ?_⟩
  · intro j
    exact (hφan j).mono fun y hy => Set.mem_iInter.mp (hball hy).1 j
  · intro j y hy
    exact hφroot j y (Set.mem_iInter.mp (hball hy).1 j)
  · intro i j hij y hy
    exact (hball hy).2 (i, j) hij

/-! ### The fiber: a monic separable complex polynomial has `d` distinct simple roots -/

/-- **Distinct simple roots of a separable polynomial.** A monic *separable* complex polynomial of
degree `d` has exactly `d` distinct roots, enumerated injectively by `t : Fin d → ℂ`, whose set is
all roots, and each root is **simple** (`f'` does not vanish there). This is the fiber structure of
the branched root-covering over the discriminant-nonzero locus (where `f = H(y,0)` is separable). -/
theorem separable_distinct_simple_roots (f : Polynomial ℂ) (d : ℕ)
    (hmonic : f.Monic) (hdeg : f.natDegree = d) (hsep : f.Separable) :
    ∃ t : Fin d → ℂ, Function.Injective t ∧
      (∀ β, f.IsRoot β ↔ ∃ j, t j = β) ∧
      (∀ j, (derivative f).eval (t j) ≠ 0) := by
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hsplits : f.Splits := IsAlgClosed.splits f
  have hcard : f.roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      (splits_iff_card_roots.mp hsplits), hdeg]
  -- enumerate the `d` distinct roots
  set s := f.roots.toFinset with hs
  let e : Fin d ≃ s := (finCongr hcard.symm).trans s.equivFin.symm
  -- each `e j` is a root of `f`
  have hej_root : ∀ j, f.IsRoot (e j : ℂ) :=
    fun j => (mem_roots'.mp (Multiset.mem_toFinset.mp (e j).2)).2
  refine ⟨fun j => (e j : ℂ), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro β
    constructor
    · intro hβ
      have hmem : β ∈ s := Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hf0, hβ⟩)
      exact ⟨e.symm ⟨β, hmem⟩, by simp [Equiv.apply_symm_apply]⟩
    · rintro ⟨j, rfl⟩
      exact hej_root j
  · intro j
    have hroot : f.eval₂ (RingHom.id ℂ) (e j : ℂ) = 0 := by
      simpa [eval₂_id] using hej_root j
    simpa [eval₂_id] using hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) hroot

/-! ### Topology of the root projection: continuity, finite & bounded fibers, properness

For a family `q : (Fin n → ℂ) → ℂ[X]` of monic polynomials of constant degree `d` with continuous
coefficients, the projection from the *root variety* to the base is a proper (hence closed) map with
finite fibers. These are the standard-topology obligations of the Mathlib covering-map constructor
`IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph`. -/

section Covering

variable {d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
  (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
  (hcont : ∀ i, Continuous (fun y => (q y).coeff i))

/-- The root variety of the family `q`: pairs `(y, t)` with `t` a root of `q y`. -/
def rootVariety : Set ((Fin n → ℂ) × ℂ) := {p | (q p.1).eval p.2 = 0}

include hdeg hcont in
/-- The family evaluation `(y, t) ↦ (q y).eval t` is jointly continuous. -/
theorem evalFamily_continuous : Continuous (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2) := by
  have heval : (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2)
      = fun p => ∑ i ∈ Finset.range (d + 1), (q p.1).coeff i * p.2 ^ i := by
    funext p
    rw [eval_eq_sum_range' (n := d + 1) (by rw [hdeg]; omega)]
  rw [heval]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((hcont i).comp continuous_fst).mul (continuous_snd.pow i)

include hdeg hcont in
/-- The root variety is closed in `(Fin n → ℂ) × ℂ`. -/
theorem rootVariety_isClosed : IsClosed (rootVariety q) :=
  isClosed_eq (evalFamily_continuous q hdeg hcont) continuous_const

include hdeg in
/-- The family evaluation is jointly **analytic** at any point where the coefficients are analytic. -/
theorem evalFamily_analyticAt {y₀ : Fin n → ℂ} (t₀ : ℂ)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) y₀) :
    AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2) (y₀, t₀) := by
  have heval : (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2)
      = fun p => ∑ i ∈ Finset.range (d + 1), (q p.1).coeff i * p.2 ^ i := by
    funext p
    rw [eval_eq_sum_range' (n := d + 1) (by rw [hdeg]; omega)]
  rw [heval]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((hcoeff i).comp_of_eq analyticAt_fst rfl).mul (analyticAt_snd.pow i)

include hdeg in
/-- The partial derivative `∂F/∂t` of the family evaluation equals `(q y₀)'.eval t₀` — the bridge
between the analytic IFT hypothesis and the polynomial simple-root condition. -/
theorem evalFamily_fderiv_t {y₀ : Fin n → ℂ} (t₀ : ℂ)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) y₀) :
    fderiv ℂ (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2) (y₀, t₀) (0, 1)
      = (derivative (q y₀)).eval t₀ := by
  set F : (Fin n → ℂ) × ℂ → ℂ := fun p => (q p.1).eval p.2 with hF
  set c := (derivative (q y₀)).eval t₀ with hc
  have hF_diff : DifferentiableAt ℂ F (y₀, t₀) :=
    (evalFamily_analyticAt q hdeg t₀ hcoeff).differentiableAt
  have hderiv : HasDerivAt (fun t => F (y₀, t)) c t₀ := (q y₀).hasDerivAt t₀
  have hι : DifferentiableAt ℂ (fun t : ℂ => ((y₀ : Fin n → ℂ), t)) t₀ :=
    (differentiableAt_const _).prodMk differentiableAt_id
  have hfk : fderiv ℂ (fun t => F (y₀, t)) t₀ 1 = c := by
    rw [hderiv.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
  have hchain : fderiv ℂ (fun t => F (y₀, t)) t₀
      = (fderiv ℂ F (y₀, t₀)).comp (fderiv ℂ (fun t : ℂ => ((y₀ : Fin n → ℂ), t)) t₀) :=
    (hF_diff.hasFDerivAt.comp t₀ hι.hasFDerivAt).fderiv
  have hι_1 : fderiv ℂ (fun t : ℂ => ((y₀ : Fin n → ℂ), t)) t₀ 1 = (0, 1) := by
    have hfd : HasFDerivAt (fun t : ℂ => ((y₀ : Fin n → ℂ), t))
        ((0 : ℂ →L[ℂ] (Fin n → ℂ)).prod (ContinuousLinearMap.id ℂ ℂ)) t₀ :=
      (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id t₀)
    rw [hfd.fderiv]; simp
  calc fderiv ℂ F (y₀, t₀) (0, 1)
      = fderiv ℂ F (y₀, t₀) (fderiv ℂ (fun t : ℂ => ((y₀ : Fin n → ℂ), t)) t₀ 1) := by rw [hι_1]
    _ = ((fderiv ℂ F (y₀, t₀)).comp
          (fderiv ℂ (fun t : ℂ => ((y₀ : Fin n → ℂ), t)) t₀)) 1 := rfl
    _ = fderiv ℂ (fun t => F (y₀, t)) t₀ 1 := by rw [← hchain]
    _ = c := hfk

include hmonic in
/-- Each fiber `{t | (q y).eval t = 0}` of the projection is finite (roots of a nonzero poly). -/
theorem fiber_root_finite (y : Fin n → ℂ) : {t : ℂ | (q y).eval t = 0}.Finite :=
  Polynomial.finite_setOf_isRoot (hmonic y).ne_zero

include hmonic hdeg hcont in
/-- Over a compact base set `K`, the slice of the root variety is compact: it is closed (the variety
is closed) and bounded — every root of `q y` is bounded by the Cauchy bound, dominated by the
continuous sum `∑ᵢ ‖coeffᵢ‖ + 1`, which attains a maximum on the compact `K`. -/
theorem rootVariety_slice_isCompact {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    IsCompact (rootVariety q ∩ K ×ˢ Set.univ) := by
  have hclosed : IsClosed (rootVariety q ∩ K ×ˢ Set.univ) :=
    (rootVariety_isClosed q hdeg hcont).inter (hK.isClosed.prod isClosed_univ)
  -- a continuous coefficient-sum bound, maximised over `K`
  set B : (Fin n → ℂ) → ℝ := fun y => (∑ i ∈ Finset.range d, ‖(q y).coeff i‖) + 1 with hB
  have hB_cont : Continuous B := by
    refine (continuous_finset_sum _ fun i _ => ?_).add continuous_const
    exact (continuous_norm.comp (hcont i))
  obtain ⟨Rmax, hRmax⟩ : ∃ Rmax, ∀ y ∈ K, B y ≤ Rmax := by
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨0, by simp⟩
    · obtain ⟨y₀, _, hmax⟩ := hK.exists_isMaxOn hKne hB_cont.continuousOn
      exact ⟨B y₀, fun y hy => hmax hy⟩
  -- Cauchy bound dominated by `B`, giving a uniform root bound on `K`
  have hroot_bound : ∀ y ∈ K, ∀ t : ℂ, (q y).eval t = 0 → ‖t‖ ≤ Rmax := by
    intro y hyK t hroot
    have hcb : ‖t‖₊ < Polynomial.cauchyBound (q y) :=
      Polynomial.IsRoot.norm_lt_cauchyBound (hmonic y).ne_zero hroot
    have hdom : (Polynomial.cauchyBound (q y) : ℝ) ≤ B y := by
      have hsup : Finset.sup (Finset.range d) (fun i => ‖(q y).coeff i‖₊)
          ≤ ∑ i ∈ Finset.range d, ‖(q y).coeff i‖₊ :=
        Finset.sup_le fun i hi =>
          Finset.single_le_sum (f := fun k => ‖(q y).coeff k‖₊) (fun j _ => zero_le _) hi
      have hsupℝ : (↑(Finset.sup (Finset.range d) (fun i => ‖(q y).coeff i‖₊)) : ℝ)
          ≤ ∑ i ∈ Finset.range d, ‖(q y).coeff i‖ := by
        have h := NNReal.coe_le_coe.mpr hsup
        rw [NNReal.coe_sum] at h
        simpa using h
      rw [Polynomial.cauchyBound, hmonic y, hdeg y, hB]
      simp only [nnnorm_one, div_one, NNReal.coe_add, NNReal.coe_one]
      linarith
    calc ‖t‖ = (‖t‖₊ : ℝ) := rfl
      _ ≤ (Polynomial.cauchyBound (q y) : ℝ) := le_of_lt (by exact_mod_cast hcb)
      _ ≤ B y := hdom
      _ ≤ Rmax := hRmax y hyK
  -- closed + bounded ⟹ compact in the finite-dimensional ambient space
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  apply (hK.isBounded.prod (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Rmax))).subset
  rintro ⟨y, t⟩ ⟨hroot, hyK, -⟩
  exact ⟨hyK, by rw [Metric.mem_closedBall, dist_zero_right]; exact hroot_bound y hyK t hroot⟩

/-- The projection `π : rootVariety q → base` from the root variety to the base. -/
def rootProj : ↥(rootVariety q) → (Fin n → ℂ) := fun e => (e : (Fin n → ℂ) × ℂ).1

include hmonic hdeg hcont in
/-- **The root projection is a proper map.** Preimages of compact sets are the compact slices
`rootVariety_slice_isCompact`. -/
theorem rootProj_isProperMap : IsProperMap (rootProj q) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_fst.comp continuous_subtype_val, fun K hK => ?_⟩
  have himg : Subtype.val '' (rootProj q ⁻¹' K) = rootVariety q ∩ K ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true, rootProj]
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨e.2, he⟩
    · rintro ⟨hp, hpK⟩; exact ⟨⟨p, hp⟩, hpK, rfl⟩
  rw [(Topology.IsInducing.subtypeVal (t := rootVariety q)).isCompact_iff, himg]
  exact rootVariety_slice_isCompact q hmonic hdeg hcont hK

include hmonic hdeg hcont in
/-- **The root projection is a closed map** (it is proper). The closed-map property is the remaining
standard-topology obligation of the Mathlib covering-map constructor. -/
theorem rootProj_isClosedMap : IsClosedMap (rootProj q) :=
  (rootProj_isProperMap q hmonic hdeg hcont).isClosedMap

include hdeg in
/-- **Local trivialization of the root projection.** At a *simple* root `t₀` of `q y₀` (with analytic
coefficients near `y₀`), the projection `rootProj` restricts to an `OpenPartialHomeomorph` whose source
is an open "tube" around the point `(y₀, t₀)` of the root variety and whose inverse is the holomorphic
root section. This is the final analytic obligation of the Mathlib covering-map constructor
`IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph`. -/
theorem rootProj_openPartialHomeomorph {y₀ : Fin n → ℂ} (t₀ : ℂ)
    (hroot₀ : (q y₀).eval t₀ = 0)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) y₀)
    (hsimple : (derivative (q y₀)).eval t₀ ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph ↥(rootVariety q) (Fin n → ℂ),
      (⟨(y₀, t₀), hroot₀⟩ : ↥(rootVariety q)) ∈ Φ.source ∧
        (⇑Φ : ↥(rootVariety q) → (Fin n → ℂ)) = rootProj q := by
  classical
  have hF_an : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2) (y₀, t₀) :=
    evalFamily_analyticAt q hdeg t₀ hcoeff
  have hsimple' : fderiv ℂ (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2) (y₀, t₀) (0, 1) ≠ 0 := by
    rw [evalFamily_fderiv_t q hdeg t₀ hcoeff]; exact hsimple
  obtain ⟨U, φ, ε, hU_open, hy₀U, hφ_an, hφ_val, hε, hφ_root, hφ_uniq⟩ :=
    analytic_root_section_complex (fun p => (q p.1).eval p.2) y₀ t₀ hF_an hroot₀ hsimple'
  have hφ_cont : ContinuousOn φ U := hφ_an.continuousOn
  -- shrunken base `U₁` where the section stays within `ε` of `t₀`
  set U₁ : Set (Fin n → ℂ) := {y | y ∈ U ∧ dist (φ y) t₀ < ε} with hU₁
  have hU₁_open : IsOpen U₁ := by
    have hrw : U₁ = U ∩ φ ⁻¹' Metric.ball t₀ ε := by
      ext y; simp only [hU₁, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Metric.mem_ball]
    rw [hrw]; exact hφ_cont.isOpen_inter_preimage hU_open Metric.isOpen_ball
  have hy₀U₁ : y₀ ∈ U₁ := ⟨hy₀U, by rw [hφ_val, dist_self]; exact hε⟩
  have hU₁U : U₁ ⊆ U := fun y hy => hy.1
  have hroot_on : ∀ y ∈ U₁, (q y).eval (φ y) = 0 := fun y hy => hφ_root y (hU₁U hy)
  -- the section into the root variety (total, correct on `U₁`)
  set invF : (Fin n → ℂ) → ↥(rootVariety q) :=
    fun y => if h : (q y).eval (φ y) = 0 then ⟨(y, φ y), h⟩ else ⟨(y₀, t₀), hroot₀⟩ with hinvF
  have hinvF_eq : ∀ y ∈ U₁, (invF y : (Fin n → ℂ) × ℂ) = (y, φ y) := by
    intro y hy; rw [hinvF]; simp only [dif_pos (hroot_on y hy)]
  -- the open tube source, on which uniqueness forces points onto the section graph
  set src : Set ↥(rootVariety q) :=
    {x | (x : (Fin n → ℂ) × ℂ).1 ∈ U₁ ∧ dist (x : (Fin n → ℂ) × ℂ).2 t₀ < ε} with hsrc
  have hgraph : ∀ x : ↥(rootVariety q), x ∈ src →
      (x : (Fin n → ℂ) × ℂ) = ((x : (Fin n → ℂ) × ℂ).1, φ (x : (Fin n → ℂ) × ℂ).1) := by
    intro x hx
    have hxroot : (fun p : (Fin n → ℂ) × ℂ => (q p.1).eval p.2) (x : (Fin n → ℂ) × ℂ) = 0 := x.2
    have := hφ_uniq (x : (Fin n → ℂ) × ℂ).1 (hU₁U hx.1) (x : (Fin n → ℂ) × ℂ).2 hxroot hx.2
    exact Prod.ext rfl this
  -- assemble the partial equivalence
  refine ⟨{
    toFun := rootProj q
    invFun := invF
    source := src
    target := U₁
    map_source' := fun x hx => hx.1
    map_target' := fun y hy => by
      refine ⟨?_, ?_⟩
      · rw [hinvF_eq y hy]; exact hy
      · rw [hinvF_eq y hy]; exact hy.2
    left_inv' := fun x hx => by
      apply Subtype.ext
      show (invF ((x : (Fin n → ℂ) × ℂ).1) : (Fin n → ℂ) × ℂ) = (x : (Fin n → ℂ) × ℂ)
      rw [hinvF_eq _ hx.1]
      exact (hgraph x hx).symm
    right_inv' := fun y hy => by
      show (invF y : (Fin n → ℂ) × ℂ).1 = y
      rw [hinvF_eq y hy]
    open_source := ?_
    open_target := hU₁_open
    continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
    continuousOn_invFun := ?_ }, ?_, rfl⟩
  · -- `src` is open: preimage of the open tube `U₁ ×ˢ ball t₀ ε` under `Subtype.val`
    have hrw : src = Subtype.val ⁻¹' (U₁ ×ˢ Metric.ball t₀ ε) := by
      ext x; simp only [hsrc, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Metric.mem_ball]
    rw [hrw]
    exact (hU₁_open.prod Metric.isOpen_ball).preimage continuous_subtype_val
  · -- continuity of the inverse section on `U₁`
    rw [(Topology.IsInducing.subtypeVal (t := rootVariety q)).continuousOn_iff]
    refine ContinuousOn.congr (f := fun y => ((y : Fin n → ℂ), φ y)) ?_ ?_
    · exact continuousOn_id.prodMk (hφ_cont.mono hU₁U)
    · intro y hy; exact hinvF_eq y hy
  · -- the base point lies in the source
    exact ⟨hy₀U₁, by show dist t₀ t₀ < ε; rw [dist_self]; exact hε⟩

include hmonic hdeg hcont in
/-- **The root projection is a covering map over the separable locus.** On the set `s` of base points
`y` where `q y` is separable (equivalently `disc(q y) ≠ 0`), with analytic coefficients, the projection
`rootProj` is a covering map: the four obligations of `IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph`
are the closed-map property `rootProj_isClosedMap`, finite fibers `fiber_root_finite`, and the local
trivializations `rootProj_openPartialHomeomorph` (each root over `s` is simple by separability). -/
theorem rootProj_isCoveringMapOn
    (s : Set (Fin n → ℂ))
    (han : ∀ i, ∀ y ∈ s, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hs : ∀ y ∈ s, (q y).Separable) :
    IsCoveringMapOn (rootProj q) s := by
  apply (rootProj_isClosedMap q hmonic hdeg hcont).isCoveringMapOn_of_openPartialHomeomorph
  · -- finite fibers: inject into the finite root set `{t | (q y).eval t = 0}`
    intro y _
    apply Set.Finite.of_finite_image (f := fun e : ↥(rootVariety q) => (e : (Fin n → ℂ) × ℂ).2)
    · apply (fiber_root_finite q hmonic y).subset
      rintro _ ⟨e, he, rfl⟩
      have hey : (e : (Fin n → ℂ) × ℂ).1 = y := he
      show (q y).eval (e : (Fin n → ℂ) × ℂ).2 = 0
      rw [← hey]; exact e.2
    · intro e he e' he' heq
      apply Subtype.ext
      exact Prod.ext ((he : (e : (Fin n → ℂ) × ℂ).1 = y).trans
        (he' : (e' : (Fin n → ℂ) × ℂ).1 = y).symm) heq
  · -- local trivialization at each point over `s` (every root over `s` is simple)
    intro e he
    have hys : (e : (Fin n → ℂ) × ℂ).1 ∈ s := he
    have hsep : (q (e : (Fin n → ℂ) × ℂ).1).Separable := hs _ hys
    have hroot : (q (e : (Fin n → ℂ) × ℂ).1).eval (e : (Fin n → ℂ) × ℂ).2 = 0 := e.2
    have hsimple : (derivative (q (e : (Fin n → ℂ) × ℂ).1)).eval (e : (Fin n → ℂ) × ℂ).2 ≠ 0 := by
      have hroot₂ : (q (e : (Fin n → ℂ) × ℂ).1).eval₂ (RingHom.id ℂ) (e : (Fin n → ℂ) × ℂ).2 = 0 := by
        rw [eval₂_id]; exact hroot
      have hd := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) hroot₂
      rwa [eval₂_id] at hd
    obtain ⟨Φ, hmem, hcoe⟩ := rootProj_openPartialHomeomorph q hdeg (e : (Fin n → ℂ) × ℂ).2 e.2
      (fun i => han i _ hys) hsimple
    exact ⟨Φ, hmem, hcoe⟩

include hmonic hdeg hcont in
/-- **The restricted root projection over the separable locus is a covering map.** Packaged as a
`IsCoveringMap` on the subtypes via `IsCoveringMapOn.isCoveringMap_restrictPreimage`. -/
theorem rootProj_isCoveringMap_restrict
    (s : Set (Fin n → ℂ))
    (han : ∀ i, ∀ y ∈ s, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hs : ∀ y ∈ s, (q y).Separable) :
    IsCoveringMap (s.restrictPreimage (rootProj q)) :=
  (rootProj_isCoveringMapOn q hmonic hdeg hcont s han hs).isCoveringMap_restrictPreimage

end Covering

end
