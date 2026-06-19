import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Cad.Multivariate.ProjectionTheorem.DiscrProdInvariant
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Simple roots are delineable (Theorem: `simple_roots_delineable`)

This file proves `simple_roots_delineable` by decomposing it into axioms and theorems:

## Axioms

1. **`ift_local_root_section`**: At a simple root, the implicit function theorem
   gives a local analytic root function on a neighborhood.

2. **`separable_locally_delineable`**: At each point where `f` is separable, `f` is
   analytically delineable on a neighborhood. Combines IFT (axiom 1) with the root
   continuity principle (the number of real roots is locally constant when separable).

3. **`locally_delineable_to_global`**: On a connected open set, local delineability
   at every point patches to global delineability.

## Theorems

- **`root_continuity_delineable`**: Separable on connected open ⟹ delineable.
  Proved from axioms 2 + 3.

- **`orderFull_eq_one_of_simple_root`**: At a simple root `(a, y)`, the full
  vanishing order `orderFull f a y = 1`.

- **`order_invariant_section_of_mult_one`**: On a section of simple roots,
  `OrderInvariantFull f (SectionGraph θ S)` holds (all values are 1).

- **`simple_roots_delineable'`**: Full theorem combining delineability + order invariance.

## References

- Krantz & Parks, *The Implicit Function Theorem*, Chapter 6.
- McCallum (1985), §3.3 — proof of the lifting theorem.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-! ### Generic analytic implicit function theorem for a scalar equation -/

/-- **Analytic IFT for a scalar equation** (generic root section).

If `F : (ℝⁿ × ℝ) → ℝ` is analytic at `(y₀, t₀)`, `F(y₀, t₀) = 0`, and the partial derivative
`∂F/∂t` at `(y₀, t₀)` (i.e. `fderiv F (y₀,t₀) (0,1)`) is nonzero, then `F(y, t) = 0` has a unique
local analytic solution `t = φ(y)`: there are a neighborhood `U ∋ y₀`, an analytic `φ` with
`φ(y₀) = t₀`, and `ε > 0` such that `F(y, φ y) = 0` on `U`, and `φ(y)` is the unique root within
`ε` of `t₀`.

`ift_local_root_section` is the special case `F(y, t) = (specialize f y).eval t`. The proof is the
analytic inverse function theorem applied to `G(y,t) = (y, F(y,t))`. -/
theorem analytic_root_section
    (F : (Fin n → ℝ) × ℝ → ℝ) (y₀ : Fin n → ℝ) (t₀ : ℝ)
    (hF_an : AnalyticAt ℝ F (y₀, t₀))
    (hroot : F (y₀, t₀) = 0)
    (hsimple : fderiv ℝ F (y₀, t₀) (0, 1) ≠ 0) :
    ∃ (U : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) (ε : ℝ),
      IsOpen U ∧ y₀ ∈ U ∧
      AnalyticOn ℝ φ U ∧
      φ y₀ = t₀ ∧
      0 < ε ∧
      (∀ y ∈ U, F (y, φ y) = 0) ∧
      (∀ y ∈ U, ∀ t, F (y, t) = 0 → |t - t₀| < ε → t = φ y) := by
  let Ep := (Fin n → ℝ) × ℝ
  let G : Ep → Ep := fun p => (p.1, F p)
  set c := fderiv ℝ F (y₀, t₀) (0, 1) with hc_def
  have hc_ne : c ≠ 0 := hsimple
  have hF_diff : DifferentiableAt ℝ F (y₀, t₀) := hF_an.differentiableAt
  have hF_partial : ∀ k : ℝ, fderiv ℝ F (y₀, t₀) (0, k) = c * k := by
    intro k
    have hk : ((0 : Fin n → ℝ), k) = k • ((0 : Fin n → ℝ), (1 : ℝ)) := by
      ext i <;> simp
    rw [hk, map_smul, ← hc_def, smul_eq_mul, mul_comm]
  have hG_an : AnalyticAt ℝ G (y₀, t₀) := analyticAt_fst.prod hF_an
  have hG_fderiv_eq : fderiv ℝ G (y₀, t₀) =
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ).prod (fderiv ℝ F (y₀, t₀)) := by
    show fderiv ℝ (fun x : Ep => (x.1, F x)) (y₀, t₀) = _
    rw [DifferentiableAt.fderiv_prodMk differentiableAt_fst hF_diff, fderiv_fst]
  have hDG_val : ∀ u : Ep, fderiv ℝ G (y₀, t₀) u = (u.1, fderiv ℝ F (y₀, t₀) u) := by
    intro u; rw [hG_fderiv_eq]; rfl
  have hDG_bij : Function.Bijective (fderiv ℝ G (y₀, t₀)) := by
    constructor
    · intro v w hvw
      rw [hDG_val v, hDG_val w] at hvw
      have h1 : v.1 = w.1 := (Prod.mk.inj hvw).1
      have h2 : fderiv ℝ F (y₀, t₀) v = fderiv ℝ F (y₀, t₀) w := (Prod.mk.inj hvw).2
      have h3 : fderiv ℝ F (y₀, t₀) (0, v.2 - w.2) = 0 := by
        rw [show ((0 : Fin n → ℝ), v.2 - w.2) = v - w from
          Prod.ext (sub_eq_zero.mpr h1).symm rfl, map_sub, sub_eq_zero.mpr h2]
      rw [hF_partial] at h3
      exact Prod.ext h1 (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc_ne))
    · intro ⟨v, w⟩
      refine ⟨(v, (w - fderiv ℝ F (y₀, t₀) (v, 0)) / c), ?_⟩
      rw [hDG_val]; exact Prod.ext rfl (by
        show fderiv ℝ F (y₀, t₀) (v, (w - fderiv ℝ F (y₀, t₀) (v, 0)) / c) = w
        rw [show (v, (w - fderiv ℝ F (y₀, t₀) (v, 0)) / c) =
          ((v : Fin n → ℝ), (0 : ℝ)) + ((0 : Fin n → ℝ),
            (w - fderiv ℝ F (y₀, t₀) (v, 0)) / c) from Prod.ext (by simp) (by simp),
          map_add, hF_partial]
        field_simp; linarith)
  let i : Ep ≃L[ℝ] Ep :=
    (LinearEquiv.ofBijective (fderiv ℝ G (y₀, t₀)).toLinearMap hDG_bij).toContinuousLinearEquiv
  have hi : fderiv ℝ G (y₀, t₀) = i.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun _ => rfl
  have hG_strict : HasStrictFDerivAt G (i : Ep →L[ℝ] Ep) (y₀, t₀) :=
    hi ▸ hG_an.hasStrictFDerivAt
  let R := hG_strict.toOpenPartialHomeomorph G
  have hR_source : (y₀, t₀) ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hG_val : G (y₀, t₀) = (y₀, (0 : ℝ)) := Prod.ext rfl hroot
  have hR_target_mem : (y₀, (0 : ℝ)) ∈ R.target := by
    have : G (y₀, t₀) ∈ R.target := R.map_source hR_source
    rwa [hG_val] at this
  have hR_an_symm : AnalyticAt ℝ R.symm (y₀, (0 : ℝ)) := by
    have : AnalyticAt ℝ R.symm (G (y₀, t₀)) := R.analyticAt_symm' hR_source hG_an hi
    rwa [hG_val] at this
  obtain ⟨r_an, hr_an_pos, hR_ball_an⟩ := hR_an_symm.exists_ball_analyticOnNhd
  obtain ⟨δ_a, δ_y, hδ_a, hδ_y, hball_src⟩ : ∃ δ_a δ_y : ℝ, 0 < δ_a ∧ 0 < δ_y ∧
      Metric.ball y₀ δ_a ×ˢ Metric.ball t₀ δ_y ⊆ R.source := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp R.open_source (y₀, t₀) hR_source
    exact ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, fun ⟨a, y⟩ ⟨ha, hy⟩ => hball (
      max_lt (lt_trans (Metric.mem_ball.mp ha) (half_lt_self hδ))
             (lt_trans (Metric.mem_ball.mp hy) (half_lt_self hδ)))⟩
  obtain ⟨δ_ta, δ_t0, hδ_ta, hδ_t0, hball_tgt⟩ : ∃ δ_ta δ_t0 : ℝ, 0 < δ_ta ∧ 0 < δ_t0 ∧
      Metric.ball y₀ δ_ta ×ˢ Metric.ball (0 : ℝ) δ_t0 ⊆ R.target := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp R.open_target (y₀, 0) hR_target_mem
    exact ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, fun ⟨a, y⟩ ⟨ha, hy⟩ => hball (
      max_lt (lt_trans (Metric.mem_ball.mp ha) (half_lt_self hδ))
             (lt_trans (Metric.mem_ball.mp hy) (half_lt_self hδ)))⟩
  let φ₀ : (Fin n → ℝ) → ℝ := fun a => (R.symm (a, 0)).2
  let U₀ := Metric.ball y₀ (min (min δ_ta δ_a) r_an)
  have hφ₀_val : φ₀ y₀ = t₀ := by
    show (R.symm (y₀, 0)).2 = t₀
    have h : R.symm (G (y₀, t₀)) = (y₀, t₀) := R.left_inv hR_source
    rw [hG_val] at h; exact congrArg Prod.snd h
  have hφ₀_root : ∀ a, (a, (0 : ℝ)) ∈ R.target → F (a, φ₀ a) = 0 := by
    intro a hmem
    have hright : G (R.symm (a, 0)) = (a, 0) := R.right_inv hmem
    have h1 : (R.symm (a, 0)).1 = a := congrArg Prod.fst hright
    have h2 : F (R.symm (a, 0)) = 0 := congrArg Prod.snd hright
    show F (a, (R.symm (a, 0)).2) = 0
    rw [show (a, (R.symm (a, 0)).2) = R.symm (a, 0) from Prod.ext h1.symm rfl]; exact h2
  have hφ₀_an : AnalyticOn ℝ φ₀ U₀ := by
    intro a ha
    have ha_r : dist a y₀ < r_an :=
      lt_of_lt_of_le (Metric.mem_ball.mp ha) (min_le_right _ _)
    have hR_an_local : AnalyticAt ℝ R.symm (a, (0 : ℝ)) := by
      apply hR_ball_an; rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt ha_r (by rw [dist_self]; exact hr_an_pos)
    have hpair : AnalyticAt ℝ (fun x : Fin n → ℝ => (x, (0 : ℝ))) a :=
      (analyticAt_id (𝕜 := ℝ)).prod analyticAt_const
    exact (analyticAt_snd.comp (hR_an_local.comp_of_eq' hpair rfl)).analyticWithinAt
  have hφ₀_unique : ∀ a ∈ U₀, ∀ y, F (a, y) = 0 →
      |y - t₀| < δ_y → y = φ₀ a := by
    intro a ha y hy_root hy_close
    have ha_ball : a ∈ Metric.ball y₀ δ_a :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (lt_of_lt_of_le (Metric.mem_ball.mp ha)
        (min_le_left _ _)) (min_le_right _ _))
    have hy_ball : y ∈ Metric.ball t₀ δ_y := Metric.mem_ball.mpr (by rwa [Real.dist_eq])
    have ha_source : (a, y) ∈ R.source := hball_src ⟨ha_ball, hy_ball⟩
    have hGay : G (a, y) = (a, (0 : ℝ)) := Prod.ext rfl hy_root
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

/-! ### Axiom 1: Implicit Function Theorem for polynomial roots -/

/-- **Theorem** (IFT for simple polynomial roots).

If `f(a₀, y₀) = 0` and `f'(a₀, y₀) ≠ 0` (i.e., `y₀` is a simple root of `f(a₀, ·)`),
then there exist a neighborhood `U` of `a₀`, an analytic function `φ : U → ℝ` with
`φ(a₀) = y₀`, and `ε > 0` such that `φ(a)` is a root of `f(a, ·)` for all `a ∈ U`,
and `φ` is the unique root of `f(a, ·)` within distance `ε` of `y₀`.

This follows from the analytic IFT applied to the analytic function
`(a, y) ↦ f(a, y)` at the regular point `(a₀, y₀)`. -/
theorem ift_local_root_section
    (f : PolyR n)
    (a₀ : Fin n → ℝ)
    (y₀ : ℝ)
    (hroot : (specialize f a₀).IsRoot y₀)
    (hsimple : (specialize (Polynomial.derivative f) a₀).eval y₀ ≠ 0) :
    ∃ (U : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) (ε : ℝ),
      IsOpen U ∧ a₀ ∈ U ∧
      AnalyticOn ℝ φ U ∧
      φ a₀ = y₀ ∧
      0 < ε ∧
      (∀ a ∈ U, (specialize f a).IsRoot (φ a)) ∧
      (∀ a ∈ U, ∀ y, (specialize f a).IsRoot y → |y - y₀| < ε → y = φ a) := by
  -- Step 1: Define evaluation F(a,y) = (specialize f a).eval y and G(a,y) = (a, F(a,y))
  let Ep := (Fin n → ℝ) × ℝ
  let F : Ep → ℝ := fun p => (specialize f p.1).eval p.2
  let G : Ep → Ep := fun p => (p.1, F p)
  set c := (Polynomial.derivative (specialize f a₀)).eval y₀ with hc_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def, show Polynomial.derivative (specialize f a₀) = specialize (Polynomial.derivative f) a₀
      from by simp [specialize, Polynomial.derivative_map]]
    exact hsimple
  -- Step 2: F is analytic at (a₀, y₀) — via toMvPoly and Fin.cons composition
  have hF_mv : ∀ a y, F (a, y) = MvPolynomial.eval (Fin.cons y a) (toMvPoly f) := by
    intro a y; show (specialize f a).eval y = MvPolynomial.eval (Fin.cons y a) (toMvPoly f)
    unfold toMvPoly specialize
    rw [MvPolynomial.eval_eq_eval_mv_eval',
      (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply f]
  have hF_an : AnalyticAt ℝ F (a₀, y₀) := by
    suffices h : AnalyticAt ℝ (fun p : Ep => MvPolynomial.eval
        (fun i : Fin (n + 1) => Fin.cons p.2 p.1 i) (toMvPoly f)) (a₀, y₀) by
      exact h.congr (Filter.Eventually.of_forall fun p => (hF_mv p.1 p.2).symm)
    have hcons : AnalyticAt ℝ (fun p : Ep => fun i : Fin (n + 1) =>
        (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ) i) (a₀, y₀) := by
      apply AnalyticAt.pi; intro i; refine Fin.cases ?_ (fun j => ?_) i
      · change AnalyticAt ℝ (fun p : (Fin n → ℝ) × ℝ => p.2) (a₀, y₀)
        exact analyticAt_snd
      · change AnalyticAt ℝ (fun p : (Fin n → ℝ) × ℝ => p.1 j) (a₀, y₀)
        exact (analyticAt_pi_iff.mp analyticAt_fst) j
    have heval : AnalyticAt ℝ (fun v : Fin (n + 1) → ℝ =>
        MvPolynomial.eval v (toMvPoly f)) (Fin.cons y₀ a₀) :=
      AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (toMvPoly f) _ (Set.mem_univ _)
    exact heval.comp_of_eq' hcons rfl
  -- Step 3: G is analytic at (a₀, y₀)
  have hG_an : AnalyticAt ℝ G (a₀, y₀) := analyticAt_fst.prod hF_an
  -- Step 4: Partial derivative of F w.r.t. y equals c
  have hF_diff : DifferentiableAt ℝ F (a₀, y₀) := hF_an.differentiableAt
  have hF_partial : ∀ k : ℝ, fderiv ℝ F (a₀, y₀) (0, k) = c * k := by
    intro k
    have hderiv : HasDerivAt (fun y => F (a₀, y)) c y₀ :=
      (specialize f a₀).hasDerivAt y₀
    have hι : DifferentiableAt ℝ (fun y : ℝ => ((a₀ : Fin n → ℝ), y)) y₀ :=
      DifferentiableAt.prodMk (differentiableAt_const a₀) differentiableAt_id
    have hfk : fderiv ℝ (fun y => F (a₀, y)) y₀ k = c * k := by
      rw [hderiv.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, mul_comm]
    have hchain : fderiv ℝ (fun y => F (a₀, y)) y₀ =
        (fderiv ℝ F (a₀, y₀)).comp (fderiv ℝ (fun y : ℝ => ((a₀ : Fin n → ℝ), y)) y₀) :=
      (hF_diff.hasFDerivAt.comp y₀ hι.hasFDerivAt).fderiv
    have hι_k : fderiv ℝ (fun y : ℝ => ((a₀ : Fin n → ℝ), y)) y₀ k = (0, k) := by
      have hfd : HasFDerivAt (fun y : ℝ => ((a₀ : Fin n → ℝ), y))
          ((0 : ℝ →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)) y₀ :=
        HasFDerivAt.prodMk (hasFDerivAt_const a₀ y₀) (hasFDerivAt_id y₀)
      rw [hfd.fderiv]; simp
    calc fderiv ℝ F (a₀, y₀) (0, k)
        = fderiv ℝ F (a₀, y₀) (fderiv ℝ (fun y : ℝ => ((a₀ : Fin n → ℝ), y)) y₀ k) := by
            rw [hι_k]
      _ = ((fderiv ℝ F (a₀, y₀)).comp
              (fderiv ℝ (fun y : ℝ => ((a₀ : Fin n → ℝ), y)) y₀)) k := rfl
      _ = fderiv ℝ (fun y => F (a₀, y)) y₀ k := by rw [← hchain]
      _ = c * k := hfk
  -- Step 5: fderiv of G at (a₀, y₀) is bijective
  have hG_fderiv_eq : fderiv ℝ G (a₀, y₀) =
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ).prod (fderiv ℝ F (a₀, y₀)) := by
    show fderiv ℝ (fun x : Ep => (x.1, F x)) (a₀, y₀) = _
    rw [DifferentiableAt.fderiv_prodMk differentiableAt_fst hF_diff, fderiv_fst]
  have hDG_val : ∀ u : Ep, fderiv ℝ G (a₀, y₀) u = (u.1, fderiv ℝ F (a₀, y₀) u) := by
    intro u; rw [hG_fderiv_eq]; rfl
  have hDG_bij : Function.Bijective (fderiv ℝ G (a₀, y₀)) := by
    constructor
    · -- Injective
      intro v w hvw
      rw [hDG_val v, hDG_val w] at hvw
      have h1 : v.1 = w.1 := (Prod.mk.inj hvw).1
      have h2 : fderiv ℝ F (a₀, y₀) v = fderiv ℝ F (a₀, y₀) w := (Prod.mk.inj hvw).2
      have h3 : fderiv ℝ F (a₀, y₀) (0, v.2 - w.2) = 0 := by
        rw [show ((0 : Fin n → ℝ), v.2 - w.2) = v - w from
          Prod.ext (sub_eq_zero.mpr h1).symm rfl, map_sub, sub_eq_zero.mpr h2]
      rw [hF_partial] at h3
      exact Prod.ext h1 (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc_ne))
    · -- Surjective
      intro ⟨v, w⟩
      refine ⟨(v, (w - fderiv ℝ F (a₀, y₀) (v, 0)) / c), ?_⟩
      rw [hDG_val]; exact Prod.ext rfl (by
        show fderiv ℝ F (a₀, y₀) (v, (w - fderiv ℝ F (a₀, y₀) (v, 0)) / c) = w
        rw [show (v, (w - fderiv ℝ F (a₀, y₀) (v, 0)) / c) =
          ((v : Fin n → ℝ), (0 : ℝ)) + ((0 : Fin n → ℝ),
            (w - fderiv ℝ F (a₀, y₀) (v, 0)) / c) from Prod.ext (by simp) (by simp),
          map_add, hF_partial]
        field_simp; linarith)
  -- Step 6: Get ContinuousLinearEquiv from bijective fderiv
  let i : Ep ≃L[ℝ] Ep :=
    (LinearEquiv.ofBijective (fderiv ℝ G (a₀, y₀)).toLinearMap hDG_bij).toContinuousLinearEquiv
  have hi : fderiv ℝ G (a₀, y₀) = i.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun _ => rfl
  -- Step 7: Build OpenPartialHomeomorph from analytic IFT
  have hG_strict : HasStrictFDerivAt G (i : Ep →L[ℝ] Ep) (a₀, y₀) :=
    hi ▸ hG_an.hasStrictFDerivAt
  let R := hG_strict.toOpenPartialHomeomorph G
  have hR_source : (a₀, y₀) ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  -- Step 8: G(a₀, y₀) = (a₀, 0) since y₀ is a root
  have hG_val : G (a₀, y₀) = (a₀, (0 : ℝ)) := Prod.ext rfl hroot
  -- Step 9: Analyticity of R.symm at (a₀, 0)
  have hR_target_mem : (a₀, (0 : ℝ)) ∈ R.target := by
    have : G (a₀, y₀) ∈ R.target := R.map_source hR_source
    rwa [hG_val] at this
  have hR_an_symm : AnalyticAt ℝ R.symm (a₀, (0 : ℝ)) := by
    have : AnalyticAt ℝ R.symm (G (a₀, y₀)) := R.analyticAt_symm' hR_source hG_an hi
    rwa [hG_val] at this
  -- Step 10: Extract analyticity ball for R.symm
  obtain ⟨r_an, hr_an_pos, hR_ball_an⟩ := hR_an_symm.exists_ball_analyticOnNhd
  -- Step 11: Extract product balls from R.source and R.target
  obtain ⟨δ_a, δ_y, hδ_a, hδ_y, hball_src⟩ : ∃ δ_a δ_y : ℝ, 0 < δ_a ∧ 0 < δ_y ∧
      Metric.ball a₀ δ_a ×ˢ Metric.ball y₀ δ_y ⊆ R.source := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp R.open_source (a₀, y₀) hR_source
    exact ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, fun ⟨a, y⟩ ⟨ha, hy⟩ => hball (
      max_lt (lt_trans (Metric.mem_ball.mp ha) (half_lt_self hδ))
             (lt_trans (Metric.mem_ball.mp hy) (half_lt_self hδ)))⟩
  obtain ⟨δ_ta, δ_t0, hδ_ta, hδ_t0, hball_tgt⟩ : ∃ δ_ta δ_t0 : ℝ, 0 < δ_ta ∧ 0 < δ_t0 ∧
      Metric.ball a₀ δ_ta ×ˢ Metric.ball (0 : ℝ) δ_t0 ⊆ R.target := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp R.open_target (a₀, 0) hR_target_mem
    exact ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, fun ⟨a, y⟩ ⟨ha, hy⟩ => hball (
      max_lt (lt_trans (Metric.mem_ball.mp ha) (half_lt_self hδ))
             (lt_trans (Metric.mem_ball.mp hy) (half_lt_self hδ)))⟩
  -- Step 12: Define φ and U
  let φ₀ : (Fin n → ℝ) → ℝ := fun a => (R.symm (a, 0)).2
  let U₀ := Metric.ball a₀ (min (min δ_ta δ_a) r_an)
  -- Step 13: φ₀(a₀) = y₀
  have hφ₀_val : φ₀ a₀ = y₀ := by
    show (R.symm (a₀, 0)).2 = y₀
    have h : R.symm (G (a₀, y₀)) = (a₀, y₀) := R.left_inv hR_source
    rw [hG_val] at h; exact congrArg Prod.snd h
  -- Step 14: Root property — G(R.symm(a, 0)) = (a, 0) gives F(a, φ₀(a)) = 0
  have hφ₀_root : ∀ a, (a, (0 : ℝ)) ∈ R.target → (specialize f a).IsRoot (φ₀ a) := by
    intro a hmem
    have hright : G (R.symm (a, 0)) = (a, 0) := R.right_inv hmem
    have h1 : (R.symm (a, 0)).1 = a := congrArg Prod.fst hright
    have h2 : F (R.symm (a, 0)) = 0 := congrArg Prod.snd hright
    show (specialize f a).eval (R.symm (a, 0)).2 = 0
    change (specialize f (R.symm (a, 0)).1).eval (R.symm (a, 0)).2 = 0 at h2
    rwa [h1] at h2
  -- Step 15: φ₀ is analytic on U₀
  have hφ₀_an : AnalyticOn ℝ φ₀ U₀ := by
    intro a ha
    have ha_r : dist a a₀ < r_an :=
      lt_of_lt_of_le (Metric.mem_ball.mp ha) (min_le_right _ _)
    have hR_an_local : AnalyticAt ℝ R.symm (a, (0 : ℝ)) := by
      apply hR_ball_an; rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt ha_r (by rw [dist_self]; exact hr_an_pos)
    have hpair : AnalyticAt ℝ (fun x : Fin n → ℝ => (x, (0 : ℝ))) a :=
      (analyticAt_id (𝕜 := ℝ)).prod analyticAt_const
    exact (analyticAt_snd.comp (hR_an_local.comp_of_eq' hpair rfl)).analyticWithinAt
  -- Step 16: Uniqueness — if (a, y) ∈ R.source and F(a,y)=0, then y = φ₀(a)
  have hφ₀_unique : ∀ a ∈ U₀, ∀ y, (specialize f a).IsRoot y →
      |y - y₀| < δ_y → y = φ₀ a := by
    intro a ha y hy_root hy_close
    have ha_ball : a ∈ Metric.ball a₀ δ_a :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (lt_of_lt_of_le (Metric.mem_ball.mp ha)
        (min_le_left _ _)) (min_le_right _ _))
    have hy_ball : y ∈ Metric.ball y₀ δ_y := Metric.mem_ball.mpr (by rwa [Real.dist_eq])
    have ha_source : (a, y) ∈ R.source := hball_src ⟨ha_ball, hy_ball⟩
    have hGay : G (a, y) = (a, (0 : ℝ)) := Prod.ext rfl hy_root
    show y = (R.symm (a, 0)).2
    have hinv : R.symm (G (a, y)) = (a, y) := R.left_inv ha_source
    rw [hGay] at hinv; exact (congrArg Prod.snd hinv).symm
  -- Step 17: Assemble the result
  exact ⟨U₀, φ₀, δ_y, Metric.isOpen_ball,
    Metric.mem_ball_self (lt_min (lt_min hδ_ta hδ_a) hr_an_pos),
    hφ₀_an, hφ₀_val, hδ_y,
    fun a ha => hφ₀_root a (hball_tgt ⟨Metric.mem_ball.mpr (lt_of_lt_of_le
      (lt_of_lt_of_le (Metric.mem_ball.mp ha) (min_le_left _ _)) (min_le_left _ _)),
      Metric.mem_ball_self hδ_t0⟩),
    hφ₀_unique⟩

/-! ### Analytic families of polynomials -/

/-- Joint analyticity of the evaluation of an analytic family of polynomials.
If the coefficients of `fam y` are analytic at `y₀` and `deg (fam y) ≤ N` near `y₀`, then
`(y, t) ↦ (fam y).eval t` is analytic at `(y₀, t₀)`. -/
theorem fam_eval_analyticAt {s : ℕ} (fam : (Fin s → ℝ) → Polynomial ℝ) (N : ℕ)
    (y₀ : Fin s → ℝ) (t₀ : ℝ)
    (hdeg : ∀ᶠ y in nhds y₀, (fam y).natDegree ≤ N)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun y => (fam y).coeff i) y₀) :
    AnalyticAt ℝ (fun p : (Fin s → ℝ) × ℝ => (fam p.1).eval p.2) (y₀, t₀) := by
  have hsum_an : AnalyticAt ℝ
      (fun p : (Fin s → ℝ) × ℝ => ∑ i ∈ Finset.range (N + 1), (fam p.1).coeff i * p.2 ^ i)
      (y₀, t₀) := by
    apply Finset.analyticAt_fun_sum
    intro i _
    have hc : AnalyticAt ℝ (fun p : (Fin s → ℝ) × ℝ => (fam p.1).coeff i) (y₀, t₀) :=
      (hcoeff i).comp_of_eq analyticAt_fst rfl
    exact hc.mul (analyticAt_snd.pow i)
  refine hsum_an.congr ?_
  have htend : Filter.Tendsto (Prod.fst : (Fin s → ℝ) × ℝ → (Fin s → ℝ))
      (nhds (y₀, t₀)) (nhds y₀) := continuousAt_fst
  have hdeg' : ∀ᶠ p : (Fin s → ℝ) × ℝ in nhds (y₀, t₀), (fam p.1).natDegree ≤ N :=
    htend.eventually hdeg
  filter_upwards [hdeg'] with p hp
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) p.2).symm

/-- The `t`-partial derivative of the evaluation of an analytic family equals the evaluation of
the derivative polynomial: `∂ₜ[(fam y).eval t] = (fam y₀)'.eval t₀` at `(y₀, t₀)`. -/
theorem fam_eval_fderiv_t {s : ℕ} (fam : (Fin s → ℝ) → Polynomial ℝ) (y₀ : Fin s → ℝ) (t₀ : ℝ)
    (hH_diff : DifferentiableAt ℝ (fun p : (Fin s → ℝ) × ℝ => (fam p.1).eval p.2) (y₀, t₀)) :
    fderiv ℝ (fun p : (Fin s → ℝ) × ℝ => (fam p.1).eval p.2) (y₀, t₀) (0, 1)
      = (Polynomial.derivative (fam y₀)).eval t₀ := by
  set H : (Fin s → ℝ) × ℝ → ℝ := fun p => (fam p.1).eval p.2 with hH_def
  set c := (Polynomial.derivative (fam y₀)).eval t₀ with hc_def
  have hderiv : HasDerivAt (fun t => H (y₀, t)) c t₀ := (fam y₀).hasDerivAt t₀
  have hι : DifferentiableAt ℝ (fun t : ℝ => ((y₀ : Fin s → ℝ), t)) t₀ :=
    DifferentiableAt.prodMk (differentiableAt_const y₀) differentiableAt_id
  have hchain : fderiv ℝ (fun t => H (y₀, t)) t₀ =
      (fderiv ℝ H (y₀, t₀)).comp (fderiv ℝ (fun t : ℝ => ((y₀ : Fin s → ℝ), t)) t₀) :=
    (hH_diff.hasFDerivAt.comp t₀ hι.hasFDerivAt).fderiv
  have hι_1 : fderiv ℝ (fun t : ℝ => ((y₀ : Fin s → ℝ), t)) t₀ 1 = (0, 1) := by
    have hfd : HasFDerivAt (fun t : ℝ => ((y₀ : Fin s → ℝ), t))
        ((0 : ℝ →L[ℝ] (Fin s → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)) t₀ :=
      HasFDerivAt.prodMk (hasFDerivAt_const y₀ t₀) (hasFDerivAt_id t₀)
    rw [hfd.fderiv]; simp
  have hc1 : fderiv ℝ (fun t => H (y₀, t)) t₀ 1 = c := by
    rw [hderiv.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
  calc fderiv ℝ H (y₀, t₀) (0, 1)
      = fderiv ℝ H (y₀, t₀) (fderiv ℝ (fun t : ℝ => ((y₀ : Fin s → ℝ), t)) t₀ 1) := by rw [hι_1]
    _ = ((fderiv ℝ H (y₀, t₀)).comp
          (fderiv ℝ (fun t : ℝ => ((y₀ : Fin s → ℝ), t)) t₀)) 1 := rfl
    _ = fderiv ℝ (fun t => H (y₀, t)) t₀ 1 := by rw [← hchain]
    _ = c := hc1

/-- The evaluation of an analytic family is continuous on `W ×ˢ univ` for some open `W ∋ y₀`
(where the coefficients are analytic and the degree is `≤ d`). -/
theorem fam_eval_continuousOn {s : ℕ} (fam : (Fin s → ℝ) → Polynomial ℝ) (y₀ : Fin s → ℝ) (d : ℕ)
    (hdeg : ∀ᶠ y in nhds y₀, (fam y).natDegree ≤ d)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun y => (fam y).coeff i) y₀) :
    ∃ W : Set (Fin s → ℝ), IsOpen W ∧ y₀ ∈ W ∧
      ContinuousOn (fun p : (Fin s → ℝ) × ℝ => (fam p.1).eval p.2) (W ×ˢ Set.univ) := by
  have hcoeff_nbhd : ∀ i, ∃ W : Set (Fin s → ℝ), IsOpen W ∧ y₀ ∈ W ∧
      ContinuousOn (fun y => (fam y).coeff i) W := fun i => by
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := eventually_nhds_iff.mp (hcoeff i).eventually_analyticAt
    exact ⟨W, hW_open, hW_mem, fun y hy => (hW_sub y hy).continuousAt.continuousWithinAt⟩
  choose Wc hWc_open hWc_mem hWc_cont using hcoeff_nbhd
  obtain ⟨Wd, hWd_sub, hWd_open, hWd_mem⟩ := eventually_nhds_iff.mp hdeg
  refine ⟨Wd ∩ ⋂ i ∈ Finset.range (d + 1), Wc i,
    hWd_open.inter (isOpen_biInter_finset fun i _ => hWc_open i),
    ⟨hWd_mem, Set.mem_iInter₂.mpr fun i _ => hWc_mem i⟩, ?_⟩
  have hsum_cont : ContinuousOn
      (fun p : (Fin s → ℝ) × ℝ => ∑ i ∈ Finset.range (d + 1), (fam p.1).coeff i * p.2 ^ i)
      ((Wd ∩ ⋂ i ∈ Finset.range (d + 1), Wc i) ×ˢ Set.univ) := by
    apply continuousOn_finset_sum
    intro i hi
    apply ContinuousOn.mul _ (continuous_snd.continuousOn.pow i)
    exact (hWc_cont i).comp continuous_fst.continuousOn
      (fun p hp => (Set.mem_iInter₂.mp hp.1.2) i hi)
  exact hsum_cont.congr fun p hp =>
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hWd_sub p.1 hp.1.1)) p.2

/-- **Separable analytic family is locally delineable.**
If the family `fam : ℝˢ → ℝ[t]` has analytic coefficients, constant positive degree near `y₀`, and
`fam y₀` is separable, then on a neighborhood `V` of `y₀` its roots are given by finitely many
analytic functions, strictly ordered, with multiplicity `1`. This is the analytic-family analogue
of `separable_locally_delineable`, built on `analytic_root_section`, `fam_eval_analyticAt`,
`fam_eval_fderiv_t`, `fam_eval_continuousOn`. -/
theorem separable_family_locally_delineable {s : ℕ}
    (fam : (Fin s → ℝ) → Polynomial ℝ)
    (y₀ : Fin s → ℝ)
    (hdeg : ∀ᶠ y in nhds y₀, (fam y).natDegree = (fam y₀).natDegree)
    (hpos : 0 < (fam y₀).natDegree)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun y => (fam y).coeff i) y₀)
    (hsep : (fam y₀).Separable) :
    ∃ (V : Set (Fin s → ℝ)), IsOpen V ∧ y₀ ∈ V ∧
      ∃ (k : ℕ) (η : Fin k → (Fin s → ℝ) → ℝ) (mult : Fin k → ℕ),
        (∀ i, AnalyticOn ℝ (η i) V) ∧
        (∀ y ∈ V, ∀ i j : Fin k, i < j → η i y < η j y) ∧
        (∀ y ∈ V, ∀ α : ℝ, (fam y).IsRoot α ↔ ∃ i : Fin k, α = η i y) ∧
        (∀ i, 0 < mult i) ∧
        (∀ y ∈ V, ∀ i, (fam y).rootMultiplicity (η i y) = mult i) := by
  set d := (fam y₀).natDegree with hd_def
  set H : (Fin s → ℝ) × ℝ → ℝ := fun p => (fam p.1).eval p.2 with hH_def
  have hdeg_le : ∀ᶠ y in nhds y₀, (fam y).natDegree ≤ d := hdeg.mono fun y h => h.le
  set p := fam y₀ with hp_def
  have hp_sep : p.Separable := hsep
  have hp_ne : p ≠ 0 := hp_sep.ne_zero
  set k := p.roots.toFinset.card with hk_def
  let yiso := p.roots.toFinset.orderIsoOfFin rfl
  let yr : Fin k → ℝ := fun i => ↑(yiso i)
  have hyr_root : ∀ i, p.IsRoot (yr i) := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (yiso i).2)
  have hyr_sorted : StrictMono yr := fun _ _ h => yiso.strictMono h
  have hyr_complete : ∀ z, p.IsRoot z → ∃ i : Fin k, z = yr i := by
    intro z hz
    obtain ⟨i, hi⟩ := yiso.surjective
      ⟨z, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp_ne).mpr hz)⟩
    exact ⟨i, (congr_arg Subtype.val hi).symm⟩
  have hyr_mult : ∀ i, p.rootMultiplicity (yr i) = 1 := fun i => by
    have := Polynomial.rootMultiplicity_le_one_of_separable hp_sep (yr i)
    have := (Polynomial.rootMultiplicity_pos hp_ne).mpr (hyr_root i)
    omega
  have hder_spec : ∀ i, (Polynomial.derivative p).eval (yr i) ≠ 0 := by
    intro i h
    linarith [(Polynomial.one_lt_rootMultiplicity_iff_isRoot hp_ne).mpr ⟨hyr_root i, h⟩,
      hyr_mult i]
  -- IFT at each simple root
  have hift : ∀ i, ∃ (U : Set (Fin s → ℝ)) (φ : (Fin s → ℝ) → ℝ) (ε : ℝ),
      IsOpen U ∧ y₀ ∈ U ∧ AnalyticOn ℝ φ U ∧ φ y₀ = yr i ∧ 0 < ε ∧
      (∀ y ∈ U, (fam y).IsRoot (φ y)) ∧
      (∀ y ∈ U, ∀ t, (fam y).IsRoot t → |t - yr i| < ε → t = φ y) := fun i => by
    have hH_an : AnalyticAt ℝ H (y₀, yr i) := fam_eval_analyticAt fam d y₀ (yr i) hdeg_le hcoeff
    have hsimple' : fderiv ℝ H (y₀, yr i) (0, 1) ≠ 0 := by
      rw [fam_eval_fderiv_t fam y₀ (yr i) hH_an.differentiableAt]; exact hder_spec i
    exact analytic_root_section H y₀ (yr i) hH_an (hyr_root i) hsimple'
  choose Ui φ ε hUi_open ha₀_Ui hφ_an hφ_val hε_pos hφ_root hφ_unique using hift
  have hφ_cont : ∀ i, ContinuousAt (φ i) y₀ := fun i =>
    (hφ_an i).continuousOn.continuousAt ((hUi_open i).mem_nhds (ha₀_Ui i))
  -- (a) all IFT sections defined
  have h_ift : ∀ᶠ a in nhds y₀, a ∈ ⋂ i, Ui i :=
    (isOpen_iInter_of_finite fun i => hUi_open i).mem_nhds (Set.mem_iInter.mpr ha₀_Ui)
  -- (b) ordering preserved
  have h_ord : ∀ᶠ a in nhds y₀, ∀ i j : Fin k, i < j → φ i a < φ j a := by
    simp only [Filter.eventually_all]
    intro i j hij
    exact (((hφ_cont j).sub (hφ_cont i)).eventually
      (Ioi_mem_nhds (sub_pos.mpr (by
        show φ i y₀ < φ j y₀; rw [hφ_val i, hφ_val j]; exact hyr_sorted hij)))).mono
      fun _ h => sub_pos.mp h
  -- (c) no extra roots
  have h_roots : ∀ᶠ a in nhds y₀, ∀ z, (fam a).IsRoot z → ∃ i : Fin k, z = φ i a := by
    obtain ⟨W, hW_open, hW_mem, hW_cont⟩ := fam_eval_continuousOn fam y₀ d hdeg_le hcoeff
    let iftBall (i : Fin k) := Set.Ioo (yr i - ε i) (yr i + ε i)
    have hyr_in_ball : ∀ i, yr i ∈ iftBall i := fun i =>
      Set.mem_Ioo.mpr ⟨by linarith [hε_pos i], by linarith [hε_pos i]⟩
    let coeffSum := ∑ i ∈ Finset.range d, |p.coeff i|
    let lcAbs := |p.leadingCoeff|
    set R := max (coeffSum / lcAbs + 2)
        (if h : k = 0 then 1 else (Finset.univ.sup'
          ⟨⟨0, Nat.pos_of_ne_zero h⟩, Finset.mem_univ _⟩
          (fun i : Fin k => |yr i| + ε i)) + 1) with hR_def
    have hR_pos : (0 : ℝ) < R := lt_max_of_lt_left (by positivity)
    have hyr_in_R : ∀ i, |yr i| < R := by
      intro i
      have hk_ne : k ≠ 0 := by have := i.isLt; omega
      apply lt_of_lt_of_le _ (le_max_right _ _)
      rw [dif_neg hk_ne]
      have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
        ⟨⟨0, Nat.pos_of_ne_zero hk_ne⟩, Finset.mem_univ _⟩
      calc |yr i| < |yr i| + ε i := by linarith [hε_pos i]
        _ ≤ Finset.univ.sup' hne (fun j : Fin k => |yr j| + ε j) :=
            Finset.le_sup' (fun j : Fin k => |yr j| + ε j) (Finset.mem_univ i)
        _ < _ + 1 := by linarith
    set K := Set.Icc (-R) R \ ⋃ i, iftBall i
    have hK_compact : IsCompact K :=
      (isCompact_Icc).diff (isOpen_iUnion fun i => isOpen_Ioo)
    have hK_no_root : ∀ y ∈ K, ¬ p.IsRoot y := by
      intro y ⟨_, hy_not⟩ hroot
      obtain ⟨i, rfl⟩ := hyr_complete y hroot
      exact hy_not (Set.mem_iUnion.mpr ⟨i, hyr_in_ball i⟩)
    -- open set in W ×ˢ univ where H ≠ 0
    have hopen_ne : IsOpen ((W ×ˢ Set.univ) ∩ H ⁻¹' {x | x ≠ 0}) :=
      hW_cont.isOpen_inter_preimage (hW_open.prod isOpen_univ) isOpen_ne
    have hprod_sub : {y₀} ×ˢ K ⊆ (W ×ˢ Set.univ) ∩ H ⁻¹' {x | x ≠ 0} := by
      intro ⟨a, y⟩ ⟨ha, hy⟩
      simp only [Set.mem_singleton_iff] at ha; subst ha
      exact ⟨⟨hW_mem, Set.mem_univ _⟩, hK_no_root y hy⟩
    have h_tube : ∀ᶠ a in nhds y₀, ∀ y ∈ K, (fam a).eval y ≠ 0 := by
      rcases Set.eq_empty_or_nonempty K with hKe | hKne
      · exact Filter.Eventually.of_forall fun a y hy =>
          absurd hy (hKe ▸ (Set.mem_empty_iff_false y).mp)
      · obtain ⟨u, v, hu_open, _, ha₀u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton
            hK_compact hopen_ne hprod_sub
        exact Filter.Eventually.mono (hu_open.mem_nhds (Set.singleton_subset_iff.mp ha₀u))
          fun a ha y hy => (huv (Set.mk_mem_prod ha (hKv hy))).2
    -- root bound via Cauchy bound, eventually < R
    have h_bound : ∀ᶠ a in nhds y₀,
        ∀ z, (fam a).IsRoot z → z ∈ Set.Ioo (-R) R := by
      have hlc_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
      have hlc_eq : (fam y₀).coeff d = p.leadingCoeff := rfl
      let gbnd : (Fin s → ℝ) → ℝ := fun a =>
        (∑ i ∈ Finset.range d, |(fam a).coeff i|) / |(fam a).coeff d| + 1
      have hg_cont : ContinuousAt gbnd y₀ := by
        apply ContinuousAt.add _ continuousAt_const
        apply ContinuousAt.div
        · exact tendsto_finset_sum _ fun i _ => (hcoeff i).continuousAt.abs
        · exact (hcoeff d).continuousAt.abs
        · rw [hlc_eq]; exact abs_ne_zero.mpr hlc_ne
      have hg_val : gbnd y₀ = coeffSum / lcAbs + 1 := by
        show (∑ i ∈ Finset.range d, |(fam y₀).coeff i|) / |(fam y₀).coeff d| + 1 = _
        rw [hlc_eq]
      have hg_lt_R : coeffSum / lcAbs + 1 < R := by
        have : coeffSum / lcAbs + 2 ≤ R := le_max_left _ _
        linarith
      have hg_ev : ∀ᶠ a in nhds y₀, gbnd a < R :=
        hg_cont.eventually (gt_mem_nhds (hg_val ▸ hg_lt_R))
      have hlc_ne' : (fam y₀).coeff d ≠ 0 := by rw [hlc_eq]; exact hlc_ne
      have h_lc_ev : ∀ᶠ a in nhds y₀, (fam a).coeff d ≠ 0 :=
        (hcoeff d).continuousAt.eventually (isOpen_ne.mem_nhds hlc_ne')
      filter_upwards [hg_ev, h_lc_ev, hdeg] with a hga ha_lc ha_deg z hroot
      have hfa_ne : fam a ≠ 0 := fun h => ha_lc (by rw [h]; simp)
      have hcb := hroot.norm_lt_cauchyBound hfa_ne
      have hd_eq : (fam a).natDegree = d := ha_deg
      have hcb_le : (Polynomial.cauchyBound (fam a) : ℝ) ≤ gbnd a := by
        have hcb_nn : Polynomial.cauchyBound (fam a) ≤
            (∑ i ∈ Finset.range d, ‖(fam a).coeff i‖₊) / ‖(fam a).leadingCoeff‖₊ + 1 := by
          simp only [Polynomial.cauchyBound, hd_eq]
          gcongr
          exact Finset.sup_le fun i hi =>
            Finset.single_le_sum (f := fun i => ‖(fam a).coeff i‖₊) (fun _ _ => zero_le _) hi
        calc (↑(Polynomial.cauchyBound (fam a)) : ℝ)
            ≤ ↑((∑ i ∈ Finset.range d, ‖(fam a).coeff i‖₊) /
                ‖(fam a).leadingCoeff‖₊ + 1) := by exact_mod_cast hcb_nn
          _ = gbnd a := by
              simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
              have hlc : (↑‖(fam a).leadingCoeff‖₊ : ℝ) = |(fam a).coeff d| := by
                have hlc' : (fam a).leadingCoeff = (fam a).coeff d := by
                  show (fam a).coeff (fam a).natDegree = (fam a).coeff d; rw [hd_eq]
                rw [hlc', coe_nnnorm, Real.norm_eq_abs]
              have hnum : (∑ i ∈ Finset.range d, (↑‖(fam a).coeff i‖₊ : ℝ)) =
                  ∑ i ∈ Finset.range d, |(fam a).coeff i| :=
                Finset.sum_congr rfl fun i _ => by rw [coe_nnnorm, Real.norm_eq_abs]
              show (∑ i ∈ Finset.range d, (↑‖(fam a).coeff i‖₊ : ℝ)) /
                  ↑‖(fam a).leadingCoeff‖₊ + 1
                = (∑ i ∈ Finset.range d, |(fam a).coeff i|) / |(fam a).coeff d| + 1
              rw [hnum, hlc]
      have hz_lt : |z| < R := calc
        |z| = ↑‖z‖₊ := by simp [coe_nnnorm, Real.norm_eq_abs]
        _ < ↑(Polynomial.cauchyBound (fam a)) := by exact_mod_cast hcb
        _ ≤ gbnd a := hcb_le
        _ < R := hga
      exact Set.mem_Ioo.mpr (abs_lt.mp hz_lt)
    exact (h_ift.and (h_tube.and h_bound)).mono fun a ⟨ha_ift, ha_tube, ha_bound⟩ z hroot => by
      have hz_R := ha_bound z hroot
      have hz_Icc : z ∈ Set.Icc (-R) R := Set.Ioo_subset_Icc_self hz_R
      have hz_not_K : z ∉ K := fun hzK => ha_tube z hzK hroot
      have hz_ball : ∃ i, z ∈ iftBall i := by
        by_contra h; push_neg at h
        exact hz_not_K ⟨hz_Icc, fun hmem => let ⟨i, hi⟩ := Set.mem_iUnion.mp hmem; h i hi⟩
      obtain ⟨i, hi⟩ := hz_ball
      refine ⟨i, hφ_unique i a (Set.mem_iInter.mp ha_ift i) z hroot ?_⟩
      simp only [iftBall, Set.mem_Ioo] at hi
      rw [abs_sub_lt_iff]; constructor <;> linarith [hi.1, hi.2]
  -- (d) derivative nonzero at each φ i a
  have h_der : ∀ᶠ a in nhds y₀,
      ∀ i, (Polynomial.derivative (fam a)).eval (φ i a) ≠ 0 := by
    simp only [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt
        (fun a => (Polynomial.derivative (fam a)).eval (φ i a)) y₀ := by
      have hdcoeff : ∀ j, AnalyticAt ℝ (fun y => (Polynomial.derivative (fam y)).coeff j) y₀ := by
        intro j
        have heq : (fun y => (Polynomial.derivative (fam y)).coeff j)
            = (fun y => (↑(j + 1) : ℝ) * (fam y).coeff (j + 1)) := by
          funext y; rw [Polynomial.coeff_derivative]; push_cast; ring
        rw [heq]; exact analyticAt_const.mul (hcoeff (j + 1))
      have hddeg : ∀ᶠ y in nhds y₀, (Polynomial.derivative (fam y)).natDegree ≤ d := by
        filter_upwards [hdeg_le] with y h
        calc (Polynomial.derivative (fam y)).natDegree
            ≤ (fam y).natDegree - 1 := Polynomial.natDegree_derivative_le (fam y)
          _ ≤ d := by omega
      obtain ⟨W', hW'_open, hW'_mem, hW'_cont⟩ :=
        fam_eval_continuousOn (fun y => Polynomial.derivative (fam y)) y₀ d hddeg hdcoeff
      have hmap : ContinuousAt (fun a => (a, φ i a)) y₀ := continuousAt_id.prodMk (hφ_cont i)
      exact (hW'_cont.continuousAt
        ((hW'_open.prod isOpen_univ).mem_nhds ⟨hW'_mem, Set.mem_univ _⟩)).comp hmap
    exact hcont.eventually (isOpen_ne.mem_nhds (show
        (Polynomial.derivative (fam y₀)).eval (φ i y₀) ≠ 0 by
      rw [hφ_val i]; exact hder_spec i))
  obtain ⟨V, hV_sub, hV_open, ha₀_V⟩ :=
    mem_nhds_iff.mp (h_ift.and (h_ord.and (h_roots.and h_der)))
  refine ⟨V, hV_open, ha₀_V, k, φ, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hφ_an i).mono fun a ha => Set.mem_iInter.mp (hV_sub ha).1 i
  · intro a haV i j hij; exact (hV_sub haV).2.1 i j hij
  · intro a haV z
    exact ⟨(hV_sub haV).2.2.1 z, fun ⟨i, hi⟩ => hi ▸ hφ_root i a (Set.mem_iInter.mp (hV_sub haV).1 i)⟩
  · intro _; exact Nat.one_pos
  · intro a haV i
    have ha_Ui : a ∈ Ui i := Set.mem_iInter.mp (hV_sub haV).1 i
    have hroot_a := hφ_root i a ha_Ui
    have hder_ne_a := (hV_sub haV).2.2.2 i
    have hfa_ne : fam a ≠ 0 := by
      intro h
      have := (hV_sub haV).2.2.2 i
      rw [h] at this; simp at this
    have hle : ¬ 1 < (fam a).rootMultiplicity (φ i a) := by
      rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hfa_ne]
      push_neg; intro _; rwa [Polynomial.IsRoot]
    have hge := (Polynomial.rootMultiplicity_pos hfa_ne).mpr hroot_a
    show (fam a).rootMultiplicity (φ i a) = 1
    omega

/-! ### Theorem 2: Separable implies locally delineable -/

/-- **Theorem** (Separable local delineability).

At each point `a₀` of an open set where `f(a₀, ·)` is separable (coprime with its
derivative), `f` is analytically delineable on some neighborhood `S ∩ U`.

**Proof outline:**
1. Extract the `k` sorted simple roots `y₁ < ⋯ < yₖ` of `f(a₀, ·)`.
2. Apply `ift_local_root_section` at each root to get analytic sections `φᵢ`.
3. Shrink the neighborhood so that ordering `φ₁(a) < ⋯ < φₖ(a)` is preserved
   (by continuity), the derivative doesn't vanish at each `φᵢ(a)` (so multiplicities
   stay 1), and no new roots appear (compactness + root bound argument). -/
theorem separable_locally_delineable
    (f : PolyR n)
    (a₀ : Fin n → ℝ)
    (S : Set (Fin n → ℝ))
    (ha₀ : a₀ ∈ S)
    (hdeg : DegreeInvariant f S)
    (hsep : IsCoprime (specialize f a₀) (Polynomial.derivative (specialize f a₀))) :
    ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ a₀ ∈ U ∧ AnalyticDelineable f (S ∩ U) := by
  -- Step 1: f(a₀, ·) is separable with sorted simple roots
  set p := specialize f a₀ with hp_def
  have hp_sep : p.Separable := hsep
  have hp_ne : p ≠ 0 := hp_sep.ne_zero
  set k := p.roots.toFinset.card with hk_def
  let yiso := p.roots.toFinset.orderIsoOfFin rfl
  let yr : Fin k → ℝ := fun i => ↑(yiso i)
  have hyr_root : ∀ i, p.IsRoot (yr i) := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (yiso i).2)
  have hyr_sorted : StrictMono yr := fun _ _ h => yiso.strictMono h
  have hyr_complete : ∀ z, p.IsRoot z → ∃ i : Fin k, z = yr i := by
    intro z hz
    obtain ⟨i, hi⟩ := yiso.surjective
      ⟨z, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp_ne).mpr hz)⟩
    exact ⟨i, (congr_arg Subtype.val hi).symm⟩
  have hyr_mult : ∀ i, p.rootMultiplicity (yr i) = 1 := fun i => by
    have := Polynomial.rootMultiplicity_le_one_of_separable hp_sep (yr i)
    have := (Polynomial.rootMultiplicity_pos hp_ne).mpr (hyr_root i)
    omega
  -- Step 2: Apply IFT at each simple root
  have hder_spec : ∀ i, (specialize (Polynomial.derivative f) a₀).eval (yr i) ≠ 0 := by
    intro i h
    rw [show specialize (Polynomial.derivative f) a₀ = Polynomial.derivative p from
      by simp [hp_def, specialize, Polynomial.derivative_map]] at h
    linarith [(Polynomial.one_lt_rootMultiplicity_iff_isRoot hp_ne).mpr ⟨hyr_root i, h⟩,
      hyr_mult i]
  choose Ui φ ε hUi_open ha₀_Ui hφ_an hφ_val hε_pos hφ_root hφ_unique using
    fun i => ift_local_root_section f a₀ (yr i) (hyr_root i) (hder_spec i)
  -- Continuity of IFT sections at a₀
  have hφ_cont : ∀ i, ContinuousAt (φ i) a₀ := fun i =>
    (hφ_an i).continuousOn.continuousAt ((hUi_open i).mem_nhds (ha₀_Ui i))
  -- Step 3: Find neighborhood where all constraints hold
  -- (a) All IFT sections are defined
  have h_ift : ∀ᶠ a in nhds a₀, a ∈ ⋂ i, Ui i :=
    (isOpen_iInter_of_finite fun i => hUi_open i).mem_nhds (Set.mem_iInter.mpr ha₀_Ui)
  -- (b) Ordering preserved: φ i a < φ j a for i < j
  have h_ord : ∀ᶠ a in nhds a₀, ∀ i j : Fin k, i < j → φ i a < φ j a := by
    simp only [Filter.eventually_all]
    intro i j hij
    exact (((hφ_cont j).sub (hφ_cont i)).eventually
      (Ioi_mem_nhds (sub_pos.mpr (by
        show φ i a₀ < φ j a₀; rw [hφ_val i, hφ_val j]; exact hyr_sorted hij)))).mono
      fun _ h => sub_pos.mp h
  -- (c) No extra roots: every root of f(a, ·) is among φ₁(a), ..., φₖ(a)
  have h_roots : ∀ᶠ a in nhds a₀, a ∈ S →
      ∀ z, (specialize f a).IsRoot z → ∃ i : Fin k, z = φ i a := by
    -- Joint continuity of (a, y) ↦ (specialize f a).eval y
    have hjoint : Continuous (fun (q : (Fin n → ℝ) × ℝ) => (specialize f q.1).eval q.2) := by
      have : (fun q : (Fin n → ℝ) × ℝ => (specialize f q.1).eval q.2) =
          fun q => ∑ i ∈ f.support, MvPolynomial.eval q.1 (f.coeff i) * q.2 ^ i := by
        ext ⟨a, y⟩; simp [specialize, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
          Polynomial.sum_def]
      rw [this]; exact continuous_finset_sum _ fun i _ =>
        ((MvPolynomial.continuous_eval _).comp continuous_fst).mul (continuous_snd.pow i)
    -- IFT uniqueness balls: Ioo (yr i - ε i) (yr i + ε i)
    let iftBall (i : Fin k) := Set.Ioo (yr i - ε i) (yr i + ε i)
    have hyr_in_ball : ∀ i, yr i ∈ iftBall i := fun i =>
      Set.mem_Ioo.mpr ⟨by linarith [hε_pos i], by linarith [hε_pos i]⟩
    -- R: large enough for IFT balls and root bound
    let coeffSum := ∑ i ∈ Finset.range p.natDegree, |p.coeff i|
    let lcAbs := |p.leadingCoeff|
    set R := max (coeffSum / lcAbs + 2)
        (if h : k = 0 then 1 else (Finset.univ.sup'
          ⟨⟨0, Nat.pos_of_ne_zero h⟩, Finset.mem_univ _⟩
          (fun i : Fin k => |yr i| + ε i)) + 1) with hR_def
    have hR_pos : (0 : ℝ) < R := lt_max_of_lt_left (by positivity)
    -- All roots of p are in (-R, R)
    have hyr_in_R : ∀ i, |yr i| < R := by
      intro i
      have hk_ne : k ≠ 0 := by have := i.isLt; omega
      apply lt_of_lt_of_le _ (le_max_right _ _)
      rw [dif_neg hk_ne]
      have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
        ⟨⟨0, Nat.pos_of_ne_zero hk_ne⟩, Finset.mem_univ _⟩
      calc |yr i| < |yr i| + ε i := by linarith [hε_pos i]
        _ ≤ Finset.univ.sup' hne (fun j : Fin k => |yr j| + ε j) :=
            Finset.le_sup' (fun j : Fin k => |yr j| + ε j) (Finset.mem_univ i)
        _ < _ + 1 := by linarith
    -- Compact set K = [-R, R] \ ⋃ iftBall i: has no roots of p
    set K := Set.Icc (-R) R \ ⋃ i, iftBall i
    have hK_compact : IsCompact K :=
      (isCompact_Icc).diff (isOpen_iUnion fun i => isOpen_Ioo)
    have hK_no_root : ∀ y ∈ K, ¬ p.IsRoot y := by
      intro y ⟨_, hy_not⟩ hroot
      obtain ⟨i, rfl⟩ := hyr_complete y hroot
      exact hy_not (Set.mem_iUnion.mpr ⟨i, hyr_in_ball i⟩)
    -- Open set where eval ≠ 0, containing {a₀} × K
    have hopen_ne : IsOpen {q : (Fin n → ℝ) × ℝ | (specialize f q.1).eval q.2 ≠ 0} :=
      hjoint.isOpen_preimage _ (isOpen_compl_singleton)
    have hprod_sub : {a₀} ×ˢ K ⊆ {q | (specialize f q.1).eval q.2 ≠ 0} := by
      intro ⟨a, y⟩ ⟨ha, hy⟩
      simp only [Set.mem_singleton_iff] at ha; subst ha
      exact fun h => hK_no_root y hy h
    -- Tube lemma: open neighborhood of a₀ where f(a, ·) ≠ 0 on K
    have h_tube : ∀ᶠ a in nhds a₀, ∀ y ∈ K, (specialize f a).eval y ≠ 0 := by
      rcases Set.eq_empty_or_nonempty K with hKe | hKne
      · exact Filter.Eventually.of_forall fun a y hy => absurd hy (hKe ▸ (Set.mem_empty_iff_false y).mp)
      · obtain ⟨u, v, hu_open, _, ha₀u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton
            hK_compact hopen_ne hprod_sub
        exact Filter.Eventually.mono (hu_open.mem_nhds (Set.singleton_subset_iff.mp ha₀u))
          fun a ha y hy => huv (Set.mk_mem_prod ha (hKv hy))
    -- Root bound: for a ∈ S near a₀, all roots of specialize f a are in (-R, R)
    have h_bound : ∀ᶠ a in nhds a₀, a ∈ S →
        ∀ z, (specialize f a).IsRoot z → z ∈ Set.Ioo (-R) R := by
      set d := p.natDegree with hd_def
      have hlc_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
      have hcoeff_eq : ∀ i, p.coeff i = MvPolynomial.eval a₀ (f.coeff i) := fun i => by
        simp [hp_def, specialize, Polynomial.coeff_map]
      have hlc_eq : MvPolynomial.eval a₀ (f.coeff d) = p.leadingCoeff := (hcoeff_eq d).symm
      -- g(a) = (∑ |coeff_i(a)|) / |lc(a)| + 1 bounds the Cauchy bound from above
      let g : (Fin n → ℝ) → ℝ := fun a =>
        (∑ i ∈ Finset.range d, |MvPolynomial.eval a (f.coeff i)|) /
          |MvPolynomial.eval a (f.coeff d)| + 1
      have hg_cont : ContinuousAt g a₀ := by
        apply ContinuousAt.add _ continuousAt_const
        apply ContinuousAt.div
        · exact (continuous_finset_sum _ fun i _ =>
            (MvPolynomial.continuous_eval _).abs).continuousAt
        · exact (MvPolynomial.continuous_eval _).continuousAt.abs
        · rw [hlc_eq]; exact abs_ne_zero.mpr hlc_ne
      have hg_val : g a₀ = coeffSum / lcAbs + 1 := by
        show (∑ i ∈ Finset.range d, |MvPolynomial.eval a₀ (f.coeff i)|) /
          |MvPolynomial.eval a₀ (f.coeff d)| + 1 = coeffSum / lcAbs + 1
        congr 1; congr 1
        · exact Finset.sum_congr rfl fun i _ => by rw [← hcoeff_eq]
        · rw [hlc_eq]
      have hg_lt_R : coeffSum / lcAbs + 1 < R := by
        have : coeffSum / lcAbs + 2 ≤ R := le_max_left _ _
        linarith
      -- Eventually g(a) < R
      have hg_ev : ∀ᶠ a in nhds a₀, g a < R :=
        hg_cont.eventually (gt_mem_nhds (hg_val ▸ hg_lt_R))
      -- Eventually leading coefficient is nonzero
      have hlc_ne' : MvPolynomial.eval a₀ (f.coeff d) ≠ 0 := by rw [hlc_eq]; exact hlc_ne
      have h_lc_ev : ∀ᶠ a in nhds a₀, MvPolynomial.eval a (f.coeff d) ≠ 0 :=
        (MvPolynomial.continuous_eval _).continuousAt.eventually
          (isOpen_ne.mem_nhds hlc_ne')
      -- Combine
      exact (hg_ev.and h_lc_ev).mono fun a ⟨hga, ha_lc⟩ haS z hroot => by
        -- specialize f a ≠ 0 (its d-th coefficient is nonzero)
        have hfa_ne : specialize f a ≠ 0 := by
          intro h; apply ha_lc
          have : (specialize f a).coeff d = MvPolynomial.eval a (f.coeff d) := by
            simp [specialize, Polynomial.coeff_map]
          rw [← this, h]; simp
        -- Cauchy bound: ‖z‖₊ < cauchyBound (specialize f a)
        have hcb := hroot.norm_lt_cauchyBound hfa_ne
        -- cauchyBound ≤ g(a): sup ≤ sum in NNReal, then divide and add 1
        have hd_eq : (specialize f a).natDegree = d := hdeg a haS a₀ ha₀
        have hcb_le : (Polynomial.cauchyBound (specialize f a) : ℝ) ≤ g a := by
          have hsup_le : (Finset.range d).sup (fun i => ‖(specialize f a).coeff i‖₊) ≤
              ∑ i ∈ Finset.range d, ‖(specialize f a).coeff i‖₊ :=
            Finset.sup_le fun i hi =>
              Finset.single_le_sum (f := fun i => ‖(specialize f a).coeff i‖₊)
                (fun _ _ => zero_le _) hi
          have hcb_nn : Polynomial.cauchyBound (specialize f a) ≤
              (∑ i ∈ Finset.range d, ‖(specialize f a).coeff i‖₊) /
                ‖(specialize f a).leadingCoeff‖₊ + 1 := by
            simp only [Polynomial.cauchyBound, hd_eq]
            gcongr
          calc (↑(Polynomial.cauchyBound (specialize f a)) : ℝ)
              ≤ ↑((∑ i ∈ Finset.range d, ‖(specialize f a).coeff i‖₊) /
                  ‖(specialize f a).leadingCoeff‖₊ + 1) := by exact_mod_cast hcb_nn
            _ = g a := by
                simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
                show (∑ i ∈ Finset.range d, (↑‖(specialize f a).coeff i‖₊ : ℝ)) /
                  ↑‖(specialize f a).leadingCoeff‖₊ + 1 = g a
                congr 1; congr 1
                · apply Finset.sum_congr rfl; intro i _
                  simp [coe_nnnorm, Real.norm_eq_abs, specialize, Polynomial.coeff_map]
                · have : (specialize f a).leadingCoeff = MvPolynomial.eval a (f.coeff d) := by
                    unfold Polynomial.leadingCoeff
                    rw [hd_eq]; simp [specialize, Polynomial.coeff_map]
                  rw [this, coe_nnnorm, Real.norm_eq_abs]
        -- Chain: |z| = ‖z‖ < cauchyBound ≤ g(a) < R
        have hz_lt : |z| < R := calc
          |z| = ↑‖z‖₊ := by simp [coe_nnnorm, Real.norm_eq_abs]
          _ < ↑(Polynomial.cauchyBound (specialize f a)) := by exact_mod_cast hcb
          _ ≤ g a := hcb_le
          _ < R := hga
        exact Set.mem_Ioo.mpr (abs_lt.mp hz_lt)
    -- Combine: root z is in Ioo(-R)(R), not in K, so in some iftBall i
    -- and IFT uniqueness gives z = φ i a
    exact (h_ift.and (h_tube.and h_bound)).mono fun a ⟨ha_ift, ha_tube, ha_bound⟩ haS z hroot => by
      have hz_R := ha_bound haS z hroot
      have hz_Icc : z ∈ Set.Icc (-R) R := Set.Ioo_subset_Icc_self hz_R
      have hz_not_K : z ∉ K := fun hzK => ha_tube z hzK hroot
      have hz_ball : ∃ i, z ∈ iftBall i := by
        by_contra h; push_neg at h
        exact hz_not_K ⟨hz_Icc, fun hmem => let ⟨i, hi⟩ := Set.mem_iUnion.mp hmem; h i hi⟩
      obtain ⟨i, hi⟩ := hz_ball
      refine ⟨i, hφ_unique i a (Set.mem_iInter.mp ha_ift i) z hroot ?_⟩
      simp only [iftBall, Set.mem_Ioo] at hi
      rw [abs_sub_lt_iff]; constructor <;> linarith [hi.1, hi.2]
  -- (d) Derivative nonzero at each φ i a (so multiplicities stay 1)
  have h_der : ∀ᶠ a in nhds a₀,
      ∀ i, (Polynomial.derivative (specialize f a)).eval (φ i a) ≠ 0 := by
    simp only [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt
        (fun a => (Polynomial.derivative (specialize f a)).eval (φ i a)) a₀ := by
      have heq : (fun a => (Polynomial.derivative (specialize f a)).eval (φ i a)) =
          (fun a => ∑ j ∈ (Polynomial.derivative f).support,
            MvPolynomial.eval a ((Polynomial.derivative f).coeff j) * (φ i a) ^ j) := by
        ext a; simp [specialize, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
          Polynomial.sum_def, Polynomial.derivative_map]
      rw [heq]
      exact (continuousOn_finset_sum _ fun j _ =>
        (MvPolynomial.continuous_eval _).continuousOn.mul
          ((hφ_an i).continuousOn.pow j)).continuousAt
        ((hUi_open i).mem_nhds (ha₀_Ui i))
    exact hcont.eventually (isOpen_ne.mem_nhds (show
        (Polynomial.derivative (specialize f a₀)).eval (φ i a₀) ≠ 0 by
      rw [hφ_val i, show Polynomial.derivative (specialize f a₀) = Polynomial.derivative p
        from by rfl]
      intro h
      linarith [(Polynomial.one_lt_rootMultiplicity_iff_isRoot hp_ne).mpr
        ⟨hyr_root i, h⟩, hyr_mult i]))
  -- Combine and extract open neighborhood
  obtain ⟨U, hU_sub, hU_open, ha₀_U⟩ :=
    mem_nhds_iff.mp (h_ift.and (h_ord.and (h_roots.and h_der)))
  refine ⟨U, hU_open, ha₀_U, k, φ, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- Analyticity: each φ i is analytic on S ∩ U ⊆ Ui i
    intro i; exact (hφ_an i).mono fun a ha => Set.mem_iInter.mp (hU_sub ha.2).1 i
  · -- Ordering: φ i a < φ j a for i < j
    intro a ⟨_, haU⟩ i j hij; exact (hU_sub haU).2.1 i j hij
  · -- Root coverage: roots of f(a, ·) are exactly {φ₁(a), ..., φₖ(a)}
    intro a ⟨haS, haU⟩ z
    have hprops := hU_sub haU
    exact ⟨hprops.2.2.1 haS z,
      fun ⟨i, hi⟩ => hi ▸ hφ_root i a (Set.mem_iInter.mp hprops.1 i)⟩
  · -- Positive multiplicities: 1 > 0
    intro _; exact Nat.one_pos
  · -- Multiplicities = 1
    intro a ⟨haS, haU⟩ i
    have hprops := hU_sub haU
    have ha_Ui : a ∈ Ui i := Set.mem_iInter.mp hprops.1 i
    have hroot_a := hφ_root i a ha_Ui
    have hder_ne_a := hprops.2.2.2 i
    -- specialize f a ≠ 0 (from DegreeInvariant + existence of root yr₁ when k > 0)
    have hfa_ne : specialize f a ≠ 0 := by
      intro h
      have hd : p.natDegree = 0 := by
        have := hdeg a₀ ha₀ a haS; rw [this, h]; simp
      have : Multiset.card p.roots ≤ 0 := hd ▸ Polynomial.card_roots' p
      have hk0 : k = 0 := by
        simp only [hk_def]; rw [Multiset.toFinset_card_of_nodup (nodup_roots hp_sep)]; omega
      exact absurd i.isLt (by omega)
    have hle : ¬ 1 < (specialize f a).rootMultiplicity (φ i a) := by
      rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hfa_ne]
      push_neg; intro _; rwa [Polynomial.IsRoot]
    have hge := (Polynomial.rootMultiplicity_pos hfa_ne).mpr hroot_a
    show (specialize f a).rootMultiplicity (φ i a) = 1
    omega

/-! ### Helper lemmas for local-to-global patching -/

/-- Two strictly increasing functions `Fin k → ℝ` with the same range are equal.
This follows from `StrictMono.range_inj` (Fin k has WellFoundedLT). -/
theorem strictMono_fin_eq_of_range_eq {k : ℕ}
    (f g : Fin k → ℝ) (hf : StrictMono f) (hg : StrictMono g)
    (hrange : Set.range f = Set.range g) :
    f = g :=
  (hf.range_inj hg).mp hrange

/-- Two strictly increasing functions `Fin k₁ → α` and `Fin k₂ → α` with the same
range must have `k₁ = k₂`. -/
theorem strictMono_fin_card_eq {k₁ k₂ : ℕ} [LinearOrder α]
    (f : Fin k₁ → α) (g : Fin k₂ → α) (hf : StrictMono f) (hg : StrictMono g)
    (hrange : Set.range f = Set.range g) :
    k₁ = k₂ := by
  have e : Fin k₁ ≃ Fin k₂ :=
    (Equiv.ofInjective f hf.injective).trans
      ((Equiv.setCongr hrange).trans (Equiv.ofInjective g hg.injective).symm)
  have h := Fintype.card_congr e
  simp [Fintype.card_fin] at h
  exact h

/-- The root sets of two delineations on overlapping domains are equal at any
shared point. -/
theorem delineable_root_range_eq
    (T₁ T₂ : Set (Fin n → ℝ))
    (f : PolyR n) {k₁ k₂ : ℕ}
    (θ₁ : Fin k₁ → (Fin n → ℝ) → ℝ) (θ₂ : Fin k₂ → (Fin n → ℝ) → ℝ)
    (hroots₁ : ∀ a ∈ T₁, ∀ y, (specialize f a).IsRoot y ↔ ∃ i, y = θ₁ i a)
    (hroots₂ : ∀ a ∈ T₂, ∀ y, (specialize f a).IsRoot y ↔ ∃ i, y = θ₂ i a)
    (a : Fin n → ℝ) (ha₁ : a ∈ T₁) (ha₂ : a ∈ T₂) :
    Set.range (fun i => θ₁ i a) = Set.range (fun i => θ₂ i a) := by
  ext y; constructor
  · rintro ⟨i, rfl⟩
    exact ((hroots₂ a ha₂ _).mp ((hroots₁ a ha₁ _).mpr ⟨i, rfl⟩)).imp fun _ h => h.symm
  · rintro ⟨j, rfl⟩
    exact ((hroots₁ a ha₁ _).mp ((hroots₂ a ha₂ _).mpr ⟨j, rfl⟩)).imp fun _ h => h.symm

/-! ### Theorem: Local-to-global delineability -/

/-- On a connected open set `S` where `f` has constant degree and is locally analytically
delineable at every point, `f` is analytically delineable on all of `S`.

**Proof outline:**
1. Pick a base point `a₀ ∈ S` and get its local delineation with `k` sections.
2. The root count `k` is locally constant (from local delineability), hence constant
   on `S` by connectedness.
3. Define global root functions: `θ i a` = value of the `i`-th local root function at `a`.
   This is well-defined because two local delineations with the same `k` give the same
   `i`-th root at any shared point (unique ordering of finite sets of reals).
4. Analyticity follows from `analyticOn_of_locally_analyticOn` (Mathlib): each `θ i`
   agrees with a local analytic root function on a neighborhood of each point.
5. Ordering, root coverage, and constant multiplicities transfer from local to global. -/
theorem locally_delineable_to_global
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hlocal : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)),
      IsOpen U ∧ a ∈ U ∧ AnalyticDelineable f (S ∩ U)) :
    AnalyticDelineable f S := by
  -- Step 1: Pick base point a₀ and get its local delineation
  obtain ⟨a₀, ha₀⟩ := hS_conn.nonempty
  obtain ⟨U₀, hU₀_open, ha₀U₀, k, θ₀, m₀, hθ₀_an, hθ₀_ord, hθ₀_roots, hm₀_pos, hm₀_const⟩ :=
    hlocal a₀ ha₀
  -- Step 2: By connectivity, every point of S has a local delineation with k sections
  -- and multiplicities m₀. The root count and multiplicities are both locally constant
  -- on S (constant within each local delineation), hence constant on connected S.
  have hk_loc : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)) (θ : Fin k → (Fin n → ℝ) → ℝ),
      IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOn ℝ (θ i) (S ∩ U)) ∧
      (∀ b ∈ S ∩ U, ∀ i j : Fin k, i < j → θ i b < θ j b) ∧
      (∀ b ∈ S ∩ U, ∀ y, (specialize f b).IsRoot y ↔ ∃ i, y = θ i b) ∧
      (∀ b ∈ S ∩ U, ∀ i, (specialize f b).rootMultiplicity (θ i b) = m₀ i) := by
    -- Extract delineation data at each point
    have hlocal' : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)) (k' : ℕ)
        (θ' : Fin k' → (Fin n → ℝ) → ℝ) (m' : Fin k' → ℕ),
        IsOpen U ∧ a ∈ U ∧
        (∀ i, AnalyticOn ℝ (θ' i) (S ∩ U)) ∧
        (∀ b ∈ S ∩ U, ∀ i j : Fin k', i < j → θ' i b < θ' j b) ∧
        (∀ b ∈ S ∩ U, ∀ y, (specialize f b).IsRoot y ↔ ∃ i, y = θ' i b) ∧
        (∀ i, 0 < m' i) ∧
        (∀ b ∈ S ∩ U, ∀ i, (specialize f b).rootMultiplicity (θ' i b) = m' i) := by
      intro a ha
      obtain ⟨U, hU, haU, k', θ', m', h1, h2, h3, h4, h5⟩ := hlocal a ha
      exact ⟨U, k', θ', m', hU, haU, h1, h2, h3, h4, h5⟩
    choose Uc kc θc mc hUc_open hUc_mem hθc_an hθc_ord hθc_roots _hmc_pos hmc_const using hlocal'
    -- Overlapping delineations have the same root count
    have hkc_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
        b ∈ S ∩ Uc a ha → kc a ha = kc b hb :=
      fun a b ha hb hab => strictMono_fin_card_eq _ _
        (hθc_ord a ha b hab) (hθc_ord b hb b ⟨hb, hUc_mem b hb⟩)
        (delineable_root_range_eq (S ∩ Uc a ha) (S ∩ Uc b hb) f
          (θc a ha) (θc b hb) (hθc_roots a ha) (hθc_roots b hb) b hab ⟨hb, hUc_mem b hb⟩)
    -- Root count is constant on S by IsPreconnected.constant
    let rootCount : (Fin n → ℝ) → ℕ := fun a => if ha : a ∈ S then kc a ha else 0
    have hrc_cont : ContinuousOn rootCount S := by
      intro a ha
      rw [ContinuousWithinAt, hS_open.nhdsWithin_eq ha, nhds_discrete ℕ, Filter.tendsto_pure]
      exact Filter.Eventually.mono ((hS_open.inter (hUc_open a ha)).mem_nhds ⟨ha, hUc_mem a ha⟩)
        fun b ⟨hbS, hbU⟩ => show rootCount b = rootCount a by
          simp only [rootCount, dif_pos hbS, dif_pos ha]
          exact (hkc_agree a b ha hbS ⟨hbS, hbU⟩).symm
    have hkc_eq : ∀ a (ha : a ∈ S), kc a ha = k := by
      intro a ha
      have h1 := hS_conn.isPreconnected.constant hrc_cont ha ha₀
      simp only [rootCount, dif_pos ha, dif_pos ha₀] at h1
      have h2 : kc a₀ ha₀ = k := strictMono_fin_card_eq _ _
        (hθc_ord a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩)
        (hθ₀_ord a₀ ⟨ha₀, ha₀U₀⟩)
        (delineable_root_range_eq (S ∩ Uc a₀ ha₀) (S ∩ U₀) f
          (θc a₀ ha₀) θ₀ (hθc_roots a₀ ha₀) hθ₀_roots
          a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ ⟨ha₀, ha₀U₀⟩)
      omega
    -- Cast root functions from overlapping delineations agree, so multiplicities agree
    have hmc_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
        b ∈ S ∩ Uc a ha → ∀ i : Fin k,
        mc a ha (Fin.cast (hkc_eq a ha).symm i) = mc b hb (Fin.cast (hkc_eq b hb).symm i) := by
      intro a b ha hb hab i
      have hval_eq : θc a ha (Fin.cast (hkc_eq a ha).symm i) b =
          θc b hb (Fin.cast (hkc_eq b hb).symm i) b := by
        have hrange : Set.range (fun j : Fin k => θc a ha (Fin.cast (hkc_eq a ha).symm j) b) =
            Set.range (fun j : Fin k => θc b hb (Fin.cast (hkc_eq b hb).symm j) b) := by
          ext y; simp only [Set.mem_range]; constructor
          · rintro ⟨j, rfl⟩
            obtain ⟨j', hj'⟩ := (hθc_roots b hb b ⟨hb, hUc_mem b hb⟩ _).mp
              ((hθc_roots a ha b hab _).mpr ⟨_, rfl⟩)
            exact ⟨Fin.cast (hkc_eq b hb) j', hj'.symm⟩
          · rintro ⟨j, rfl⟩
            obtain ⟨j', hj'⟩ := (hθc_roots a ha b hab _).mp
              ((hθc_roots b hb b ⟨hb, hUc_mem b hb⟩ _).mpr ⟨_, rfl⟩)
            exact ⟨Fin.cast (hkc_eq a ha) j', hj'.symm⟩
        exact congrFun (strictMono_fin_eq_of_range_eq _ _
          (fun p q hpq => hθc_ord a ha b hab _ _ (by exact_mod_cast hpq))
          (fun p q hpq => hθc_ord b hb b ⟨hb, hUc_mem b hb⟩ _ _ (by exact_mod_cast hpq))
          hrange) i
      have hm1 := hmc_const a ha b hab (Fin.cast (hkc_eq a ha).symm i)
      rw [hval_eq] at hm1
      exact hm1.symm.trans (hmc_const b hb b ⟨hb, hUc_mem b hb⟩ _)
    -- Multiplicities equal m₀ by connectivity on connected S
    have hmc_eq : ∀ (a : Fin n → ℝ) (ha : a ∈ S) (i : Fin k),
        mc a ha (Fin.cast (hkc_eq a ha).symm i) = m₀ i := by
      intro a ha i
      let multFunc : (Fin n → ℝ) → ℕ := fun b =>
        if hb : b ∈ S then mc b hb (Fin.cast (hkc_eq b hb).symm i) else 0
      have hmc_cont : ContinuousOn multFunc S := by
        intro a' ha'
        rw [ContinuousWithinAt, hS_open.nhdsWithin_eq ha', nhds_discrete ℕ, Filter.tendsto_pure]
        exact Filter.Eventually.mono
          ((hS_open.inter (hUc_open a' ha')).mem_nhds ⟨ha', hUc_mem a' ha'⟩)
          fun b ⟨hbS, hbU⟩ => show multFunc b = multFunc a' by
            simp only [multFunc, dif_pos hbS, dif_pos ha']
            exact (hmc_agree a' b ha' hbS ⟨hbS, hbU⟩ i).symm
      have h1 := hS_conn.isPreconnected.constant hmc_cont ha ha₀
      simp only [multFunc, dif_pos ha, dif_pos ha₀] at h1
      have hval₀ : θc a₀ ha₀ (Fin.cast (hkc_eq a₀ ha₀).symm i) a₀ = θ₀ i a₀ := by
        have hrange₀ : Set.range (fun j : Fin k => θc a₀ ha₀ (Fin.cast (hkc_eq a₀ ha₀).symm j) a₀) =
            Set.range (fun j => θ₀ j a₀) := by
          ext y; simp only [Set.mem_range]; constructor
          · rintro ⟨j, rfl⟩
            exact ((hθ₀_roots a₀ ⟨ha₀, ha₀U₀⟩ _).mp
              ((hθc_roots a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _).mpr ⟨_, rfl⟩)).imp
              fun _ h => h.symm
          · rintro ⟨j, rfl⟩
            obtain ⟨j', hj'⟩ := (hθc_roots a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _).mp
              ((hθ₀_roots a₀ ⟨ha₀, ha₀U₀⟩ _).mpr ⟨j, rfl⟩)
            exact ⟨Fin.cast (hkc_eq a₀ ha₀) j', hj'.symm⟩
        exact congrFun (strictMono_fin_eq_of_range_eq _ _
          (fun p q hpq => hθc_ord a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _ _ (by exact_mod_cast hpq))
          (fun p q hpq => hθ₀_ord a₀ ⟨ha₀, ha₀U₀⟩ p q hpq)
          hrange₀) i
      have hm₀ := hmc_const a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ (Fin.cast (hkc_eq a₀ ha₀).symm i)
      rw [hval₀] at hm₀
      have hm₀' := hm₀_const a₀ ⟨ha₀, ha₀U₀⟩ i
      omega
    -- Construct Fin k-indexed delineation at each point
    intro a ha
    refine ⟨Uc a ha, fun i => θc a ha (Fin.cast (hkc_eq a ha).symm i),
      hUc_open a ha, hUc_mem a ha, ?_, ?_, ?_, ?_⟩
    · exact fun i => hθc_an a ha _
    · intro b hb i j hij
      exact hθc_ord a ha b hb _ _ (by exact_mod_cast hij)
    · intro b hb y
      rw [hθc_roots a ha b hb y]
      exact ⟨fun ⟨i, hi⟩ => ⟨Fin.cast (hkc_eq a ha) i, hi⟩,
             fun ⟨i, hi⟩ => ⟨Fin.cast (hkc_eq a ha).symm i, by simpa using hi⟩⟩
    · intro b hb i
      exact (hmc_const a ha b hb (Fin.cast (hkc_eq a ha).symm i)).trans (hmc_eq a ha i)
  -- Step 3: Choose local delineation data at each point
  choose U_loc θ_loc h_all using hk_loc
  -- Step 4: Two local delineations with k sections agree at shared points
  have hθ_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ U_loc a ha →
      (fun j => θ_loc a ha j b) = (fun j => θ_loc b hb j b) := by
    intro a b ha hb hab
    exact strictMono_fin_eq_of_range_eq _ _
      ((h_all a ha).2.2.2.1 b hab) ((h_all b hb).2.2.2.1 b ⟨hb, (h_all b hb).2.1⟩)
      (delineable_root_range_eq (S ∩ U_loc a ha) (S ∩ U_loc b hb) f
        (θ_loc a ha) (θ_loc b hb) (h_all a ha).2.2.2.2.1 (h_all b hb).2.2.2.2.1
        b hab ⟨hb, (h_all b hb).2.1⟩)
  -- Step 5: Define global root functions
  refine ⟨k, fun i a => if ha : a ∈ S then θ_loc a ha i a else 0, m₀,
    ?_, ?_, ?_, hm₀_pos, ?_⟩
  · -- Analyticity: each θ_i is AnalyticOn S
    intro i
    apply analyticOn_of_locally_analyticOn
    intro a ha
    refine ⟨U_loc a ha, (h_all a ha).1, (h_all a ha).2.1, ?_⟩
    apply ((h_all a ha).2.2.1 i).congr
    intro b hb
    dsimp only
    rw [dif_pos hb.1]
    exact (congrFun (hθ_agree a b ha hb.1 hb) i).symm
  · -- Ordering: θ_i a < θ_j a for i < j
    intro a ha i j hij
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.1 a ⟨ha, (h_all a ha).2.1⟩ i j hij
  · -- Root coverage: roots of f(a, ·) are exactly {θ_1(a), ..., θ_k(a)}
    intro a ha y
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.2.1 a ⟨ha, (h_all a ha).2.1⟩ y
  · -- Constant multiplicities: rootMultiplicity (θ_i a) = m₀ i
    intro a ha i
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.2.2 a ⟨ha, (h_all a ha).2.1⟩ i

/-- **Theorem** (Root continuity ⟹ delineability).

On a connected open set where `f` is separable at every point, `f` is analytically
delineable. Proved from `separable_locally_delineable` (axiom 2) and
`locally_delineable_to_global` (axiom 3). -/
theorem root_continuity_delineable
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hdeg : DegreeInvariant f S)
    (hsep : ∀ a ∈ S, IsCoprime (specialize f a) (Polynomial.derivative (specialize f a))) :
    AnalyticDelineable f S :=
  locally_delineable_to_global S f hS_open hS_conn
    fun a ha => separable_locally_delineable f a S ha hdeg (hsep a ha)

/-! ### Partial derivative of `toMvPoly` with respect to the main variable -/

/-- `finSuccEquiv` commutes with `pderiv 0` and `derivative`:
the partial derivative of a multivariate polynomial w.r.t. variable 0 corresponds to
the polynomial derivative under the `finSuccEquiv` isomorphism. -/
private theorem finSuccEquiv_pderiv_zero (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv 0 p) =
    Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ n p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.pderiv_C, map_zero]
    rw [show MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a)
      from by simp [MvPolynomial.finSuccEquiv_apply]]
    simp
  | add p q ihp ihq =>
    simp only [map_add, ihp, ihq]
  | mul_X p j ih =>
    have hleibniz := (MvPolynomial.pderiv (0 : Fin (n + 1))).leibniz p (MvPolynomial.X j)
    simp only [smul_eq_mul] at hleibniz
    rw [hleibniz, mul_comm (MvPolynomial.X j) _, mul_comm p _]
    refine Fin.cases ?_ ?_ j
    · -- j = 0: X_0 maps to Polynomial.X
      simp only [MvPolynomial.pderiv_X_self, map_add, map_mul, map_one,
        MvPolynomial.finSuccEquiv_X_zero]
      rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, ih]
      ring
    · -- j = succ k: X_{k+1} maps to Polynomial.C (X_k)
      intro k
      have hpd : MvPolynomial.pderiv (0 : Fin (n + 1))
          (MvPolynomial.X (Fin.succ k) : MvPolynomial (Fin (n + 1)) ℝ) = 0 := by
        apply MvPolynomial.pderiv_X_of_ne
        exact Fin.succ_ne_zero k
      simp only [hpd, zero_mul, zero_add, map_mul,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.derivative_mul,
        Polynomial.derivative_C, mul_zero, add_zero, ih]

/-! ### orderFull = 1 at simple roots -/

/-- The `x₀`-partial of `toMvPoly f` is `toMvPoly` of the `t`-derivative. -/
theorem pderiv_zero_toMvPoly (f : PolyR n) :
    MvPolynomial.pderiv 0 (toMvPoly f) = toMvPoly (Polynomial.derivative f) := by
  have hinj := (MvPolynomial.finSuccEquiv ℝ n).injective
  apply hinj
  unfold toMvPoly
  rw [finSuccEquiv_pderiv_zero,
    (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply,
    (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply]

/-- Evaluation of `pderiv 0 (toMvPoly f)` at `(y, a)` equals `(derivative (specialize f a)).eval y`. -/
theorem eval_pderiv_zero_toMvPoly
    (f : PolyR n) (a : Fin n → ℝ) (y : ℝ) :
    MvPolynomial.eval (Fin.cons y a) (MvPolynomial.pderiv 0 (toMvPoly f)) =
    Polynomial.eval y (Polynomial.derivative (specialize f a)) := by
  rw [pderiv_zero_toMvPoly]
  unfold toMvPoly specialize
  rw [MvPolynomial.eval_eq_eval_mv_eval',
    (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply,
    Polynomial.derivative_map]

/-- At a simple root `(a, y)` of `f`, McCallum's multivariate order `ord_{(a,y)} f = 1`:
the value `f(a,y) = 0` (order ≥ 1), and the `t`-partial `f'(a,y) ≠ 0` (simple root) gives a
nonvanishing first-order derivative (order = 1). -/
theorem orderFull_eq_one_of_simple_root
    (f : PolyR n)
    (a : Fin n → ℝ)
    (y : ℝ)
    (hsimple : (specialize f a).rootMultiplicity y = 1) :
    orderFull f a y = 1 := by
  have hne : specialize f a ≠ 0 := by intro h; rw [h] at hsimple; simp at hsimple
  have hroot : (specialize f a).IsRoot y :=
    (Polynomial.rootMultiplicity_pos hne).mp (by omega)
  unfold orderFull polyOrder
  rw [show (1 : ℕ∞) = ↑(1 : ℕ) from rfl]
  rw [order_eq_natCast_iff (𝕜 := ℝ)]
  constructor
  · intro m hm
    interval_cases m
    ext v
    simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply]
    have heval : MvPolynomial.eval (Fin.cons y a) (toMvPoly f) =
        (specialize f a).eval y := by
      unfold toMvPoly specialize
      rw [MvPolynomial.eval_eq_eval_mv_eval',
        (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply]
    rw [Polynomial.IsRoot] at hroot
    exact heval ▸ hroot
  · rw [iteratedFDeriv_ne_zero_iff_exists_iteratedPDeriv]
    refine ⟨[0], rfl, ?_⟩
    simp only [iteratedPDeriv, List.foldr_cons, List.foldr_nil]
    rw [eval_pderiv_zero_toMvPoly]
    have hnotder : ¬ (Polynomial.derivative (specialize f a)).IsRoot y := by
      intro hder
      have h1lt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hroot, hder⟩
      omega
    rw [Polynomial.IsRoot] at hnotder
    exact fun h => hnotder h

/-! ### Order invariance on simple-root sections -/

/-- On a section `SectionGraph θ S` where every root is simple (multiplicity 1),
`OrderInvariantFull f (SectionGraph θ S)` holds because `orderFull = 1` everywhere. -/
theorem order_invariant_section_of_mult_one
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (θ : (Fin n → ℝ) → ℝ)
    (hmult : ∀ a ∈ S, (specialize f a).rootMultiplicity (θ a) = 1) :
    OrderInvariantFull f (SectionGraph θ S) := by
  intro p hp q hq
  obtain ⟨hpS, hpy⟩ := hp
  obtain ⟨hqS, hqy⟩ := hq
  have h1 : orderFull f p.1 p.2 = 1 := by
    rw [hpy]
    exact orderFull_eq_one_of_simple_root f p.1 (θ p.1) (hmult p.1 hpS)
  have h2 : orderFull f q.1 q.2 = 1 := by
    rw [hqy]
    exact orderFull_eq_one_of_simple_root f q.1 (θ q.1) (hmult q.1 hqS)
  rw [h1, h2]

/-! ### Main theorem -/

/-- **Theorem**: `simple_roots_delineable`.

A polynomial that is separable at every point of a connected open set is analytically
delineable there, and order-invariant in each section.

This is proved from the IFT axiom + root continuity axiom (for delineability), plus
the `orderFull_eq_one_of_simple_root` theorem (for order invariance). -/
theorem simple_roots_delineable'
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hdeg : DegreeInvariant f S)
    (hsep : ∀ a ∈ S, IsCoprime (specialize f a) (Polynomial.derivative (specialize f a))) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  constructor
  · -- Delineability: from root_continuity_delineable
    exact root_continuity_delineable S f hS_open hS_conn hdeg hsep
  · -- Order invariance on each section
    intro θ _hθ_cont hθ_root
    -- Separability at each point means each root has multiplicity 1
    have hmult : ∀ a ∈ S, (specialize f a).rootMultiplicity (θ a) = 1 := by
      intro a ha
      have hcop := hsep a ha
      have hroot := hθ_root a ha
      have hsep' : (specialize f a).Separable :=
        (Polynomial.separable_def _).mpr hcop
      have hle := Polynomial.rootMultiplicity_le_one_of_separable hsep' (θ a)
      have hne : specialize f a ≠ 0 := hsep'.ne_zero
      have hpos : 0 < (specialize f a).rootMultiplicity (θ a) :=
        (Polynomial.rootMultiplicity_pos hne).mpr hroot
      omega
    exact order_invariant_section_of_mult_one S f θ hmult

end
