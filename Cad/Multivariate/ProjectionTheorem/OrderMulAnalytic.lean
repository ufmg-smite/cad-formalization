import Cad.Multivariate.ProjectionTheorem.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions

/-!
# Multiplicativity of the vanishing `order` for analytic functions over `ℂ`

`order ℂ (f · g) x₀ = order ℂ f x₀ + order ℂ g x₀` for `f, g` analytic at `x₀`, in any
`ℂ`-normed space. Proved by reducing to the one-variable case along generic complex lines
(`analyticOrderAt` of the line restriction) plus polarization of symmetric multilinear maps.

Relocated from `Cad.Multivariate.ProjectionTheorem.Generalized.Lifting` so the analytic germ ring `𝒪ₙ`
(`Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticGerm`) can use it as the valuation/additivity engine without
creating an import cycle.
-/

noncomputable section

open scoped Topology
open Filter Classical

/-- If `h` is eventually zero near `x₀`, then `order h x₀ = ⊤`. -/
lemma order_eq_top_of_eventuallyEq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : E → ℂ) (x₀ : E) (hev : h =ᶠ[𝓝 x₀] 0) :
    order ℂ h x₀ = ⊤ := by
  rw [order_eq_top_iff (𝕜 := ℂ)]; intro n
  have := (hev.iteratedFDeriv ℂ n).self_of_nhds
  rw [this]
  rcases n with _ | n
  · ext m; simp [iteratedFDeriv_zero_apply]
  · exact congr_fun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n) (0 : ℂ)) x₀

/-- If `order ℂ f x₀ = ⊤` and `f` is analytic at `x₀`, then `f` is eventually zero. -/
lemma eventuallyEq_zero_of_order_eq_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ : E) (hf : AnalyticAt ℂ f x₀)
    (hord : order ℂ f x₀ = ⊤) :
    f =ᶠ[𝓝 x₀] 0 := by
  have hderiv_zero := (order_eq_top_iff (𝕜 := ℂ)).mp hord
  obtain ⟨p, r, hp⟩ := hf
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨{z | z - x₀ ∈ Metric.eball 0 r}, ?_, fun z hz => ?_⟩
  · exact mem_nhds_iff.mpr ⟨_, le_refl _, Metric.isOpen_eball.preimage
      (continuous_id.sub continuous_const), by simp [Metric.mem_eball, hp.r_pos]⟩
  · have hsum := hp.hasSum_iteratedFDeriv hz
    simp only [hderiv_zero, ContinuousMultilinearMap.zero_apply, smul_zero] at hsum
    rw [show x₀ + (z - x₀) = z from by abel] at hsum
    exact hsum.unique hasSum_zero

/-- Polarization for symmetric continuous multilinear maps over ℂ: if `T` is symmetric
and vanishes on the diagonal, then `T = 0`. Proved via `iteratedFDeriv_comp_diagonal`
which gives `n! · T(v) = 0` from the diagonal vanishing. -/
lemma symmetric_multilinear_eq_zero_of_diagonal_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (T : E [×n]→L[ℂ] ℂ)
    (hsymm : ∀ (v : Fin n → E) (σ : Equiv.Perm (Fin n)), T (v ∘ σ) = T v)
    (hdiag : ∀ w : E, T (fun _ => w) = 0) :
    T = 0 := by
  ext v
  rcases n with _ | n
  · convert hdiag 0 using 1; congr 1; exact Subsingleton.elim _ _
  · have h := T.iteratedFDeriv_comp_diagonal 0 v
    have h_lhs : iteratedFDeriv ℂ (n + 1) (fun _ : E => (0 : ℂ)) 0 v = 0 := by
      simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
    rw [show (fun x : E => T (fun _ => x)) = (fun _ => (0 : ℂ)) from funext hdiag,
      h_lhs] at h
    simp only [fun σ : Equiv.Perm (Fin (n + 1)) =>
      show T (fun i => v (σ i)) = T v from hsymm v σ] at h
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- The line restriction `t ↦ f(x₀ + t • w)` is analytic at 0 when `f` is analytic at `x₀`. -/
lemma analyticAt_line_restriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ w : E) (hf : AnalyticAt ℂ f x₀) :
    AnalyticAt ℂ (fun t : ℂ => f (x₀ + t • w)) 0 := by
  apply AnalyticAt.comp (f := fun t : ℂ => x₀ + t • w)
  · simpa using hf
  · fun_prop

/-- Chain rule for line restrictions: the `k`-th iterated derivative of `t ↦ f(x₀ + t•w)`
at `t = 0` equals the `k`-th iterated Fréchet derivative of `f` at `x₀` evaluated
on the diagonal `(w, w, …, w)`. Both sides equal `k! · pₖ(w,…,w)` where `p` is
the power series of `f`. -/
lemma iteratedDeriv_line_eq_iteratedFDeriv_diag
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ w : E) (k : ℕ)
    (hf : AnalyticAt ℂ f x₀) :
    iteratedDeriv k (fun t : ℂ => f (x₀ + t • w)) 0 =
      (iteratedFDeriv ℂ k f x₀) (fun _ => w) := by
  obtain ⟨p, r, hp⟩ := hf
  have hND := hp.iteratedFDeriv_eq_sum_of_completeSpace (n := k) (fun _ => w)
  have hp0 : HasFPowerSeriesOnBall (fun y => f (y + x₀)) p 0 r := by
    have := hp.comp_sub (-x₀)
    simp only [sub_neg_eq_add, add_neg_cancel] at this; exact this
  let L_w : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) w
  have hL_zero : L_w 0 = 0 := map_zero L_w
  have hp_line : HasFPowerSeriesOnBall (fun t => f (x₀ + t • w))
      (p.compContinuousLinearMap L_w) 0 (r / ‖L_w‖ₑ) := by
    have h1 : HasFPowerSeriesOnBall ((fun y => f (y + x₀)) ∘ L_w)
        (p.compContinuousLinearMap L_w) 0 (r / ‖L_w‖ₑ) := by
      have hp0' : HasFPowerSeriesOnBall (fun y => f (y + x₀)) p (L_w (0 : ℂ)) r := by
        rwa [show L_w (0 : ℂ) = (0 : E) from map_zero L_w]
      exact hp0'.compContinuousLinearMap
    convert h1 using 1
    ext t; simp [L_w, add_comm]
  have h1D := hp_line.iteratedFDeriv_eq_sum_of_completeSpace (n := k) (fun _ => (1 : ℂ))
  rw [show iteratedDeriv k (fun t : ℂ => f (x₀ + t • w)) 0 =
    (iteratedFDeriv ℂ k (fun t : ℂ => f (x₀ + t • w)) 0) (fun _ => (1 : ℂ)) from by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]; simp]
  rw [h1D, hND]
  congr 1; ext σ
  simp [FormalMultilinearSeries.compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, L_w]

/-- Vanishing order is additive for products of analytic functions:
`order(f · g) = order(f) + order(g)`. The proof reduces to the 1-variable case via
line restrictions and polarization. -/
lemma order_mul_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (x₀ : E)
    (hf : AnalyticAt ℂ f x₀) (hg : AnalyticAt ℂ g x₀) :
    order ℂ (fun z => f z * g z) x₀ = order ℂ f x₀ + order ℂ g x₀ := by
  by_cases hf_top : order ℂ f x₀ = ⊤
  · have hfg : order ℂ (fun z => f z * g z) x₀ = ⊤ :=
      order_eq_top_of_eventuallyEq_zero _ x₀ <| by
        filter_upwards [eventuallyEq_zero_of_order_eq_top f x₀ hf hf_top] with z hz
        simp [hz]
    simp [hfg, hf_top]
  by_cases hg_top : order ℂ g x₀ = ⊤
  · have hfg : order ℂ (fun z => f z * g z) x₀ = ⊤ :=
      order_eq_top_of_eventuallyEq_zero _ x₀ <| by
        filter_upwards [eventuallyEq_zero_of_order_eq_top g x₀ hg hg_top] with z hz
        simp [hz]
    simp [hfg, hg_top]
  -- Both orders are finite: extract natural numbers m, n
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hf_top
  obtain ⟨nn, hnn⟩ := ENat.ne_top_iff_exists.mp hg_top
  rw [← hm, ← hnn, ← ENat.coe_add]
  -- Characterize: iteratedFDeriv vanishes below order, nonzero at order
  have hf_below : ∀ j < m, iteratedFDeriv ℂ j f x₀ = 0 := fun j hj =>
    iteratedFDeriv_eq_zero_of_lt_order (by rw [← hm]; exact_mod_cast hj)
  have hf_at : iteratedFDeriv ℂ m f x₀ ≠ 0 :=
    ((order_eq_natCast_iff (𝕜 := ℂ) (n := m)).mp hm.symm).2
  have hg_below : ∀ j < nn, iteratedFDeriv ℂ j g x₀ = 0 := fun j hj =>
    iteratedFDeriv_eq_zero_of_lt_order (by rw [← hnn]; exact_mod_cast hj)
  have hg_at : iteratedFDeriv ℂ nn g x₀ ≠ 0 :=
    ((order_eq_natCast_iff (𝕜 := ℂ) (n := nn)).mp hnn.symm).2
  -- Diagonal vanishing for f and g
  have hf_diag : ∀ j < m, ∀ w : E, (iteratedFDeriv ℂ j f x₀) (fun _ => w) = 0 :=
    fun j hj w => by simp [hf_below j hj]
  have hg_diag : ∀ j < nn, ∀ w : E, (iteratedFDeriv ℂ j g x₀) (fun _ => w) = 0 :=
    fun j hj w => by simp [hg_below j hj]
  -- By polarization: ∃ w₀ with diagonal nonzero at order
  have hf_diag_ne : ∃ w₀ : E, (iteratedFDeriv ℂ m f x₀) (fun _ => w₀) ≠ 0 := by
    by_contra h; push_neg at h
    exact hf_at (symmetric_multilinear_eq_zero_of_diagonal_zero _
      (fun v σ => hf.contDiffAt.iteratedFDeriv_comp_perm v σ) h)
  have hg_diag_ne : ∃ w₀ : E, (iteratedFDeriv ℂ nn g x₀) (fun _ => w₀) ≠ 0 := by
    by_contra h; push_neg at h
    exact hg_at (symmetric_multilinear_eq_zero_of_diagonal_zero _
      (fun v σ => hg.contDiffAt.iteratedFDeriv_comp_perm v σ) h)
  -- Line restriction orders
  have hf_line : ∀ w, (m : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 := by
    intro w
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_line_restriction f x₀ w hf)]
    exact fun i hi => by rw [iteratedDeriv_line_eq_iteratedFDeriv_diag f x₀ w i hf]; exact hf_diag i hi w
  have hg_line : ∀ w, (nn : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => g (x₀ + t • w)) 0 := by
    intro w
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_line_restriction g x₀ w hg)]
    exact fun i hi => by rw [iteratedDeriv_line_eq_iteratedFDeriv_diag g x₀ w i hg]; exact hg_diag i hi w
  -- Analyticity of the product
  have hfg : AnalyticAt ℂ (fun z => f z * g z) x₀ := hf.mul hg
  -- ≥ direction: order(fg) ≥ m + nn via 1D analyticOrderAt_mul + polarization
  have h_ge : (↑(m + nn) : ℕ∞) ≤ order ℂ (fun z => f z * g z) x₀ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    have hjlt : j < m + nn := by exact_mod_cast (hj ▸ hlt : (↑j : ℕ∞) < ↑(m + nn))
    have hj_ne := ((order_eq_natCast_iff (𝕜 := ℂ) (n := j)).mp hj.symm).2
    apply hj_ne
    apply symmetric_multilinear_eq_zero_of_diagonal_zero _
      (fun v σ => hfg.contDiffAt.iteratedFDeriv_comp_perm v σ)
    intro w
    rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag _ x₀ w j hfg]
    have h_anal := analyticAt_line_restriction (fun z => f z * g z) x₀ w hfg
    have h_fg_ord : ↑(m + nn) ≤
        analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 := by
      calc (↑(m + nn) : ℕ∞) = ↑m + ↑nn := by push_cast; ring
        _ ≤ analyticOrderAt (fun t => f (x₀ + t • w)) 0 +
            analyticOrderAt (fun t => g (x₀ + t • w)) 0 := add_le_add (hf_line w) (hg_line w)
        _ = analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 :=
            (analyticOrderAt_mul (analyticAt_line_restriction f x₀ w hf)
              (analyticAt_line_restriction g x₀ w hg)).symm
    exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero h_anal).mp h_fg_ord) j hjlt
  -- ≤ direction: find w with both T_f(w,...,w) ≠ 0 and T_g(w,...,w) ≠ 0
  have h_le : order ℂ (fun z => f z * g z) x₀ ≤ ↑(m + nn) := by
    suffices h : iteratedFDeriv ℂ (m + nn) (fun z => f z * g z) x₀ ≠ 0 by
      have hex : ∃ n, iteratedFDeriv ℂ n (fun z => f z * g z) x₀ ≠ 0 := ⟨m + nn, h⟩
      unfold order; rw [dif_pos hex]; exact_mod_cast Nat.find_min' hex h
    obtain ⟨v₀, hv₀⟩ := hf_diag_ne
    obtain ⟨w₀, hw₀⟩ := hg_diag_ne
    -- Find w with both T_f(fun _ => w) ≠ 0 and T_g(fun _ => w) ≠ 0
    -- (using 1D analytic argument on the line v₀ + t•w₀)
    obtain ⟨w, hw_f, hw_g⟩ : ∃ w : E,
        (iteratedFDeriv ℂ m f x₀) (fun _ => w) ≠ 0 ∧
        (iteratedFDeriv ℂ nn g x₀) (fun _ => w) ≠ 0 := by
      -- D_g(w) := T_g(w,...,w) is analytic (multilinear map composed with diagonal)
      have hDg_anal : AnalyticAt ℂ
          (fun w : E => (iteratedFDeriv ℂ nn g x₀) (fun _ => w)) v₀ :=
        (iteratedFDeriv ℂ nn g x₀).analyticAt.comp
          (AnalyticAt.pi (fun _ : Fin nn => analyticAt_id))
      -- ψ(t) := T_g(v₀+t•w₀,...) is analytic at 0
      have hψ_anal := analyticAt_line_restriction
        (fun w => (iteratedFDeriv ℂ nn g x₀) (fun _ => w)) v₀ w₀ hDg_anal
      -- nn-th derivative of ψ at 0 is nn! • T_g(w₀,...,w₀) ≠ 0
      have hψ_deriv : iteratedDeriv nn (fun t : ℂ =>
          (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀)) 0 ≠ 0 := by
        rw [iteratedDeriv_line_eq_iteratedFDeriv_diag _ v₀ w₀ nn hDg_anal,
            (iteratedFDeriv ℂ nn g x₀).iteratedFDeriv_comp_diagonal v₀ (fun _ => w₀)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero nn)) hw₀
      -- analyticOrderAt ψ 0 ≠ ⊤ (since nn-th derivative is nonzero)
      have hψ_ne_top : analyticOrderAt (fun t : ℂ =>
          (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀)) 0 ≠ ⊤ := by
        intro h_top; apply hψ_deriv
        have h_le : ↑(nn + 1) ≤ analyticOrderAt (fun t : ℂ =>
            (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀)) 0 := by
          rw [h_top]; exact le_top
        exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hψ_anal).mp h_le nn (by omega)
      -- ∃ᶠ t near 0, T_g(v₀+t•w₀,...) ≠ 0
      have hψ_freq : ∃ᶠ t in 𝓝 (0 : ℂ),
          (iteratedFDeriv ℂ nn g x₀) (fun _ => v₀ + t • w₀) ≠ 0 :=
        Filter.not_eventually.mp (analyticOrderAt_eq_top.not.mp hψ_ne_top)
      -- ∀ᶠ t near 0, T_f(v₀+t•w₀,...) ≠ 0 (continuity + nonvanishing at 0)
      have hφ_ev : ∀ᶠ t in 𝓝 (0 : ℂ),
          (iteratedFDeriv ℂ m f x₀) (fun _ => v₀ + t • w₀) ≠ 0 := by
        refine ContinuousAt.eventually_ne ?_ ?_
        · exact (iteratedFDeriv ℂ m f x₀).cont.continuousAt.comp (by fun_prop)
        · simpa using hv₀
      -- Combine: ∃ t with both nonzero
      obtain ⟨t, hψt, hφt⟩ := (hψ_freq.and_eventually hφ_ev).exists
      exact ⟨v₀ + t • w₀, hφt, hψt⟩
    -- w gives exact analyticOrderAt: f_w has order m, g_w has order nn
    have hf_w_eq : analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 = ↑m := by
      apply le_antisymm
      · by_contra hgt; push_neg at hgt
        have h_succ : (↑(m + 1) : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 := by
          rwa [show (↑(m + 1) : ℕ∞) = ↑m + 1 from by push_cast; ring,
            ENat.add_one_le_iff (ENat.coe_ne_top m)]
        apply hw_f
        rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag f x₀ w m hf]
        exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (analyticAt_line_restriction f x₀ w hf)).mp h_succ) m (by omega)
      · exact hf_line w
    have hg_w_eq : analyticOrderAt (fun t : ℂ => g (x₀ + t • w)) 0 = ↑nn := by
      apply le_antisymm
      · by_contra hgt; push_neg at hgt
        have h_succ : (↑(nn + 1) : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => g (x₀ + t • w)) 0 := by
          rwa [show (↑(nn + 1) : ℕ∞) = ↑nn + 1 from by push_cast; ring,
            ENat.add_one_le_iff (ENat.coe_ne_top nn)]
        apply hw_g
        rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag g x₀ w nn hg]
        exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (analyticAt_line_restriction g x₀ w hg)).mp h_succ) nn (by omega)
      · exact hg_line w
    -- Product has analyticOrderAt = m + nn
    have hfg_w_eq : analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 =
        ↑(m + nn) := by
      calc analyticOrderAt (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0
          = analyticOrderAt (fun t => f (x₀ + t • w)) 0 +
            analyticOrderAt (fun t => g (x₀ + t • w)) 0 :=
            analyticOrderAt_mul (analyticAt_line_restriction f x₀ w hf)
              (analyticAt_line_restriction g x₀ w hg)
        _ = ↑m + ↑nn := by rw [hf_w_eq, hg_w_eq]
        _ = ↑(m + nn) := by push_cast; ring
    -- The (m+nn)-th iteratedDeriv of the line restriction is nonzero
    intro h_eq
    have h_diag_zero : (iteratedFDeriv ℂ (m + nn) (fun z => f z * g z) x₀) (fun _ => w) = 0 :=
      by simp [h_eq]
    rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag _ x₀ w _ hfg] at h_diag_zero
    -- But analyticOrderAt = m+nn means iteratedDeriv (m+nn) ≠ 0
    have h_below : ∀ i < m + nn + 1,
        iteratedDeriv i (fun t : ℂ => f (x₀ + t • w) * g (x₀ + t • w)) 0 = 0 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (analyticAt_line_restriction _ x₀ w hfg)).mp (le_of_eq hfg_w_eq.symm)) i hi'
      · exact hi' ▸ h_diag_zero
    have h_succ := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_line_restriction _ x₀ w hfg)).mpr h_below
    rw [hfg_w_eq] at h_succ
    exact absurd (by exact_mod_cast h_succ : m + nn + 1 ≤ m + nn) (by omega)
  exact le_antisymm h_le h_ge


/-! ## Upper semicontinuity of the analytic vanishing order (relocated from Lifting) -/

/-- Identity theorem for multi-variable analytic functions: if `f` is analytic on a
connected open set and not identically zero, then `f` has finite vanishing order everywhere.

The proof shows `{z ∈ U : order f z = ⊤}` is clopen: closed because it is
`⋂_n {iteratedFDeriv n f = 0}`, and open because at a point of infinite order the
power series is identically zero, so `f = 0` on a ball, hence all derivatives vanish
throughout that ball. -/
lemma order_ne_top_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU_conn : IsConnected U)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) :
    ∀ z ∈ U, order ℂ f z ≠ ⊤ := by
  -- Contrapositive: if order = ⊤ somewhere, f = 0 on all of U.
  by_contra hpush
  push_neg at hpush
  obtain ⟨z₀, hz₀, hord⟩ := hpush
  -- order = ⊤ means all iteratedFDeriv vanish at z₀
  have hderiv_zero : ∀ n, iteratedFDeriv ℂ n f z₀ = 0 :=
    (order_eq_top_iff (𝕜 := ℂ)).mp hord
  -- f is analytic at z₀, so it has a convergent power series
  obtain ⟨p, r, hp⟩ := hf z₀ hz₀
  -- All terms of ∑ (n!)⁻¹ • iteratedFDeriv n f z₀ (fun _ => y) vanish
  -- so the sum (= f(z₀ + y)) is 0 for y near 0
  have hf_zero : f =ᶠ[𝓝 z₀] 0 := by
    rw [eventuallyEq_iff_exists_mem]
    refine ⟨{z | z - z₀ ∈ Metric.eball 0 r}, ?_, fun z hz => ?_⟩
    · apply mem_nhds_iff.mpr
      refine ⟨{z | z - z₀ ∈ Metric.eball 0 r}, le_refl _, ?_, ?_⟩
      · exact Metric.isOpen_eball.preimage (continuous_id.sub continuous_const)
      · simp [Metric.mem_eball, hp.r_pos]
    · have hsum := hp.hasSum_iteratedFDeriv hz
      simp only [hderiv_zero, ContinuousMultilinearMap.zero_apply, smul_zero,] at hsum
      rw [show z₀ + (z - z₀) = z from by abel] at hsum
      exact hsum.unique hasSum_zero
  -- By identity principle: f = 0 on all of U
  have hf_eq : Set.EqOn f 0 U :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_conn.isPreconnected hz₀ hf_zero
  -- This contradicts the existence of z with f z ≠ 0
  obtain ⟨z, hzU, hfz⟩ := hne
  exact hfz (hf_eq hzU)

/-- Upper semi-continuity of vanishing order: `{z ∈ U | order f z ≤ n}` is open
for `f` analytic on open `U`. At a point where `order ≤ n`, some `iteratedFDeriv k f`
is nonzero. By continuity of `iteratedFDeriv` (analytic ⟹ C^∞), this persists nearby. -/
lemma isOpen_order_le_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU_open : IsOpen U)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U) (n : ℕ∞) :
    IsOpen {z ∈ U | order ℂ f z ≤ n} := by
  -- Handle n = ⊤: {order ≤ ⊤} = U, which is open
  rcases eq_or_ne n ⊤ with rfl | hn_ne
  · convert hU_open using 1; ext z; simp
  apply isOpen_iff_forall_mem_open.mpr
  intro z₀ ⟨hz₀U, hz₀_le⟩
  -- order ℂ f z₀ ≤ n < ⊤ means order is finite
  have hfin : ∃ m, iteratedFDeriv ℂ m f z₀ ≠ 0 := by
    rw [order] at hz₀_le
    split_ifs at hz₀_le with h
    · exact h
    · exact absurd (le_antisymm hz₀_le le_top).symm hn_ne
  set k := Nat.find hfin
  have hk_ne : iteratedFDeriv ℂ k f z₀ ≠ 0 := Nat.find_spec hfin
  have hk_le : (k : ℕ∞) ≤ n := by
    have hord : order ℂ f z₀ = ↑k := by rw [order, dif_pos hfin]
    rw [← hord]; exact hz₀_le
  -- U ∩ {iteratedFDeriv k f ≠ 0} is open and contains z₀
  have hcont : ContinuousOn (iteratedFDeriv ℂ k f) U :=
    (hf.iteratedFDeriv_of_isOpen hU_open k).continuousOn
  set W := U ∩ (iteratedFDeriv ℂ k f) ⁻¹' {x | x ≠ 0}
  have hW_open : IsOpen W := hcont.isOpen_inter_preimage hU_open isOpen_ne
  have hW_sub : W ⊆ {z ∈ U | order ℂ f z ≤ n} := by
    intro z ⟨hzU, hzk⟩
    refine ⟨hzU, le_trans ?_ hk_le⟩
    rw [order, dif_pos ⟨k, hzk⟩]
    exact Nat.cast_le.mpr (Nat.find_min' _ hzk)
  exact ⟨W, hW_sub, hW_open, hz₀U, hk_ne⟩

/-- The set `{z ∈ U | order f z < b}` is open for `f` analytic on open `U`. -/
lemma isOpen_order_lt_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU_open : IsOpen U)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U) (b : ℕ∞) :
    IsOpen {z ∈ U | order ℂ f z < b} := by
  -- {order < b} = ⋃ (n : ℕ) (hn : ↑n < b), {order ≤ n} (since order takes values in ℕ∞)
  -- But more directly: at z₀ with order < b, order(z₀) = k for some k < b.
  -- Then {order ≤ k} ∩ U is open (isOpen_order_le_inter) and z₀ ∈ it ⊆ {order < b}.
  apply isOpen_iff_forall_mem_open.mpr
  intro z₀ ⟨hz₀U, hz₀_lt⟩
  have hfin : order ℂ f z₀ ≠ ⊤ := ne_top_of_lt hz₀_lt
  set k := (order ℂ f z₀).toNat
  have hk : order ℂ f z₀ = ↑k := (ENat.coe_toNat hfin).symm
  refine ⟨{z ∈ U | order ℂ f z ≤ ↑k}, fun z ⟨hzU, hle⟩ => ⟨hzU, lt_of_le_of_lt hle ?_⟩,
         isOpen_order_le_inter U hU_open f hf ↑k, hz₀U, hk ▸ le_refl _⟩
  rw [← hk]; exact hz₀_lt

/-- The vanishing order of a power: `order(fᵐ) = m · order f` for `f` analytic (over `ℂ`). -/
theorem order_pow_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ : E) (hf : AnalyticAt ℂ f x₀) (m : ℕ) :
    order ℂ (fun z => (f z) ^ m) x₀ = (m : ℕ∞) * order ℂ f x₀ := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    have h0 : order ℂ (fun _ : E => (1 : ℂ)) x₀ = ((0 : ℕ) : ℕ∞) := by
      rw [order_eq_natCast_iff]
      refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), fun h => ?_⟩
      have h1 : (iteratedFDeriv ℂ 0 (fun _ : E => (1 : ℂ)) x₀) (fun _ => 0) = 1 := by
        simp [iteratedFDeriv_zero_apply]
      rw [h] at h1; simp at h1
    simpa using h0
  | succ k ih =>
    have hpow : (fun z => (f z) ^ (k + 1)) = (fun z => f z * (f z) ^ k) := by
      funext z; rw [pow_succ]; ring
    rw [hpow, order_mul_analytic f (fun z => (f z) ^ k) x₀ hf (hf.pow k), ih,
      Nat.cast_succ, add_mul, one_mul, add_comm]

/-- A nonzero constant function has vanishing order `0`. -/
theorem order_const_analytic_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (hc : c ≠ 0) (x : E) :
    order ℂ (fun _ : E => c) x = 0 := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, order_eq_natCast_iff]
  refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), fun h => ?_⟩
  have h1 : (iteratedFDeriv ℂ 0 (fun _ : E => c) x) (fun _ => 0) = c := by
    simp [iteratedFDeriv_zero_apply]
  rw [h] at h1; simp only [ContinuousMultilinearMap.zero_apply] at h1
  exact hc h1.symm

/-- Multiplying by a nonzero constant does not change the vanishing order (for analytic `f`). -/
theorem order_const_mul_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (hc : c ≠ 0) (f : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) :
    order ℂ (fun z => c * f z) x = order ℂ f x := by
  rw [order_mul_analytic (fun _ => c) f x analyticAt_const hf,
    order_const_analytic_ne c hc x, zero_add]

/-- A function not vanishing at `x` has vanishing order `0` there (no analyticity needed). -/
theorem order_eq_zero_of_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x : E) (hf : f x ≠ 0) :
    order ℂ f x = 0 := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, order_eq_natCast_iff]
  refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), fun h => ?_⟩
  have h1 : (iteratedFDeriv ℂ 0 f x) (fun _ => 0) = f x := by
    simp [iteratedFDeriv_zero_apply]
  rw [h] at h1; simp only [ContinuousMultilinearMap.zero_apply] at h1
  exact hf h1.symm

/-- **L2 (order under an analytic unit).** Multiplying by an analytic factor `u` that does not
vanish at `x` does not change the vanishing order: `order(u·f) = order f`. This is the order-transport
step `order(g) = order(h)` from the Weierstrass factorization `g = u·h` with `u(graph point) ≠ 0`.
Generalizes `order_const_mul_analytic` from a constant to an analytic unit. -/
theorem order_unit_mul_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u f : E → ℂ) (x : E) (hu : AnalyticAt ℂ u x) (hu0 : u x ≠ 0) (hf : AnalyticAt ℂ f x) :
    order ℂ (fun z => u z * f z) x = order ℂ f x := by
  rw [order_mul_analytic u f x hu hf, order_eq_zero_of_ne u x hu0, zero_add]

/-! ## Reverse factor bridge for the analytic order along a preconnected set (Phase D3 core) -/

/-- **Analytic reverse factor bridge.** If `f, g` are holomorphic and not identically zero on a
connected open `U`, and `f · g` has **constant vanishing order along a preconnected subset `S ⊆ U`**
(with basepoint `z₀ ∈ S`), then `f` and `g` *each* have constant order along `S`.

This is the holomorphic, *preconnected-but-not-open* analogue of `order_invariant_factor_of_mul`
(which is for `polyOrder` on `MvPolynomial`) and of `order_additivity_holomorphic` (which is the
`S = U` open case). It is the engine of Phase D3: the witness forces `order(P)` constant along the
section, the norm identity gives `P^m = ±disc(h)·Q`, and this bridge peels off `disc(h)`.

Proof: finite order on `U` (identity theorem), additivity `order(f·g) = order f + order g` at each
section point (`order_mul_analytic`), then the connectivity argument with the open superlevel sets
`{order f ≤ a}`, `{order g < b}` and `IsPreconnected S`. -/
theorem order_factor_const_of_mul_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {S : Set E} (hS_conn : IsPreconnected S) (hSU : S ⊆ U)
    (f g : E → ℂ)
    (hf_an : AnalyticOnNhd ℂ f U) (hg_an : AnalyticOnNhd ℂ g U)
    (hf_ne : ∃ z ∈ U, f z ≠ 0) (hg_ne : ∃ z ∈ U, g z ≠ 0)
    (z₀ : E) (hz₀S : z₀ ∈ S)
    (hfg_const : ∀ z ∈ S,
      order ℂ (fun w => f w * g w) z = order ℂ (fun w => f w * g w) z₀) :
    (∀ z ∈ S, order ℂ f z = order ℂ f z₀) ∧
    (∀ z ∈ S, order ℂ g z = order ℂ g z₀) := by
  have hf_fin : ∀ z ∈ U, order ℂ f z ≠ ⊤ :=
    order_ne_top_of_ne_zero U hU_conn f hf_an hf_ne
  have hg_fin : ∀ z ∈ U, order ℂ g z ≠ ⊤ :=
    order_ne_top_of_ne_zero U hU_conn g hg_an hg_ne
  set c := order ℂ (fun w => f w * g w) z₀ with hc
  have hsum_eq : ∀ z ∈ S, order ℂ f z + order ℂ g z = c := by
    intro z hz
    rw [← order_mul_analytic f g z (hf_an z (hSU hz)) (hg_an z (hSU hz))]
    exact hfg_const z hz
  set a := order ℂ f z₀ with ha
  set b := order ℂ g z₀ with hb
  have hab : a + b = c := hsum_eq z₀ hz₀S
  have ha_ne : a ≠ ⊤ := hf_fin z₀ (hSU hz₀S)
  have hb_ne : b ≠ ⊤ := hg_fin z₀ (hSU hz₀S)
  have sum_transfer_fg : ∀ z ∈ S, a < order ℂ f z → order ℂ g z < b := by
    intro z hz hlt
    have hsz := hsum_eq z hz; rw [← hab] at hsz
    have h1 : a + order ℂ g z < order ℂ f z + order ℂ g z :=
      (ENat.add_lt_add_iff_right (hg_fin z (hSU hz))).mpr hlt
    rw [hsz] at h1
    exact (ENat.add_lt_add_iff_left ha_ne).mp h1
  have sum_transfer_gf : ∀ z ∈ S, b < order ℂ g z → order ℂ f z < a := by
    intro z hz hlt
    have hsz := hsum_eq z hz; rw [← hab] at hsz
    have h1 : order ℂ f z + b < order ℂ f z + order ℂ g z :=
      (ENat.add_lt_add_iff_left (hf_fin z (hSU hz))).mpr hlt
    rw [hsz] at h1
    exact (ENat.add_lt_add_iff_right hb_ne).mp h1
  have hf_le : ∀ z ∈ S, order ℂ f z ≤ a := by
    by_contra hpush; push_neg at hpush
    obtain ⟨z₁, hz₁, hlt⟩ := hpush
    set A' := {z ∈ U | order ℂ f z ≤ a}
    set B' := {z ∈ U | order ℂ g z < b}
    have hA'_open := isOpen_order_le_inter U hU_open f hf_an a
    have hB'_open := isOpen_order_lt_inter U hU_open g hg_an b
    have hcov : S ⊆ A' ∪ B' := by
      intro z hz
      by_cases h : order ℂ f z ≤ a
      · exact Or.inl ⟨hSU hz, h⟩
      · exact Or.inr ⟨hSU hz, sum_transfer_fg z hz (not_le.mp h)⟩
    obtain ⟨z, hzS, ⟨_, hle_a⟩, _, hlt_b⟩ := hS_conn A' B' hA'_open hB'_open hcov
      ⟨z₀, hz₀S, hSU hz₀S, le_refl a⟩
      ⟨z₁, hz₁, hSU hz₁, sum_transfer_fg z₁ hz₁ hlt⟩
    have hsz := hsum_eq z hzS; rw [← hab] at hsz
    have hlt2 : order ℂ f z + order ℂ g z < a + b :=
      lt_of_le_of_lt ((ENat.add_le_add_iff_right (hg_fin z (hSU hzS))).mpr hle_a)
        ((ENat.add_lt_add_iff_left ha_ne).mpr hlt_b)
    exact absurd hsz (ne_of_lt hlt2)
  have hg_le : ∀ z ∈ S, order ℂ g z ≤ b := by
    by_contra hpush; push_neg at hpush
    obtain ⟨z₁, hz₁, hlt⟩ := hpush
    set A' := {z ∈ U | order ℂ g z ≤ b}
    set B' := {z ∈ U | order ℂ f z < a}
    have hA'_open := isOpen_order_le_inter U hU_open g hg_an b
    have hB'_open := isOpen_order_lt_inter U hU_open f hf_an a
    have hcov : S ⊆ A' ∪ B' := by
      intro z hz
      by_cases h : order ℂ g z ≤ b
      · exact Or.inl ⟨hSU hz, h⟩
      · exact Or.inr ⟨hSU hz, sum_transfer_gf z hz (not_le.mp h)⟩
    obtain ⟨z, hzS, ⟨_, hle_b⟩, _, hlt_a⟩ := hS_conn A' B' hA'_open hB'_open hcov
      ⟨z₀, hz₀S, hSU hz₀S, le_refl b⟩
      ⟨z₁, hz₁, hSU hz₁, sum_transfer_gf z₁ hz₁ hlt⟩
    have hsz := hsum_eq z hzS; rw [← hab] at hsz
    have hlt2 : order ℂ f z + order ℂ g z < a + b :=
      lt_of_lt_of_le ((ENat.add_lt_add_iff_right (hg_fin z (hSU hzS))).mpr hlt_a)
        ((ENat.add_le_add_iff_left ha_ne).mpr hle_b)
    exact absurd hsz (ne_of_lt hlt2)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hge : a ≤ order ℂ f z := by
      have hsz := hsum_eq z hz; rw [← hab] at hsz
      exact (ENat.add_le_add_iff_right (hg_fin z (hSU hz))).mp
        (hsz ▸ (ENat.add_le_add_iff_left ha_ne).mpr (hg_le z hz))
    exact le_antisymm (hf_le z hz) hge
  · have hge : b ≤ order ℂ g z := by
      have hsz := hsum_eq z hz; rw [← hab] at hsz
      exact (ENat.add_le_add_iff_left (hf_fin z (hSU hz))).mp
        (hsz ▸ (ENat.add_le_add_iff_right hb_ne).mpr (hf_le z hz))
    exact le_antisymm (hg_le z hz) hge

end
