import Cad.Multivariate.ProjectionTheorem.DiscrMul
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiFactorization
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassResAnalytic
import Cad.Multivariate.ProjectionTheorem.Generalized.PolyOfFamily
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic
import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticGerm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A5 (resultant coincidence) — the algebraic engine

The proof of A5 (`irreducible_factors_section_share_root`) runs through the **discriminant**: for a
factorization `h = ∏ⱼ facⱼ`, the discriminant `disc(h)` carries `res(facᵢ, facⱼ)²` as a factor
(McCallum 2.3.3, `discr_mul_eq`, applied twice). Since `disc(h)` is order-invariant along the section
(hypothesis) and `res(facᵢ,facⱼ)` vanishes at the base point (the factors are `Xᵈ` there, sharing the
root `0`), the order-invariance descends (project's `order_factor_const_of_mul_analytic`) to force
`res(facᵢ,facⱼ) = 0` on the whole section — i.e. the factors share a root.

This file builds the **algebraic engine**: the polynomial identity
`disc(∏ facₗ) = res(facᵢ,facⱼ)² · Q` with an explicit analytic-friendly cofactor `Q`.
-/

noncomputable section

open Polynomial Finset Filter
open scoped Topology

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- A finite product of monic polynomials is monic. -/
private lemma monic_prod_fin {k : ℕ} (fac : Fin k → R[X]) (s : Finset (Fin k))
    (hmonic : ∀ l, (fac l).Monic) : (∏ l ∈ s, fac l).Monic :=
  monic_prod_of_monic s fac fun l _ => hmonic l

/-- **Discriminant factorization (the A5 engine).** For a product of monic, positive-degree
polynomials and two distinct indices `i ≠ j`, the discriminant of the product equals
`res(facᵢ, facⱼ)²` times an explicit cofactor. -/
theorem discr_prod_eq_resultant_sq_mul {k : ℕ} (fac : Fin k → R[X])
    (hmonic : ∀ l, (fac l).Monic) (hpos : ∀ l, 0 < (fac l).natDegree)
    (i j : Fin k) (hij : i ≠ j) :
    (∏ l, fac l).discr
      = resultant (fac i) (fac j) ^ 2 *
          ((fac i).discr * resultant (fac i) (∏ l ∈ (univ.erase i).erase j, fac l) ^ 2 *
            (∏ l ∈ univ.erase i, fac l).discr) := by
  set P := ∏ l ∈ univ.erase i, fac l with hP
  set P' := ∏ l ∈ (univ.erase i).erase j, fac l with hP'
  have hj_mem : j ∈ univ.erase i := mem_erase.mpr ⟨(Ne.symm hij), mem_univ j⟩
  -- degree/positivity facts
  have hP'_monic : P'.Monic := monic_prod_fin fac _ hmonic
  have hP_pos : 0 < P.natDegree := by
    rw [hP, Polynomial.natDegree_prod _ _ fun l _ => (hmonic l).ne_zero]
    exact Finset.sum_pos' (fun l _ => Nat.zero_le _) ⟨j, hj_mem, hpos j⟩
  -- split the whole product as `facᵢ * P`
  have hsplit : (∏ l, fac l) = fac i * P := (Finset.mul_prod_erase univ fac (mem_univ i)).symm
  -- split `P` as `facⱼ * P'`
  have hP_eq : P = fac j * P' := (Finset.mul_prod_erase (univ.erase i) fac hj_mem).symm
  have hPnd : P.natDegree = (fac j).natDegree + P'.natDegree := by
    rw [hP_eq, Polynomial.natDegree_mul (hmonic j).ne_zero hP'_monic.ne_zero]
  -- `disc(facᵢ · P) = disc(facᵢ) · res(facᵢ,P)² · disc(P)`
  have hstep1 : (∏ l, fac l).discr
      = (fac i).discr * resultant (fac i) P ^ 2 * P.discr := by
    rw [hsplit, discr_mul_eq (fac i) P (hpos i) hP_pos]
  -- `res(facᵢ, P) = res(facᵢ, facⱼ) · res(facᵢ, P')`
  have hres : resultant (fac i) P = resultant (fac i) (fac j) * resultant (fac i) P' := by
    have h := resultant_mul_right (fac i) (fac j) P' (fac i).natDegree le_rfl
    -- the LHS `resultant facᵢ P` has default `n = P.natDegree = facⱼ.natDegree + P'.natDegree`
    rw [show resultant (fac i) P = resultant (fac i) (fac j * P') (fac i).natDegree
          ((fac j).natDegree + P'.natDegree) by rw [hP_eq]; rw [← hPnd, hP_eq], h]
  rw [hstep1, hres]
  ring

/-- **Discriminant factorization (the A4 engine).** For a product of monic, positive-degree
polynomials with `k ≥ 2`, the discriminant of the product carries `disc(facⱼ)` as a factor. -/
theorem discr_prod_eq_disc_mul {k : ℕ} (fac : Fin k → R[X])
    (hmonic : ∀ l, (fac l).Monic) (hpos : ∀ l, 0 < (fac l).natDegree)
    (j : Fin k) (hk2 : 2 ≤ k) :
    (∏ l, fac l).discr
      = (fac j).discr *
          (resultant (fac j) (∏ l ∈ univ.erase j, fac l) ^ 2 * (∏ l ∈ univ.erase j, fac l).discr) := by
  set P := ∏ l ∈ univ.erase j, fac l with hP
  have hP_monic : P.Monic := monic_prod_fin fac _ hmonic
  have hP_pos : 0 < P.natDegree := by
    obtain ⟨l, hl⟩ : (univ.erase j).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ j), Finset.card_univ,
        Fintype.card_fin]; omega
    rw [hP, Polynomial.natDegree_prod _ _ fun l _ => (hmonic l).ne_zero]
    exact Finset.sum_pos' (fun l _ => Nat.zero_le _) ⟨l, hl, hpos l⟩
  have hsplit : (∏ l, fac l) = fac j * P := (Finset.mul_prod_erase univ fac (mem_univ j)).symm
  rw [hsplit, discr_mul_eq (fac j) P (hpos j) hP_pos]; ring

/-- At the base point the factors are `X^{dᵢ}`, `X^{dⱼ}` (positive degree), which share the root `0`,
so their resultant vanishes. -/
lemma resultant_X_pow_eq_zero {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    resultant (X ^ a : ℂ[X]) (X ^ b) = 0 := by
  rw [show resultant (X ^ a : ℂ[X]) (X ^ b) = (X ^ a : ℂ[X]).resultant (X ^ b) a b by
        rw [natDegree_X_pow, natDegree_X_pow],
    resultant_X_pow_left (X ^ b : ℂ[X]) a b (by rw [natDegree_X_pow]),
    Polynomial.coeff_X_pow, if_neg (by omega), zero_pow (by omega)]

/-- **Vanishing resultant ⟹ shared root.** For a monic `f` over `ℂ`, if `res(f, g) = 0` then `f` and
`g` have a common root (Vieta: the resultant is `∏_{r ∈ roots f} g(r)`). -/
lemma share_root_of_resultant_zero {f g : ℂ[X]} (hf : f.Monic) (hres : resultant f g = 0) :
    ∃ β : ℂ, f.IsRoot β ∧ g.IsRoot β := by
  have heq : resultant f g = f.leadingCoeff ^ g.natDegree * (f.roots.map g.eval).prod :=
    resultant_eq_prod_eval f g g.natDegree le_rfl (IsAlgClosed.splits f)
  rw [hf.leadingCoeff, one_pow, one_mul] at heq
  have hprod : (f.roots.map g.eval).prod = 0 := heq.symm.trans hres
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨r, hr_mem, hr_eval⟩ := hprod
  exact ⟨r, isRoot_of_mem_roots hr_mem, hr_eval⟩

/-! ### Analyticity of the family resultant -/

section Analytic

variable {s e : ℕ}

/-- Evaluating the function-ring polynomial `polyOfFamily N gℂ` at a parameter `w` recovers the
section polynomial `gℂ w` (when `N` bounds the degree). -/
lemma polyOfFamily_map (N : ℕ) (gℂ : CParam s e → Polynomial ℂ) (w : CParam s e)
    (hdeg : (gℂ w).natDegree ≤ N) :
    (polyOfFamily N gℂ).map (Pi.evalRingHom (fun _ => ℂ) w) = gℂ w := by
  ext j
  rw [Polynomial.coeff_map, polyOfFamily_coeff]
  by_cases hj : j ≤ N
  · simp only [if_pos hj]; rfl
  · simp only [if_neg hj, map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- `polyOfFamily` of a family with analytic coefficient functions has analytic coefficients. -/
lemma analyticCoeffs_polyOfFamily (N : ℕ) (gℂ : CParam s e → Polynomial ℂ)
    (hc : ∀ i, AnalyticAt ℂ (fun w => (gℂ w).coeff i) 0) :
    AnalyticCoeffs (polyOfFamily N gℂ) := by
  intro i
  rw [polyOfFamily_coeff]
  by_cases hi : i ≤ N
  · simpa only [if_pos hi] using hc i
  · simpa only [if_neg hi] using (analyticAt_const : AnalyticAt ℂ (fun _ : CParam s e => (0 : ℂ)) 0)

/-- **The resultant of two analytic families is analytic.** If `H₁, H₂ : CParam → ℂ[X]` have
coefficient functions analytic at `0` and degrees bounded by `N₁, N₂`, then
`w ↦ res(H₁ w, H₂ w)` (with the fixed degree windows `N₁, N₂`) is analytic at `0`. Proved via the
`toSubring` + `resultant_map_map` technique (cf. `weierstrassResFun_analyticAt`). -/
lemma familyResultant_analyticAt (H₁ H₂ : CParam s e → Polynomial ℂ) (N₁ N₂ : ℕ)
    (hc₁ : ∀ i, AnalyticAt ℂ (fun w => (H₁ w).coeff i) 0)
    (hc₂ : ∀ i, AnalyticAt ℂ (fun w => (H₂ w).coeff i) 0)
    (hdeg₁ : ∀ w, (H₁ w).natDegree ≤ N₁) (hdeg₂ : ∀ w, (H₂ w).natDegree ≤ N₂) :
    AnalyticAt ℂ (fun w => resultant (H₁ w) (H₂ w) N₁ N₂) 0 := by
  set S := AnalyticAtSubring s e
  set P₁ := polyOfFamily N₁ H₁
  set P₂ := polyOfFamily N₂ H₂
  have hAC₁ : AnalyticCoeffs P₁ := analyticCoeffs_polyOfFamily N₁ H₁ hc₁
  have hAC₂ : AnalyticCoeffs P₂ := analyticCoeffs_polyOfFamily N₂ H₂ hc₂
  have hfun_eq : (fun w => resultant (H₁ w) (H₂ w) N₁ N₂) = resultant P₁ P₂ N₁ N₂ := by
    funext w
    have hm := Polynomial.resultant_map_map P₁ P₂ N₁ N₂ (Pi.evalRingHom (fun _ => ℂ) w)
    rw [polyOfFamily_map N₁ H₁ w (hdeg₁ w), polyOfFamily_map N₂ H₂ w (hdeg₂ w)] at hm
    exact hm
  rw [hfun_eq]
  have hsub : resultant P₁ P₂ N₁ N₂
      = S.subtype (resultant (P₁.toSubring S hAC₁.coeffs_subset) (P₂.toSubring S hAC₂.coeffs_subset)
          N₁ N₂) := by
    have hr := Polynomial.resultant_map_map (P₁.toSubring S hAC₁.coeffs_subset)
      (P₂.toSubring S hAC₂.coeffs_subset) N₁ N₂ S.subtype
    rw [map_toSubring, map_toSubring] at hr
    exact hr
  rw [hsub]
  exact (resultant (P₁.toSubring S hAC₁.coeffs_subset) (P₂.toSubring S hAC₂.coeffs_subset) N₁ N₂).2

/-- The coefficients of a finite product of analytic families are analytic. -/
lemma analyticCoeffs_prodFamily {ι : Type*} (t : Finset ι)
    (fac : ι → CParam s e → Polynomial ℂ)
    (hc : ∀ l i, AnalyticAt ℂ (fun w => (fac l w).coeff i) 0) :
    ∀ i, AnalyticAt ℂ (fun w => (∏ l ∈ t, fac l w).coeff i) 0 := by
  classical
  induction t using Finset.induction with
  | empty => intro i; simpa only [Finset.prod_empty] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : CParam s e => (1 : Polynomial ℂ).coeff i) 0)
  | insert a t ha IH =>
    intro i
    have hrw : (fun w => (∏ l ∈ insert a t, fac l w).coeff i)
        = fun w => ∑ x ∈ Finset.antidiagonal i,
            (fac a w).coeff x.1 * (∏ l ∈ t, fac l w).coeff x.2 := by
      funext w; rw [Finset.prod_insert ha, Polynomial.coeff_mul]
    rw [hrw]
    exact Finset.analyticAt_fun_sum _ fun x _ => (hc a x.1).mul (IH x.2)

/-- The discriminant of a monic analytic family of constant positive degree is analytic. -/
lemma familyDiscr_analyticAt (H : CParam s e → Polynomial ℂ) (d : ℕ) (hd : 0 < d)
    (hmonic : ∀ w, (H w).Monic) (hdeg : ∀ w, (H w).natDegree = d)
    (hc : ∀ i, AnalyticAt ℂ (fun w => (H w).coeff i) 0) :
    AnalyticAt ℂ (fun w => (H w).discr) 0 := by
  have hkey : (fun w => (H w).discr)
      = fun w => (-1 : ℂ) ^ (d * (d - 1) / 2)
          * resultant (H w) (derivative (H w)) d (d - 1) := by
    funext w
    have hpos : 0 < (H w).degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hdeg w]; exact hd)
    have hrd : resultant (H w) (derivative (H w)) d (d - 1)
        = (-1 : ℂ) ^ (d * (d - 1) / 2) * (H w).discr := by
      have h := resultant_deriv hpos
      rw [hdeg w, (hmonic w).leadingCoeff, mul_one] at h
      exact h
    rw [hrd, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hkey]
  refine analyticAt_const.mul (familyResultant_analyticAt H (fun w => derivative (H w)) d (d - 1)
    hc (fun i => ?_) (fun w => (hdeg w).le) (fun w => ?_))
  · have hrw : (fun w => (derivative (H w)).coeff i)
        = fun w => (H w).coeff (i + 1) * ((i : ℂ) + 1) := by
      funext w; rw [Polynomial.coeff_derivative]
    rw [hrw]; exact (hc (i + 1)).mul analyticAt_const
  · have h1 := Polynomial.natDegree_derivative_le (H w)
    rw [hdeg w] at h1; exact h1

/-- If `f` vanishes at `x`, its analytic order there is nonzero. -/
lemma order_ne_zero_of_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : F → ℂ) (x : F) (hf : f x = 0) : order ℂ f x ≠ 0 := by
  intro h
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, order_eq_natCast_iff] at h
  refine h.2 ?_
  ext v
  simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply]
  exact hf

/-- **The order-invariance descent (A5 capstone).** Let `D = R² · Q` on a connected open `U`, with
`R, Q` analytic and not identically zero. If `D` has constant vanishing order along the section
`{(y,0) : y ∈ V}` (`V` preconnected), and `R` vanishes at the base point `(0,0)`, then `R` vanishes on
the whole section. (Order-invariance of `D` descends to `R²` via `order_factor_const_of_mul_analytic`;
constancy plus `R²(0,0)=0` forces `R²`, hence `R`, to vanish along the section.) -/
theorem factor_vanishes_on_section
    (R Q D : CParam s e → ℂ)
    {U : Set (CParam s e)} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {V : Set (Fin s → ℂ)} (hV_conn : IsPreconnected V) (hV0 : (0 : Fin s → ℂ) ∈ V)
    (hVU : ∀ y ∈ V, ((y, 0) : CParam s e) ∈ U)
    (hR_an : AnalyticOnNhd ℂ R U) (hQ_an : AnalyticOnNhd ℂ Q U)
    (hR_ne : ∃ z ∈ U, R z ≠ 0) (hQ_ne : ∃ z ∈ U, Q z ≠ 0)
    (hD : ∀ z ∈ U, D z = R z ^ 2 * Q z)
    (hD_oi : ∀ y ∈ V, order ℂ D ((y, 0) : CParam s e) = order ℂ D ((0, 0) : CParam s e))
    (hR0 : R ((0, 0) : CParam s e) = 0) :
    ∀ y ∈ V, R ((y, 0) : CParam s e) = 0 := by
  set ι : (Fin s → ℂ) → CParam s e := fun y => (y, 0) with hι
  have hι_cont : Continuous ι := by fun_prop
  set S : Set (CParam s e) := ι '' V with hS
  have hS_conn : IsPreconnected S := hV_conn.image ι hι_cont.continuousOn
  have hSU : S ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hVU y hy
  have hz₀S : ((0, 0) : CParam s e) ∈ S := ⟨0, hV0, rfl⟩
  have hf_an : AnalyticOnNhd ℂ (fun w => R w ^ 2) U := fun z hz => (hR_an z hz).pow 2
  have hf_ne : ∃ z ∈ U, R z ^ 2 ≠ 0 := by
    obtain ⟨z, hz, hzne⟩ := hR_ne; exact ⟨z, hz, pow_ne_zero 2 hzne⟩
  have hfg_const : ∀ z ∈ S, order ℂ (fun w => R w ^ 2 * Q w) z
      = order ℂ (fun w => R w ^ 2 * Q w) ((0, 0) : CParam s e) := by
    have heq : ∀ z ∈ U, order ℂ (fun w => R w ^ 2 * Q w) z = order ℂ D z := fun z hz =>
      order_congr_of_eventuallyEq' (by
        filter_upwards [hU_open.mem_nhds hz] with w hw using (hD w hw).symm)
    rintro _ ⟨y, hy, rfl⟩
    rw [heq _ (hVU y hy), heq _ (hVU 0 hV0), hD_oi y hy]
  have hbridge := (order_factor_const_of_mul_analytic hU_open hU_conn hS_conn hSU
    (fun w => R w ^ 2) Q hf_an hQ_an hf_ne hQ_ne ((0, 0) : CParam s e) hz₀S hfg_const).1
  intro y hy
  have hconst := hbridge (ι y) ⟨y, hy, rfl⟩
  have hord0 : order ℂ (fun w => R w ^ 2) ((0, 0) : CParam s e) ≠ 0 :=
    order_ne_zero_of_eq_zero _ _ (by show R ((0, 0) : CParam s e) ^ 2 = 0; rw [hR0]; ring)
  have hord_y : order ℂ (fun w => R w ^ 2) (ι y) ≠ 0 := hconst ▸ hord0
  have hR2 : R (ι y) ^ 2 = 0 := by
    by_contra hne
    exact hord_y (order_eq_zero_of_ne _ _ hne)
  exact pow_eq_zero_iff (by norm_num) |>.mp hR2

/-- Explicit-degree resultant equals the default when the degrees match the natDegrees. -/
private lemma resultant_deg_eq {f g : Polynomial ℂ} {df dg : ℕ}
    (hf : f.natDegree = df) (hg : g.natDegree = dg) :
    resultant f g df dg = resultant f g := by rw [← hf, ← hg]

/-- **Order-invariance descent (A4 wiring).** If `D = f · g` on a connected open `U` with `f, g`
analytic and not identically zero, and `D` has constant order along the section `{(y,0) : y ∈ V}`
(`V` preconnected), then so does `f`. (Direct application of `order_factor_const_of_mul_analytic`.) -/
theorem factor_order_inv_on_section (f g D : CParam s e → ℂ)
    {U : Set (CParam s e)} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {V : Set (Fin s → ℂ)} (hV_conn : IsPreconnected V) (hV0 : (0 : Fin s → ℂ) ∈ V)
    (hVU : ∀ y ∈ V, ((y, 0) : CParam s e) ∈ U)
    (hf_an : AnalyticOnNhd ℂ f U) (hg_an : AnalyticOnNhd ℂ g U)
    (hf_ne : ∃ z ∈ U, f z ≠ 0) (hg_ne : ∃ z ∈ U, g z ≠ 0)
    (hD : ∀ z ∈ U, D z = f z * g z)
    (hD_oi : ∀ y ∈ V, order ℂ D ((y, 0) : CParam s e) = order ℂ D ((0, 0) : CParam s e)) :
    ∀ y ∈ V, order ℂ f ((y, 0) : CParam s e) = order ℂ f ((0, 0) : CParam s e) := by
  set ι : (Fin s → ℂ) → CParam s e := fun y => (y, 0) with hι
  have hι_cont : Continuous ι := by fun_prop
  set S : Set (CParam s e) := ι '' V with hS
  have hS_conn : IsPreconnected S := hV_conn.image ι hι_cont.continuousOn
  have hSU : S ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hVU y hy
  have hz₀S : ((0, 0) : CParam s e) ∈ S := ⟨0, hV0, rfl⟩
  have hfg_const : ∀ z ∈ S, order ℂ (fun w => f w * g w) z
      = order ℂ (fun w => f w * g w) ((0, 0) : CParam s e) := by
    have heq : ∀ z ∈ U, order ℂ (fun w => f w * g w) z = order ℂ D z := fun z hz =>
      order_congr_of_eventuallyEq' (by
        filter_upwards [hU_open.mem_nhds hz] with w hw using (hD w hw).symm)
    rintro _ ⟨y, hy, rfl⟩
    rw [heq _ (hVU y hy), heq _ (hVU 0 hV0), hD_oi y hy]
  have hbridge := (order_factor_const_of_mul_analytic hU_open hU_conn hS_conn hSU
    f g hf_an hg_an hf_ne hg_ne ((0, 0) : CParam s e) hz₀S hfg_const).1
  intro y hy
  exact hbridge (ι y) ⟨y, hy, rfl⟩

/-- **A5, per pair.** For two factors `facᵢ, facⱼ` of the discriminant-order-invariant factorization,
the section polynomials share a root for `y` near `0`. (`i=j`: any root; `i≠j`: the resultant vanishes
on the section by the discriminant order-invariance descent.) -/
theorem pair_share_root
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hfac_fam : ∀ l, IsWeierstrassFamily (fac l) (deg l)) (hdeg1 : ∀ l, 1 ≤ deg l)
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ l : Fin k, fac l w)
    (i j : Fin k) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ β : ℂ, (fac i ((y, 0) : CParam s e)).IsRoot β ∧ (fac j ((y, 0) : CParam s e)).IsRoot β := by
  rcases eq_or_ne i j with rfl | hij
  · -- `i = j`: any root of the (monic, positive-degree) section polynomial
    refine Filter.Eventually.of_forall fun y => ?_
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (p := fac i ((y, 0) : CParam s e))
      (by rw [Polynomial.degree_eq_natDegree ((hfac_fam i).monic _).ne_zero,
            (hfac_fam i).degree_eq]; exact_mod_cast (by have := hdeg1 i; omega : (deg i : ℕ) ≠ 0))
    exact ⟨β, hβ, hβ⟩
  · -- `i ≠ j`: resultant vanishes on the section
    set P' : CParam s e → Polynomial ℂ := fun w => ∏ l ∈ (univ.erase i).erase j, fac l w with hP'
    set Pf : CParam s e → Polynomial ℂ := fun w => ∏ l ∈ univ.erase i, fac l w with hPf
    set dP' : ℕ := ∑ l ∈ (univ.erase i).erase j, deg l with hdP'
    set dP : ℕ := ∑ l ∈ univ.erase i, deg l with hdP
    set Rf : CParam s e → ℂ := fun w => resultant (fac i w) (fac j w) with hRfd
    set Qf : CParam s e → ℂ :=
      fun w => (fac i w).discr * resultant (fac i w) (P' w) ^ 2 * (Pf w).discr with hQfd
    have hj_mem : j ∈ univ.erase i := mem_erase.mpr ⟨(Ne.symm hij), mem_univ j⟩
    -- analyticity of `P'`, `Pf`
    have hP'_ca : ∀ idx, AnalyticAt ℂ (fun w => (P' w).coeff idx) 0 :=
      analyticCoeffs_prodFamily _ fac fun l idx => (hfac_fam l).coeff_analyticAt idx
    have hPf_ca : ∀ idx, AnalyticAt ℂ (fun w => (Pf w).coeff idx) 0 :=
      analyticCoeffs_prodFamily _ fac fun l idx => (hfac_fam l).coeff_analyticAt idx
    have hP'_deg : ∀ w, (P' w).natDegree = dP' := fun w => by
      rw [hP', Polynomial.natDegree_prod _ _ fun l _ => ((hfac_fam l).monic w).ne_zero]
      exact Finset.sum_congr rfl fun l _ => (hfac_fam l).degree_eq w
    have hPf_deg : ∀ w, (Pf w).natDegree = dP := fun w => by
      rw [hPf, Polynomial.natDegree_prod _ _ fun l _ => ((hfac_fam l).monic w).ne_zero]
      exact Finset.sum_congr rfl fun l _ => (hfac_fam l).degree_eq w
    have hPf_monic : ∀ w, (Pf w).Monic := fun w => monic_prod_of_monic _ _ fun l _ => (hfac_fam l).monic w
    have hdP_pos : 0 < dP := by
      rw [hdP]; exact Finset.sum_pos' (fun l _ => Nat.zero_le _) ⟨j, hj_mem, hdeg1 j⟩
    -- analyticity of `Rf`, `Qf` (bridging default ↔ explicit degrees)
    have hRf_expl : Rf = fun w => resultant (fac i w) (fac j w) (deg i) (deg j) := by
      funext w
      exact (resultant_deg_eq ((hfac_fam i).degree_eq w) ((hfac_fam j).degree_eq w)).symm
    have hQf_expl : Qf = fun w =>
        (fac i w).discr * resultant (fac i w) (P' w) (deg i) dP' ^ 2 * (Pf w).discr := by
      funext w
      show (fac i w).discr * resultant (fac i w) (P' w) ^ 2 * (Pf w).discr = _
      rw [resultant_deg_eq ((hfac_fam i).degree_eq w) (hP'_deg w)]
    have hRan : AnalyticAt ℂ Rf 0 := by
      rw [hRf_expl]
      exact familyResultant_analyticAt (fac i) (fac j) (deg i) (deg j)
        (hfac_fam i).coeff_analyticAt (hfac_fam j).coeff_analyticAt
        (fun w => ((hfac_fam i).degree_eq w).le) (fun w => ((hfac_fam j).degree_eq w).le)
    have hQan : AnalyticAt ℂ Qf 0 := by
      rw [hQf_expl]
      refine (AnalyticAt.mul (AnalyticAt.mul ?_ ?_) ?_)
      · exact familyDiscr_analyticAt (fac i) (deg i) (by have := hdeg1 i; omega)
          (fun w => (hfac_fam i).monic w) (fun w => (hfac_fam i).degree_eq w)
          (hfac_fam i).coeff_analyticAt
      · exact (familyResultant_analyticAt (fac i) P' (deg i) dP' (hfac_fam i).coeff_analyticAt hP'_ca
          (fun w => ((hfac_fam i).degree_eq w).le) (fun w => (hP'_deg w).le)).pow 2
      · exact familyDiscr_analyticAt Pf dP hdP_pos hPf_monic hPf_deg hPf_ca
    -- `disc = Rf² · Qf` wherever the factorization holds (default degrees match the engine)
    have hDrel : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassDiscFn m a w = Rf w ^ 2 * Qf w := by
      filter_upwards [hfac_eq] with w hw
      show (weierstrassPoly m a w).discr = Rf w ^ 2 * Qf w
      rw [hw, discr_prod_eq_resultant_sq_mul (fun l => fac l w) (fun l => (hfac_fam l).monic w)
        (fun l => by rw [(hfac_fam l).degree_eq w]; exact hdeg1 l) i j hij]
    -- `disc` is analytic (from `Rf² · Qf`)
    have hDan : AnalyticAt ℂ (weierstrassDiscFn m a) 0 :=
      ((hRan.pow 2).mul hQan).congr (Filter.EventuallyEq.symm hDrel)
    -- a ball `U` where everything is analytic and the relation holds
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hRan.eventually_analyticAt.and hQan.eventually_analyticAt) hDrel)
    set U : Set (CParam s e) := Metric.ball 0 ε with hU
    have hU_open : IsOpen U := Metric.isOpen_ball
    have hU_conn : IsConnected U :=
      ⟨⟨0, Metric.mem_ball_self hε⟩, (convex_ball (0 : CParam s e) ε).isPreconnected⟩
    have hU_mem : U ∈ 𝓝 (0 : CParam s e) := hU_open.mem_nhds (Metric.mem_ball_self hε)
    have hRan_U : AnalyticOnNhd ℂ Rf U := fun z hz => (hball hz).1.1
    have hQan_U : AnalyticOnNhd ℂ Qf U := fun z hz => (hball hz).1.2
    have hD_U : ∀ z ∈ U, weierstrassDiscFn m a z = Rf z ^ 2 * Qf z := fun z hz => (hball hz).2
    -- `Qf ≢ 0` on `U` (else `disc ≡ 0`, contradicting `hdisc_ne`)
    have hQne : ∃ z ∈ U, Qf z ≠ 0 := by
      by_contra h; push_neg at h
      apply hdisc_ne
      apply order_eq_top_of_eventuallyEq_zero
      filter_upwards [hU_mem] with w hw
      show weierstrassDiscFn m a w = 0
      rw [hD_U w hw, h w hw, mul_zero]
    -- the section ball `V`
    have hsec_pre : (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) ⁻¹' U ∈ 𝓝 (0 : Fin s → ℂ) := by
      apply (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      simpa using hU_mem
    obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hsec_pre hdisc)
    set V : Set (Fin s → ℂ) := Metric.ball 0 δ with hV
    have hV_conn : IsPreconnected V := (convex_ball (0 : Fin s → ℂ) δ).isPreconnected
    have hV0 : (0 : Fin s → ℂ) ∈ V := Metric.mem_ball_self hδ
    have hV_mem : V ∈ 𝓝 (0 : Fin s → ℂ) := Metric.isOpen_ball.mem_nhds hV0
    have hVU : ∀ y ∈ V, ((y, 0) : CParam s e) ∈ U := fun y hy => (hδball hy).1
    have hD_oi : ∀ y ∈ V, order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s e) := fun y hy => (hδball hy).2
    -- `Rf (0,0) = 0` (the base point factors are `X^{deg}` and share root `0`)
    have hR00 : Rf ((0, 0) : CParam s e) = 0 := by
      show resultant (fac i ((0, 0) : CParam s e)) (fac j ((0, 0) : CParam s e)) = 0
      rw [show ((0, 0) : CParam s e) = 0 from rfl, (hfac_fam i).eval_zero, (hfac_fam j).eval_zero]
      exact resultant_X_pow_eq_zero (hdeg1 i) (hdeg1 j)
    -- conclude `∀ᶠ y, Rf (y,0) = 0`, then share a root
    suffices hres0 : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), Rf ((y, 0) : CParam s e) = 0 by
      filter_upwards [hres0] with y hy
      exact share_root_of_resultant_zero ((hfac_fam i).monic ((y, 0) : CParam s e)) hy
    by_cases hRne : ∃ z ∈ U, Rf z ≠ 0
    · filter_upwards [hV_mem] with y hy
      exact factor_vanishes_on_section Rf Qf (weierstrassDiscFn m a) hU_open hU_conn hV_conn hV0
        hVU hRan_U hQan_U hRne hQne hD_U hD_oi hR00 y hy
    · push_neg at hRne
      filter_upwards [hV_mem] with y hy
      exact hRne ((y, 0) : CParam s e) (hVU y hy)

/-- **A4 disc descent.** For a factorization with `k ≥ 2`, the discriminant of one factor `facⱼ` is
itself order-invariant along the section (and not identically zero near `0`), inheriting these from
`disc(weierstrassPoly)` via the factorization `disc(h) = disc(facⱼ) · (res(facⱼ,∏)²·disc(∏))`. -/
theorem factor_disc_order_inv
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hfac_fam : ∀ l, IsWeierstrassFamily (fac l) (deg l)) (hdeg1 : ∀ l, 1 ≤ deg l)
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ l : Fin k, fac l w)
    (j : Fin k) (hk2 : 2 ≤ k) :
    order ℂ (fun w => (fac j w).discr) (0 : CParam s e) ≠ ⊤ ∧
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
        = order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e) := by
  set P : CParam s e → Polynomial ℂ := fun w => ∏ l ∈ univ.erase j, fac l w with hP
  set dP : ℕ := ∑ l ∈ univ.erase j, deg l with hdP
  set Df : CParam s e → ℂ := fun w => (fac j w).discr with hDfd
  set Qf : CParam s e → ℂ := fun w => resultant (fac j w) (P w) ^ 2 * (P w).discr with hQfd
  have hP_ca : ∀ idx, AnalyticAt ℂ (fun w => (P w).coeff idx) 0 :=
    analyticCoeffs_prodFamily _ fac fun l idx => (hfac_fam l).coeff_analyticAt idx
  have hP_deg : ∀ w, (P w).natDegree = dP := fun w => by
    rw [hP, Polynomial.natDegree_prod _ _ fun l _ => ((hfac_fam l).monic w).ne_zero]
    exact Finset.sum_congr rfl fun l _ => (hfac_fam l).degree_eq w
  have hP_monic : ∀ w, (P w).Monic := fun w => monic_prod_of_monic _ _ fun l _ => (hfac_fam l).monic w
  have hdP_pos : 0 < dP := by
    obtain ⟨l, hl⟩ : (univ.erase j).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ j), Finset.card_univ,
        Fintype.card_fin]; omega
    rw [hdP]; exact Finset.sum_pos' (fun l _ => Nat.zero_le _) ⟨l, hl, hdeg1 l⟩
  -- analyticity of `Df`, `Qf`
  have hDf_an : AnalyticAt ℂ Df 0 := familyDiscr_analyticAt (fac j) (deg j) (by have := hdeg1 j; omega)
    (fun w => (hfac_fam j).monic w) (fun w => (hfac_fam j).degree_eq w) (hfac_fam j).coeff_analyticAt
  have hQf_expl : Qf = fun w => resultant (fac j w) (P w) (deg j) dP ^ 2 * (P w).discr := by
    funext w
    show resultant (fac j w) (P w) ^ 2 * (P w).discr = _
    rw [resultant_deg_eq ((hfac_fam j).degree_eq w) (hP_deg w)]
  have hQf_an : AnalyticAt ℂ Qf 0 := by
    rw [hQf_expl]
    exact (familyResultant_analyticAt (fac j) P (deg j) dP (hfac_fam j).coeff_analyticAt hP_ca
      (fun w => ((hfac_fam j).degree_eq w).le) (fun w => (hP_deg w).le)).pow 2
      |>.mul (familyDiscr_analyticAt P dP hdP_pos hP_monic hP_deg hP_ca)
  -- `disc(h) = Df · Qf` wherever the factorization holds
  have hDrel : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassDiscFn m a w = Df w * Qf w := by
    filter_upwards [hfac_eq] with w hw
    show (weierstrassPoly m a w).discr = Df w * Qf w
    rw [hw, discr_prod_eq_disc_mul (fun l => fac l w) (fun l => (hfac_fam l).monic w)
      (fun l => by rw [(hfac_fam l).degree_eq w]; exact hdeg1 l) j hk2]
  -- ball `U` where everything is analytic and the relation holds
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hDf_an.eventually_analyticAt.and hQf_an.eventually_analyticAt) hDrel)
  set U : Set (CParam s e) := Metric.ball 0 ε with hU
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_conn : IsConnected U :=
    ⟨⟨0, Metric.mem_ball_self hε⟩, (convex_ball (0 : CParam s e) ε).isPreconnected⟩
  have hU_mem : U ∈ 𝓝 (0 : CParam s e) := hU_open.mem_nhds (Metric.mem_ball_self hε)
  have hDf_an_U : AnalyticOnNhd ℂ Df U := fun z hz => (hball hz).1.1
  have hQf_an_U : AnalyticOnNhd ℂ Qf U := fun z hz => (hball hz).1.2
  have hD_U : ∀ z ∈ U, weierstrassDiscFn m a z = Df z * Qf z := fun z hz => (hball hz).2
  -- `Df ≢ 0`, `Qf ≢ 0` on `U` (else `disc ≡ 0`, contradicting `hdisc_ne`)
  have hDf_ne : ∃ z ∈ U, Df z ≠ 0 := by
    by_contra h; push_neg at h
    apply hdisc_ne
    apply order_eq_top_of_eventuallyEq_zero
    filter_upwards [hU_mem] with w hw
    show weierstrassDiscFn m a w = 0
    rw [hD_U w hw, h w hw, zero_mul]
  have hQf_ne : ∃ z ∈ U, Qf z ≠ 0 := by
    by_contra h; push_neg at h
    apply hdisc_ne
    apply order_eq_top_of_eventuallyEq_zero
    filter_upwards [hU_mem] with w hw
    show weierstrassDiscFn m a w = 0
    rw [hD_U w hw, h w hw, mul_zero]
  -- `order Df 0 ≠ ⊤`
  have hDf_ne_top : order ℂ Df (0 : CParam s e) ≠ ⊤ := by
    intro htop
    apply hdisc_ne
    apply order_eq_top_of_eventuallyEq_zero
    have hDf0 := eventuallyEq_zero_of_order_eq_top Df 0 hDf_an htop
    filter_upwards [hDf0, hDrel] with w hwDf hwrel
    show weierstrassDiscFn m a w = 0
    rw [hwrel]
    simp only [Pi.zero_apply] at hwDf
    rw [hwDf, zero_mul]
  refine ⟨hDf_ne_top, ?_⟩
  -- section ball `V` and the order-invariance descent
  have hsec_pre : (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) ⁻¹' U ∈ 𝓝 (0 : Fin s → ℂ) := by
    apply (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
    simpa using hU_mem
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hsec_pre hdisc)
  set V : Set (Fin s → ℂ) := Metric.ball 0 δ with hV
  have hV_conn : IsPreconnected V := (convex_ball (0 : Fin s → ℂ) δ).isPreconnected
  have hV0 : (0 : Fin s → ℂ) ∈ V := Metric.mem_ball_self hδ
  have hV_mem : V ∈ 𝓝 (0 : Fin s → ℂ) := Metric.isOpen_ball.mem_nhds hV0
  have hVU : ∀ y ∈ V, ((y, 0) : CParam s e) ∈ U := fun y hy => (hδball hy).1
  have hD_oi : ∀ y ∈ V, order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
      = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s e) := fun y hy => (hδball hy).2
  have hdescent := factor_order_inv_on_section Df Qf (weierstrassDiscFn m a) hU_open hU_conn
    hV_conn hV0 hVU hDf_an_U hQf_an_U hDf_ne hQf_ne hD_U hD_oi
  filter_upwards [hV_mem] with y hy
  exact hdescent y hy

end Analytic
