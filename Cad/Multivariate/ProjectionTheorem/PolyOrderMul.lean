import Cad.Multivariate.ProjectionTheorem.Order
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Additivity of vanishing order under multiplication

We prove `polyOrder m (f * g) a = polyOrder m f a + polyOrder m g a` for
multivariate polynomials, using the Taylor shift and `MvPowerSeries.order_mul`.

## Strategy

1. Define the **Taylor shift** `τ_a f := aeval (X + C a) f`, a ring endomorphism.
2. Show `polyOrder m f a = polyOrder m (τ_a f) 0` (translation invariance via `order'`).
3. Show `polyOrder m f 0 = MvPowerSeries.order (↑f)` (connecting derivatives to coefficients).
4. Combine with `MvPowerSeries.order_mul` (ℝ is an integral domain).
-/

noncomputable section

open MvPolynomial MvPowerSeries Classical Finsupp

variable {m : ℕ}

/-! ### Taylor shift -/

/-- The Taylor shift of `f` at `a`: substitutes `Xᵢ + aᵢ` for each `Xᵢ`. -/
def taylorShift (m : ℕ) (f : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    MvPolynomial (Fin m) ℝ :=
  MvPolynomial.aeval (R := ℝ) (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) f

/-- The Taylor shift of `f` at `a` packaged as an `ℝ`-algebra homomorphism. -/
def taylorShiftHom (m : ℕ) (a : Fin m → ℝ) :
    MvPolynomial (Fin m) ℝ →ₐ[ℝ] MvPolynomial (Fin m) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i))

/-- `taylorShift` agrees with the algebra homomorphism `taylorShiftHom` on elements. -/
theorem taylorShift_eq_hom (f : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    taylorShift m f a = taylorShiftHom m a f := rfl

/-- The Taylor shift is multiplicative: `τ_a (f * g) = (τ_a f) * (τ_a g)`. -/
@[simp]
theorem taylorShift_mul (f g : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    taylorShift m (f * g) a = taylorShift m f a * taylorShift m g a :=
  map_mul _ f g

/-- Evaluation of `τ_a f` at `b` equals evaluation of `f` at `b + a`. -/
theorem eval_taylorShift (f : MvPolynomial (Fin m) ℝ) (a b : Fin m → ℝ) :
    MvPolynomial.eval b (taylorShift m f a) = MvPolynomial.eval (fun i => b i + a i) f := by
  have h : ((MvPolynomial.aeval b).comp (taylorShiftHom m a) :
      MvPolynomial (Fin m) ℝ →ₐ[ℝ] ℝ) =
      MvPolynomial.aeval (fun i => b i + a i) := by
    ext i
    simp [taylorShiftHom, aeval_def, MvPolynomial.eval₂_X]
  change (MvPolynomial.aeval b) ((taylorShiftHom m a) f) = MvPolynomial.eval (fun i => b i + a i) f
  rw [← AlgHom.comp_apply, h]
  rfl

/-- Evaluation of `τ_a f` at the origin equals evaluation of `f` at `a`. -/
theorem eval_zero_taylorShift (f : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    MvPolynomial.eval 0 (taylorShift m f a) = MvPolynomial.eval a f := by
  rw [eval_taylorShift]
  simp only [Pi.zero_apply, zero_add]

/-! ### Connecting polyOrder to MvPowerSeries.order -/

/-- The coefficient of `e` in `pderiv j f` equals `(e j + 1) * coeff (e + single j 1) f`. -/
private lemma coeff_pderiv_eq
    (e : Fin m →₀ ℕ) (j : Fin m) (f : MvPolynomial (Fin m) ℝ) :
    MvPolynomial.coeff e (pderiv j f) =
    (↑(e j + 1) : ℝ) * MvPolynomial.coeff (e + Finsupp.single j 1) f := by
  rw [f.as_sum]
  simp only [map_sum, pderiv_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s = e + Finsupp.single j 1
  · subst hs
    have hsub : e + Finsupp.single j 1 - Finsupp.single j 1 = e := by
      ext i; simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [if_pos hsub, if_pos rfl]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    push_cast; ring
  · rw [if_neg hs, mul_zero]
    by_cases heq : s - Finsupp.single j 1 = e
    · have hsj : s j = 0 := by
        by_contra h; apply hs; subst heq
        ext i
        simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
        split_ifs with h'
        · subst h'; omega
        · omega
      rw [if_pos heq, hsj, Nat.cast_zero, mul_zero]
    · rw [if_neg heq]

/-- Convert a list of variable indices to a multi-index (Finsupp) via multiset counting. -/
private def listToFinsupp (l : List (Fin m)) : Fin m →₀ ℕ :=
  Multiset.toFinsupp (↑l)

private lemma listToFinsupp_cons (j : Fin m) (l : List (Fin m)) :
    listToFinsupp (j :: l) = listToFinsupp l + Finsupp.single j 1 := by
  ext i; simp only [listToFinsupp, Multiset.toFinsupp_apply, Finsupp.add_apply,
    Finsupp.single_apply]
  rw [show (↑(j :: l) : Multiset (Fin m)) = {j} + ↑l from rfl,
    Multiset.count_add, Multiset.count_singleton]
  split_ifs with h <;> omega

/-- The coefficient of `e` in `iteratedPDeriv l f` equals a positive natural number
    times `coeff (e + listToFinsupp l) f`. -/
private lemma coeff_iteratedPDeriv_eq_pos_mul_coeff
    (e : Fin m →₀ ℕ) (l : List (Fin m)) (f : MvPolynomial (Fin m) ℝ) :
    ∃ c : ℕ, 0 < c ∧
    MvPolynomial.coeff e (iteratedPDeriv l f) =
    (↑c : ℝ) * MvPolynomial.coeff (e + listToFinsupp l) f := by
  induction l generalizing e with
  | nil => exact ⟨1, Nat.one_pos, by simp [iteratedPDeriv, listToFinsupp]⟩
  | cons j l ih =>
    rw [iteratedPDeriv_cons, coeff_pderiv_eq e j]
    obtain ⟨c, hc, heq⟩ := ih (e + Finsupp.single j 1)
    refine ⟨(e j + 1) * c, Nat.mul_pos (Nat.succ_pos _) hc, ?_⟩
    rw [heq, show e + Finsupp.single j 1 + listToFinsupp l = e + listToFinsupp (j :: l) from
      by rw [listToFinsupp_cons]; abel]
    push_cast; ring

private lemma listToFinsupp_toMultiset_toList (d : Fin m →₀ ℕ) :
    listToFinsupp (d.toMultiset.toList) = d := by
  simp [listToFinsupp, Multiset.coe_toList]

private lemma iteratedPDeriv_zero_eq_zero (l : List (Fin m)) :
    iteratedPDeriv l (0 : MvPolynomial (Fin m) ℝ) = 0 := by
  induction l with
  | nil => simp [iteratedPDeriv]
  | cons j l ih => simp [iteratedPDeriv_cons, ih]

private lemma degree_listToFinsupp_eq_length (l : List (Fin m)) :
    Finsupp.degree (listToFinsupp l) = l.length := by
  have : Finsupp.degree (listToFinsupp l) = (listToFinsupp l).toMultiset.card := by
    rw [Finsupp.card_toMultiset]; rfl
  rw [this]; simp [listToFinsupp]

private lemma length_toMultiset_toList_eq_degree (d : Fin m →₀ ℕ) :
    (d.toMultiset.toList).length = Finsupp.degree d := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]; rfl

/-- If `coeff d f ≠ 0`, then `iteratedPDeriv` along the list derived from `d` is nonzero
    at the origin. -/
private lemma iteratedPDeriv_eval_zero_ne_zero_of_coeff (d : Fin m →₀ ℕ)
    (f : MvPolynomial (Fin m) ℝ) (hd : MvPolynomial.coeff d f ≠ 0) :
    (iteratedPDeriv (d.toMultiset.toList) f).eval 0 ≠ 0 := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  obtain ⟨c, hcpos, heq⟩ := coeff_iteratedPDeriv_eq_pos_mul_coeff 0 d.toMultiset.toList f
  rw [zero_add, listToFinsupp_toMultiset_toList] at heq; rw [heq]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcpos)) hd

/-- If `iteratedPDeriv l f` is nonzero at the origin, then `coeff (listToFinsupp l) f ≠ 0`. -/
private lemma coeff_ne_zero_of_iteratedPDeriv_eval_zero (l : List (Fin m))
    (f : MvPolynomial (Fin m) ℝ) (h : (iteratedPDeriv l f).eval 0 ≠ 0) :
    MvPolynomial.coeff (listToFinsupp l) f ≠ 0 := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] at h
  obtain ⟨c, _, heq⟩ := coeff_iteratedPDeriv_eq_pos_mul_coeff 0 l f
  rw [zero_add] at heq; rw [heq] at h
  exact right_ne_zero_of_mul h

/-- At the origin, `polyOrder` of a polynomial equals the `MvPowerSeries.order` of its
    coercion to a power series. -/
theorem polyOrder_zero_eq_mvPowerSeries_order
    (f : MvPolynomial (Fin m) ℝ) :
    polyOrder m f 0 = (↑f : MvPowerSeries (Fin m) ℝ).order := by
  have heq_order : polyOrder m f 0 = order' m f 0 := by
    unfold polyOrder; rw [← (order_order' m f 0 _).mpr rfl]
  rw [heq_order]
  by_cases hf : f = 0
  · subst hf; simp [order', iteratedPDeriv_zero_eq_zero, MvPowerSeries.order_zero]
  · have hcoe_ne : (↑f : MvPowerSeries (Fin m) ℝ) ≠ 0 := by
      intro h; apply hf; ext d
      have := congr_arg (MvPowerSeries.coeff d) h; simp [coeff_coe] at this; exact this
    have hA : ∃ k : ℕ, ∃ l : List (Fin m), l.length = k ∧
        (iteratedPDeriv l f).eval 0 ≠ 0 := by
      obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.coeff d f ≠ 0 := by
        by_contra hall; push Not at hall; apply hf; ext d; simp [hall d]
      exact ⟨_, d.toMultiset.toList, rfl,
        iteratedPDeriv_eval_zero_ne_zero_of_coeff d f hd⟩
    unfold order'; rw [dif_pos hA]
    apply le_antisymm
    · -- ↑(Nat.find hA) ≤ order: all coefficients below Nat.find hA vanish
      apply MvPowerSeries.nat_le_order
      intro d hd_lt
      by_contra hne
      have hcoeff : MvPolynomial.coeff d f ≠ 0 := by rwa [coeff_coe] at hne
      have : Nat.find hA ≤ Finsupp.degree d :=
        Nat.find_min' hA ⟨d.toMultiset.toList,
          length_toMultiset_toList_eq_degree d,
          iteratedPDeriv_eval_zero_ne_zero_of_coeff d f hcoeff⟩
      exact not_le.mpr hd_lt (by exact_mod_cast this)
    · -- order ≤ ↑(Nat.find hA): the witness list gives a nonzero coefficient
      obtain ⟨l, hl, hne⟩ := Nat.find_spec hA
      have hcoeff := coeff_ne_zero_of_iteratedPDeriv_eval_zero l f hne
      calc (↑f : MvPowerSeries (Fin m) ℝ).order
          ≤ Finsupp.degree (listToFinsupp l) :=
            MvPowerSeries.order_le (by rwa [coeff_coe])
        _ = l.length := by exact_mod_cast degree_listToFinsupp_eq_length l
        _ = Nat.find hA := by exact_mod_cast hl

private theorem pderiv_taylorShiftHom (j : Fin m) (f : MvPolynomial (Fin m) ℝ)
    (a : Fin m → ℝ) :
    pderiv j (taylorShiftHom m a f) = taylorShiftHom m a (pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [taylorShiftHom]
  | add p q hp hq => simp only [map_add, (pderiv j).map_add, hp, hq]
  | mul_X p i hp =>
    have hX : pderiv j (taylorShiftHom m a (X i)) = taylorShiftHom m a (pderiv j (X i)) := by
      simp only [taylorShiftHom, aeval_X, pderiv_X]
      rw [(pderiv j).map_add, pderiv_C]
      simp only [add_zero]
      rcases eq_or_ne i j with rfl | h
      · simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne h]
    simp only [map_mul, (pderiv j).leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

private theorem pderiv_taylorShift (j : Fin m) (f : MvPolynomial (Fin m) ℝ)
    (a : Fin m → ℝ) :
    pderiv j (taylorShift m f a) = taylorShift m (pderiv j f) a := by
  simp only [taylorShift_eq_hom]
  exact pderiv_taylorShiftHom j f a

private theorem iteratedPDeriv_taylorShift (l : List (Fin m))
    (f : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    iteratedPDeriv l (taylorShift m f a) = taylorShift m (iteratedPDeriv l f) a := by
  induction l with
  | nil => simp [iteratedPDeriv]
  | cons j l ih =>
    simp only [iteratedPDeriv_cons, ih]
    exact pderiv_taylorShift j (iteratedPDeriv l f) a

/-- Translation invariance: `polyOrder m f a = polyOrder m (τ_a f) 0`. -/
theorem polyOrder_taylorShift
    (f : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    polyOrder m f a = polyOrder m (taylorShift m f a) 0 := by
  -- Use order' as a bridge: order' agrees with polyOrder
  suffices h : order' m f a = order' m (taylorShift m f a) 0 by
    rw [polyOrder, polyOrder, ← (order_order' m f a _ ).mpr rfl,
      ← (order_order' m (taylorShift m f a) 0 _).mpr rfl, h]
  -- The key: iteratedPDeriv l (taylorShift m f a) evaluated at 0 equals
  -- iteratedPDeriv l f evaluated at a
  have key : ∀ l : List (Fin m),
      (iteratedPDeriv l (taylorShift m f a)).eval 0 = (iteratedPDeriv l f).eval a := by
    intro l
    rw [iteratedPDeriv_taylorShift, eval_zero_taylorShift]
  -- Now show order' m f a = order' m (taylorShift m f a) 0
  unfold order'
  -- The existential predicates are equivalent
  have equiv : (∃ k : ℕ, ∃ l : List (Fin m), l.length = k ∧
      (iteratedPDeriv l (taylorShift m f a)).eval 0 ≠ 0) ↔
      (∃ k : ℕ, ∃ l : List (Fin m), l.length = k ∧
      (iteratedPDeriv l f).eval a ≠ 0) := by
    constructor <;> rintro ⟨k, l, hl, hne⟩ <;> exact ⟨k, l, hl, by rwa [key] at *⟩
  by_cases h1 : ∃ k : ℕ, ∃ l : List (Fin m), l.length = k ∧
      (iteratedPDeriv l f).eval a ≠ 0
  · have h2 := equiv.mpr h1
    rw [dif_pos h1, dif_pos h2]
    congr 1
    apply le_antisymm
    · apply Nat.find_min' h1
      obtain ⟨l, hl, hne⟩ := Nat.find_spec h2
      exact ⟨l, hl, by rwa [key] at hne⟩
    · apply Nat.find_min' h2
      obtain ⟨l, hl, hne⟩ := Nat.find_spec h1
      exact ⟨l, hl, by rwa [key]⟩
  · rw [dif_neg (mt equiv.mp h1), dif_neg h1]

/-! ### Main theorem -/

/-- Vanishing order of a product of multivariate polynomials equals the sum of orders. -/
theorem polyOrder_mul_add (m : ℕ) (f g : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    polyOrder m (f * g) a = polyOrder m f a + polyOrder m g a := by
  rw [polyOrder_taylorShift (f * g) a, taylorShift_mul,
    polyOrder_zero_eq_mvPowerSeries_order,
    MvPolynomial.coe_mul, MvPowerSeries.order_mul,
    ← polyOrder_zero_eq_mvPowerSeries_order,
    ← polyOrder_zero_eq_mvPowerSeries_order,
    ← polyOrder_taylorShift f a,
    ← polyOrder_taylorShift g a]

end
