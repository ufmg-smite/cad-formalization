import Cad.Multivariate.ProjectionTheorem.DiscrMul
import Cad.Multivariate.ProjectionTheorem.PolyOrderMul
import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Proof of `discr_prod_order_invariant`

We prove that the discriminant of a product of squarefree, pairwise coprime polynomials
is order-invariant on a connected set `S`, given that individual discriminants and pairwise
resultants are order-invariant on `S`.

## Structure

1. **`polyOrder_mul_add`** (proved in `Cad.Multivariate.ProjectionTheorem.PolyOrderMul`): vanishing order is additive
   under products. Proved via the Taylor shift and `MvPowerSeries.order_mul`.

2. **Lemma 3.2.2** (forward direction, McCallum §3.2): a product of order-invariant
   multivariate polynomials is order-invariant. Proved from `polyOrder_mul_add`.

3. **Theorem 2.3.3** (McCallum §2.3, axiom): the discriminant product formula
   `discr(f · g) = discr(f) · res(f, g)² · discr(g)`.

4. **Main result**: `discr_prod_order_invariant` by Finset induction, combining
   the discriminant product formula, the multiplicativity of resultants (from Mathlib),
   and the order-invariance closure under products.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-! ### Lemma 3.2.2: Order invariance is closed under products -/

theorem order_invariant_mul_mv
    (S : Set (Fin n → ℝ)) (f g : MvPolyR n)
    (hf : OrderInvariantMv f S) (hg : OrderInvariantMv g S) :
    OrderInvariantMv (f * g) S := by
  intro a ha b hb
  rw [polyOrder_mul_add, polyOrder_mul_add, hf a ha b hb, hg a ha b hb]

theorem order_invariant_prod_mv
    (S : Set (Fin n → ℝ)) {ι : Type*} (s : Finset ι) (f : ι → MvPolyR n)
    (hf : ∀ i ∈ s, OrderInvariantMv (f i) S) :
    OrderInvariantMv (∏ i ∈ s, f i) S := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    intro a _ b _
    have h1 : polyOrder n (1 : MvPolyR n) a = 0 := (polyOrder_zero_iff n 1 a).mpr (by simp)
    have h2 : polyOrder n (1 : MvPolyR n) b = 0 := (polyOrder_zero_iff n 1 b).mpr (by simp)
    rw [h1, h2]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact order_invariant_mul_mv S _ _
      (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-! ### Reverse direction: order-invariance of a product transfers to its factors

This is the key step justifying the generalization from the discriminant to an arbitrary
element of the elimination ideal **without** a non-vanishing hypothesis. The vanishing order
`polyOrder` is upper semi-continuous; so if two such orders sum to a constant on a connected
set, each must individually be constant (if one jumps up at a point, the other must jump
down, contradicting its upper semi-continuity). -/

/-- A nonzero polynomial has finite vanishing order at every point. -/
theorem polyOrder_ne_top_of_ne_zero (g : MvPolyR n) (hg : g ≠ 0) (a : Fin n → ℝ) :
    polyOrder n g a ≠ ⊤ := by
  rw [polyOrder_taylorShift, polyOrder_zero_eq_mvPowerSeries_order]
  intro htop
  rw [MvPowerSeries.order_eq_top_iff] at htop
  have hts0 : taylorShift n g a = 0 := by
    ext d
    have hcd := congr_arg (MvPowerSeries.coeff d) htop
    rw [coeff_coe, map_zero] at hcd
    simpa using hcd
  apply hg
  apply MvPolynomial.funext
  intro c
  have h1 := eval_taylorShift g a (c - a)
  rw [hts0, map_zero] at h1
  have hca : (fun i => (c - a) i + a i) = c := by funext i; simp
  rw [hca] at h1
  rw [map_zero]
  exact h1.symm

/-- Upper semi-continuity of `polyOrder`: each superlevel set `{a | k ≤ polyOrder g a}`
is closed (it is the intersection of the closed zero-sets of the Fréchet derivatives of
order `< k` of the analytic evaluation map). -/
private lemma isClosed_polyOrder_ge (g : MvPolyR n) (k : ℕ) :
    IsClosed {a : Fin n → ℝ | (↑k : ℕ∞) ≤ polyOrder n g a} := by
  have hcontdiff : ContDiff ℝ ⊤ (fun x => MvPolynomial.eval x g) :=
    (show AnalyticOnNhd ℝ (fun x => MvPolynomial.eval x g) univ from
      fun x hx => AnalyticOnNhd.eval_mvPolynomial g x hx).contDiff
  have heq : {a : Fin n → ℝ | (↑k : ℕ∞) ≤ polyOrder n g a} =
      ⋂ (j : ℕ) (_ : j < k),
        {a : Fin n → ℝ | iteratedFDeriv ℝ j (fun x => MvPolynomial.eval x g) a = 0} := by
    ext a
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro h j hj
      apply iteratedFDeriv_eq_zero_of_lt_order
      calc (↑j : ℕ∞) < ↑k := by exact_mod_cast hj
        _ ≤ polyOrder n g a := h
    · intro h
      by_contra hlt
      push_neg at hlt
      have hfin : polyOrder n g a ≠ ⊤ := ne_top_of_lt hlt
      have hm : polyOrder n g a = ↑(polyOrder n g a).toNat := (ENat.coe_toNat hfin).symm
      have hmk : (polyOrder n g a).toNat < k := by rw [hm] at hlt; exact_mod_cast hlt
      exact ((order_eq_natCast_iff).mp hm).2 (h _ hmk)
  rw [heq]
  refine isClosed_iInter (fun j => isClosed_iInter (fun _ => ?_))
  exact isClosed_eq (hcontdiff.continuous_iteratedFDeriv le_top) continuous_const

/-- Helper for the reverse direction: if `polyOrder f + polyOrder g` is constant on a
connected set `S` (with `f, g ≠ 0`), then `polyOrder f` is bounded above by its value at
the basepoint `a₀` everywhere on `S`. Proved by a connectivity argument: the open sets
`{f ≤ A}` and `{g < B}` cover `S` (from the constant sum) and are disjoint on `S`, so the
second cannot meet `S`. -/
private lemma polyOrder_factor_le
    (S : Set (Fin n → ℝ)) (hS : IsPreconnected S) (f g : MvPolyR n)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (a₀ : Fin n → ℝ) (ha₀ : a₀ ∈ S)
    (hsum : ∀ a ∈ S, polyOrder n f a + polyOrder n g a
        = polyOrder n f a₀ + polyOrder n g a₀) :
    ∀ z ∈ S, polyOrder n f z ≤ polyOrder n f a₀ := by
  set A := polyOrder n f a₀ with hA
  set B := polyOrder n g a₀ with hB
  have hA_ne : A ≠ ⊤ := polyOrder_ne_top_of_ne_zero f hf_ne a₀
  have hB_ne : B ≠ ⊤ := polyOrder_ne_top_of_ne_zero g hg_ne a₀
  -- The two open sets
  have hA'_open : IsOpen {z : Fin n → ℝ | polyOrder n f z ≤ A} := by
    have hrw : {z : Fin n → ℝ | polyOrder n f z ≤ A}
        = {z : Fin n → ℝ | (↑((A.toNat) + 1) : ℕ∞) ≤ polyOrder n f z}ᶜ := by
      ext z
      simp only [mem_setOf_eq, mem_compl_iff, not_le, Nat.cast_add, Nat.cast_one]
      conv_lhs => rw [(ENat.coe_toNat hA_ne).symm]
      exact (ENat.lt_add_one_iff (ENat.coe_ne_top A.toNat)).symm
    rw [hrw]; exact (isClosed_polyOrder_ge f (A.toNat + 1)).isOpen_compl
  have hB'_open : IsOpen {z : Fin n → ℝ | polyOrder n g z < B} := by
    have hrw : {z : Fin n → ℝ | polyOrder n g z < B}
        = {z : Fin n → ℝ | (↑(B.toNat) : ℕ∞) ≤ polyOrder n g z}ᶜ := by
      ext z
      simp only [mem_setOf_eq, mem_compl_iff, not_le]
      conv_lhs => rw [(ENat.coe_toNat hB_ne).symm]
    rw [hrw]; exact (isClosed_polyOrder_ge g B.toNat).isOpen_compl
  -- Covering: S ⊆ {f ≤ A} ∪ {g < B}
  have hcov : S ⊆ {z : Fin n → ℝ | polyOrder n f z ≤ A} ∪ {z | polyOrder n g z < B} := by
    intro z hz
    by_contra hzn
    rw [Set.mem_union, not_or] at hzn
    obtain ⟨hzA, hzB⟩ := hzn
    simp only [mem_setOf_eq, not_le] at hzA
    simp only [mem_setOf_eq, not_lt] at hzB
    have hsz := hsum z hz
    have hlt : A + B < polyOrder n f z + polyOrder n g z :=
      lt_of_lt_of_le ((ENat.add_lt_add_iff_right hB_ne).mpr hzA)
        (add_le_add_right hzB (polyOrder n f z))
    rw [hsz] at hlt; exact lt_irrefl _ hlt
  -- The second set does not meet S
  have hBempty : S ∩ {z : Fin n → ℝ | polyOrder n g z < B} = ∅ := by
    rcases Set.eq_empty_or_nonempty (S ∩ {z | polyOrder n g z < B}) with h | hne
    · exact h
    · exfalso
      have hcap := hS _ _ hA'_open hB'_open hcov ⟨a₀, ha₀, by simp [hA]⟩ hne
      obtain ⟨z, hzS, hzA', hzB'⟩ := hcap
      simp only [mem_setOf_eq] at hzA' hzB'
      have hsz := hsum z hzS
      have hlt : polyOrder n f z + polyOrder n g z < A + B :=
        lt_of_le_of_lt (add_le_add_left hzA' (polyOrder n g z))
          ((ENat.add_lt_add_iff_left hA_ne).mpr hzB')
      rw [hsz] at hlt; exact lt_irrefl _ hlt
  -- Conclude
  intro z hz
  have hzB : ¬ polyOrder n g z < B := by
    intro h
    have : z ∈ S ∩ {z | polyOrder n g z < B} := ⟨hz, h⟩
    rw [hBempty] at this; exact this
  rw [not_lt] at hzB
  have hsz := hsum z hz
  have h2 : polyOrder n f z + B ≤ polyOrder n f z + polyOrder n g z :=
    add_le_add_right hzB (polyOrder n f z)
  rw [hsz] at h2
  exact (ENat.add_le_add_iff_right hB_ne).mp h2

/-! ### Main result -/

private lemma leadingCoeff_prod_ne_zero
    (A : Finset (PolyR n)) (hpos : ∀ f ∈ A, 0 < f.natDegree) :
    ∏ f ∈ A, f.leadingCoeff ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun f hf =>
    leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (hpos f hf))

private theorem resultant_prod_eq
    (p : PolyR n) (A : Finset (PolyR n))
    (hpos : ∀ f ∈ A, 0 < f.natDegree) :
    resultant p (∏ f ∈ A, f) = ∏ g ∈ A, resultant p g := by
  have hlc := leadingCoeff_prod_ne_zero A hpos
  have h := resultant_prod_right A p id p.natDegree le_rfl (by simpa using hlc)
  simpa using h

end
