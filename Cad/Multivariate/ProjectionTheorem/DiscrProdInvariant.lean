import Cad.Multivariate.ProjectionTheorem.DiscrMul
import Cad.Multivariate.ProjectionTheorem.PolyOrderMul
import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Proof of `discr_prod_order_invariant`

We prove that the discriminant of a product of squarefree, pairwise coprime polynomials
is order-invariant on a connected set `S`, given that individual discriminants and pairwise
resultants are order-invariant on `S`.

## Structure

1. **`polyOrder_mul_add`** (proved in `Mccalum.PolyOrderMul`): vanishing order is additive
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

theorem order_invariant_sq_mv
    (S : Set (Fin n → ℝ)) (f : MvPolyR n) (hf : OrderInvariantMv f S) :
    OrderInvariantMv (f ^ 2) S := by
  rw [sq]; exact order_invariant_mul_mv S f f hf hf

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

/-- **Theorem**: The discriminant of a product of squarefree, pairwise coprime polynomials
of positive degree is order-invariant, given order-invariance of individual discriminants
and pairwise resultants.

This replaces the axiom `discr_prod_order_invariant` from `Mccalum.Prerequisites`, with the
additional hypothesis `hpos` (positive degree), which is available at every call site via
`IsSquarefreeBasis.pos_degree`. -/
theorem discr_prod_order_invariant
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hpos : ∀ f ∈ A, 0 < f.natDegree)
    (hsf : ∀ f ∈ A, Squarefree f)
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g)
    (hdisc : ∀ f ∈ A, OrderInvariantMv (discr f) S)
    (hres : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      OrderInvariantMv (resultant f g) S) :
    OrderInvariantMv (discr (∏ f ∈ A, f)) S := by
  induction A using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rw [show (1 : PolyR n) = Polynomial.C 1 from rfl, discr_C]
    intro a _ b _
    have h1 : polyOrder n (1 : MvPolyR n) a = 0 := (polyOrder_zero_iff n 1 a).mpr (by simp)
    have h2 : polyOrder n (1 : MvPolyR n) b = 0 := (polyOrder_zero_iff n 1 b).mpr (by simp)
    rw [h1, h2]
  | @insert p A hpA ih =>
    have hpos' : ∀ f ∈ A, 0 < f.natDegree := fun f hf => hpos f (Finset.mem_insert_of_mem hf)
    have hsf' : ∀ f ∈ A, Squarefree f := fun f hf => hsf f (Finset.mem_insert_of_mem hf)
    have hcop' : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g :=
      fun f hf g hg => hcop f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg)
    have hdisc' : ∀ f ∈ A, OrderInvariantMv (discr f) S :=
      fun f hf => hdisc f (Finset.mem_insert_of_mem hf)
    have hres' : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → OrderInvariantMv (resultant f g) S :=
      fun f hf g hg => hres f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg)
    have ih_oi := ih hpos' hsf' hcop' hdisc' hres'
    rw [Finset.prod_insert hpA]
    by_cases hA : A = ∅
    · subst hA; simp; exact hdisc p (Finset.mem_insert_self p ∅)
    · have hA_ne : A.Nonempty := Finset.nonempty_of_ne_empty hA
      have hp_pos := hpos p (Finset.mem_insert_self p A)
      have hq_pos : 0 < (∏ f ∈ A, f).natDegree := prod_pos_degree A hA_ne hpos'
      rw [discr_mul_eq p (∏ f ∈ A, f) hp_pos hq_pos]
      -- res(p, ∏ A) is order-invariant
      have hres_pq : OrderInvariantMv (resultant p (∏ f ∈ A, f)) S := by
        rw [resultant_prod_eq p A hpos']
        apply order_invariant_prod_mv S A (fun g => resultant p g)
        intro g hg
        exact hres p (Finset.mem_insert_self p A) g (Finset.mem_insert_of_mem hg)
          (fun h => hpA (h ▸ hg))
      exact order_invariant_mul_mv S _ _
        (order_invariant_mul_mv S _ _
          (hdisc p (Finset.mem_insert_self p A))
          (order_invariant_sq_mv S _ hres_pq))
        ih_oi

#print axioms discr_prod_order_invariant

end
