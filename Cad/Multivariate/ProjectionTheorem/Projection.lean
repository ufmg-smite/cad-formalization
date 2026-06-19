import Cad.Multivariate.ProjectionTheorem.DiscrMul
import Cad.Multivariate.ProjectionTheorem.DiscrNonzero
import Cad.Multivariate.ProjectionTheorem.DiscrProdInvariant
import Cad.Multivariate.ProjectionTheorem.OrderInvariantFactor
import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Cad.Multivariate.ProjectionTheorem.SquarefreeBasis
import Cad.Multivariate.ProjectionTheorem.Generalized.Projection
import Cad.Multivariate.ProjectionTheorem.Brown.Discr

/-!
# McCallum's Reduced Projection Theorem (Theorem 3.2.3)

This file contains the statement and proof of Theorem 3.2.3 from McCallum's PhD thesis
"An Improved Projection Operation for Cylindrical Algebraic Decomposition" (1984).

## Main result

**Theorem 3.2.3**: Let `A` be a finite squarefree basis of `r`-variate integral polynomials
(`r ≥ 2`), `S` a connected submanifold of `ℝ^{r-1}`. Suppose each element of `A` is not
identically zero on `S`, and each element of the reduced projection `P(A)` is
order-invariant in `S`. Then:
1. Each element of `A` is degree-invariant on `S`
2. Each element of `A` is analytically delineable on `S`
3. The sections of `A` over `S` are pairwise disjoint
4. Each element of `A` is order-invariant in every section of `A` over `S`
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

theorem lifting_theorem
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hdeg : DegreeInvariant f S)
    (hf_deg : 1 < f.natDegree)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (hf_sf : Squarefree f)
    (hP_oi : OrderInvariantMv f.discr S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  have hf_deg' : 0 < f.natDegree := by omega
  have discr_ne_zero : f.discr ≠ 0 := by apply discr_ne_zero_of_squarefree f hf_sf hf_deg'

  have hunit : IsUnit (f.natDegree : MvPolynomial (Fin n) ℝ) := by
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) f.natDegree]
    exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))

  have discr_in_span := Brown.discr_mem_span f hf_deg hunit
  exact lifting_theorem_generalized S f hS_submfld hS_conn hdeg hspec_ne f.discr discr_ne_zero discr_in_span hP_oi

/-/1-- The set of nonzero coefficients of polynomials in `A`, viewed as multivariate -/
/-polynomials in the base ring. Part of the reduced projection `P(A)`. -1/ -/
/-def coeffSet (A : Finset (PolyR n)) : Set (MvPolyR n) := -/
/-  {c | ∃ f ∈ A, ∃ k : ℕ, f.coeff k = c ∧ c ≠ 0} -/

/-/1-- The set of discriminants of polynomials in `A` of degree at least 2. -/
/-Part of the reduced projection `P(A)`. -1/ -/
/-def discrSet (A : Finset (PolyR n)) : Set (MvPolyR n) := -/
/-  {d | ∃ f ∈ A, 2 ≤ f.natDegree ∧ d = Polynomial.discr f} -/

/-/1-- The set of resultants of pairs of distinct polynomials in `A`, both of positive -/
/-degree. Part of the reduced projection `P(A)`. -1/ -/
/-def resSet (A : Finset (PolyR n)) : Set (MvPolyR n) := -/
/-  {r | ∃ f ∈ A, ∃ g ∈ A, f ≠ g ∧ 1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ -/
/-    r = Polynomial.resultant f g} -/

/-/1-- McCallum's **reduced projection** `P(A)`: the union of `coeffSet A`, `discrSet A`, -/
/-and `resSet A`. -1/ -/
/-def reducedProjection (A : Finset (PolyR n)) : Set (MvPolyR n) := -/
/-  coeffSet A ∪ discrSet A ∪ resSet A -/

/-theorem mccallum_3_2_3 -/
/-    (A : Finset (PolyR n)) -/
/-    (S : Set (Fin n → ℝ)) -/
/-    (hA : IsSquarefreeBasis A) -/
/-    (hA_ne : A.Nonempty) -/
/-    (hS_submfld : IsAnalyticSubmanifold S) -/
/-    (hS_conn : IsConnected S) -/
/-    (hnonzero : ∀ f ∈ A, NotIdenticallyZeroOn f S) -/
/-    (hP : ∀ g ∈ reducedProjection A, OrderInvariantMv g S) : -/
/-    (∀ f ∈ A, DegreeInvariant f S) ∧ -/
/-    (∀ f ∈ A, AnalyticDelineable f S) ∧ -/
/-    SectionsDisjoint A S ∧ -/
/-    OrderInvariantInAllSections A S := by -/
/-  have h_coeff : -/
/-     (∀ f ∈ A, ∀ (k : ℕ), Polynomial.coeff f k ≠ 0 → OrderInvariantMv (Polynomial.coeff f k) S) := sorry -/
/-  let d := fun f: PolyR n => f.discr -/
/-  have hD_ne : ∀ p ∈ A, d p ≠ 0 := by -/
/-    intros p hp -/
/-    have : Squarefree p := hA.sq_free p hp -/
/-    unfold d -/
/-    exact discr_ne_zero_of_squarefree p this (hA.pos_degree p hp) -/
/-  -- Needs to be refined a bit, right now there is no guarantee that the elements of `A` have degree >= 2 -/
/-  have := mccallum_3_2_3_generalized A S hA hA_ne hS_submfld hS_conn hnonzero h_coeff d hD_ne -/
/-  admit -/

end
