import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Cad.Multivariate.ProjectionTheorem.Delineability
import Cad.Multivariate.ProjectionTheorem.Invariance

/-!
# Squarefree basis, reduced projection, and section properties

Definitions used in the statement of Theorem 3.2.3.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- `A` is a **squarefree basis**: every element of `A` has positive degree, is squarefree,
and any two distinct elements are coprime. -/
structure IsSquarefreeBasis (A : Finset (PolyR n)) : Prop where
  pos_degree : ∀ f ∈ A, 0 < f.natDegree
  sq_free : ∀ f ∈ A, Squarefree f
  pairwise_coprime : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g

/-- The set of nonzero coefficients of polynomials in `A`, viewed as multivariate
polynomials in the base ring. Part of the reduced projection `P(A)`. -/
def coeffSet (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  {c | ∃ f ∈ A, ∃ k : ℕ, f.coeff k = c ∧ c ≠ 0}

/-- The set of discriminants of polynomials in `A` of degree at least 2.
Part of the reduced projection `P(A)`. -/
def discrSet (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  {d | ∃ f ∈ A, 2 ≤ f.natDegree ∧ d = Polynomial.discr f}

/-- The set of resultants of pairs of distinct polynomials in `A`, both of positive
degree. Part of the reduced projection `P(A)`. -/
def resSet (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  {r | ∃ f ∈ A, ∃ g ∈ A, f ≠ g ∧ 1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧
    r = Polynomial.resultant f g}

/-- McCallum's **reduced projection** `P(A)`: the union of `coeffSet A`, `discrSet A`,
and `resSet A`. -/
def reducedProjection (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  coeffSet A ∪ discrSet A ∪ resSet A

/-- The **sections of `A` over `S` are pairwise disjoint**: for any two distinct
polynomials `F, G ∈ A` and any `a ∈ S`, the roots of their specializations at `a`
do not overlap. -/
def SectionsDisjoint (A : Finset (PolyR n)) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ F ∈ A, ∀ G ∈ A, F ≠ G → ∀ a ∈ S,
    Disjoint {y | (specialize F a).IsRoot y} {y | (specialize G a).IsRoot y}

/-- Every polynomial in `A` is **order-invariant in every section of `A` over `S`**:
for any `F, G ∈ A` and any continuous root function `θ` of `G` on `S`, the polynomial
`F` is order-invariant on the section graph of `θ` over `S`. -/
def OrderInvariantInAllSections (A : Finset (PolyR n)) (S : Set (Fin n → ℝ)) :
    Prop :=
  ∀ F ∈ A, ∀ G ∈ A, ∀ θ : (Fin n → ℝ) → ℝ,
    ContinuousOn θ S → IsRootFunction G θ S →
    OrderInvariantFull F (SectionGraph θ S)

end
