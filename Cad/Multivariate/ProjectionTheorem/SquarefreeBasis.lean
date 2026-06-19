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
