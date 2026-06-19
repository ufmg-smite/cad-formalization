import Cad.Multivariate.ProjectionTheorem.Basic
import Cad.Multivariate.ProjectionTheorem.Order

/-!
# Invariance conditions: degree-invariance, order-invariance, and non-vanishing

Definitions used to express hypotheses and conclusions of McCallum's theorems.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- `f` is **degree-invariant** on `S`. -/
def DegreeInvariant (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, (specialize f a).natDegree = (specialize f b).natDegree

/-- A base polynomial `g` is **order-invariant** on `S`. -/
def OrderInvariantMv (g : MvPolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, polyOrder n g a = polyOrder n g b

/-- **McCallum's order of `f` at `(a, y)`** — the multivariate analytic order `ord_{(a,y)} f`:
the least `k` such that some order-`k` partial derivative of `f` (as the `(n+1)`-variable analytic
function `toMvPoly f`) does not vanish at `(y, a)` (`⊤` if all vanish). This is McCallum's `ord`
from §2.3 of the thesis, used uniformly for the discriminant hypothesis and the order-invariance
conclusion. (Note `ord_{(a,y)} f ≤ rootMultiplicity y (specialize f a)`, the gap being a transverse
order drop; the two coincide along delineable sections via Zariski 4.1.1, conclusion (2).) -/
def orderFull (f : PolyR n) (a : Fin n → ℝ) (y : ℝ) : ℕ∞ :=
  polyOrder (n + 1) (toMvPoly f) (Fin.cons y a)

/-- A full polynomial `f` is **order-invariant** in `T ⊆ ℝⁿ × ℝ`. -/
def OrderInvariantFull (f : PolyR n) (T : Set ((Fin n → ℝ) × ℝ)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, orderFull f p.1 p.2 = orderFull f q.1 q.2

/-- `f` is **not identically zero** on `S`. -/
def NotIdenticallyZeroOn (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ a ∈ S, specialize f a ≠ 0

/-- Degree-invariance from coefficient order-invariance. -/
theorem degree_invariant_of_coeff_order_invariant
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hcoeff : ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S) :
    DegreeInvariant f S := by
  intro a ha b hb
  -- It suffices to show that the two specialized polynomials have the same support
  -- (i.e., the same set of nonzero coefficients), since natDegree is determined by support.
  -- Key helper: for any k where f.coeff k ≠ 0, eval at a is nonzero iff eval at b is nonzero
  have coeff_nonzero_iff : ∀ k, (specialize f a).coeff k ≠ 0 ↔ (specialize f b).coeff k ≠ 0 := by
    intro k
    simp only [specialize, Polynomial.coeff_map]
    by_cases hk : f.coeff k = 0
    · simp [hk, map_zero]
    · have hinv := hcoeff k hk
      constructor
      · intro heval_a
        have hord_a : polyOrder n (f.coeff k) a = 0 :=
          (polyOrder_zero_iff n (f.coeff k) a).mpr heval_a
        have hord_b : polyOrder n (f.coeff k) b = 0 := by
          rw [← hord_a]; exact (hinv a ha b hb).symm
        exact (polyOrder_zero_iff n (f.coeff k) b).mp hord_b
      · intro heval_b
        have hord_b : polyOrder n (f.coeff k) b = 0 :=
          (polyOrder_zero_iff n (f.coeff k) b).mpr heval_b
        have hord_a : polyOrder n (f.coeff k) a = 0 := by
          rw [← hord_b]; exact hinv a ha b hb
        exact (polyOrder_zero_iff n (f.coeff k) a).mp hord_a
  -- Now show natDegree equality using le_natDegree_of_ne_zero
  apply le_antisymm
  · by_cases hza : specialize f a = 0
    · simp [hza]
    · have hlc : (specialize f a).coeff (specialize f a).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hza
      exact Polynomial.le_natDegree_of_ne_zero ((coeff_nonzero_iff _).mp hlc)
  · by_cases hzb : specialize f b = 0
    · simp [hzb]
    · have hlc : (specialize f b).coeff (specialize f b).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hzb
      exact Polynomial.le_natDegree_of_ne_zero ((coeff_nonzero_iff _).mpr hlc)

end
