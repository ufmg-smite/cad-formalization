import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Real.Basic

/-!
# Basic definitions for the McCallum formalization

Type abbreviations and the specialization operation used throughout.
-/

noncomputable section

open Polynomial MvPolynomial Classical

/-- r-variate polynomials viewed as univariate in `xᵣ` over `ℝ[x₁,…,xₙ]`. -/
abbrev PolyR (n : ℕ) := Polynomial (MvPolynomial (Fin n) ℝ)

/-- (r-1)-variate polynomials over `ℝ`. -/
abbrev MvPolyR (n : ℕ) := MvPolynomial (Fin n) ℝ

variable {n : ℕ}

/-- Evaluate base variables of an MvPolynomial at a point `a ∈ ℝⁿ`. -/
abbrev evalBase (a : Fin n → ℝ) : MvPolyR n →+* ℝ :=
  MvPolynomial.eval a

/-- Specialize `f(x, xᵣ)` at `x = a` to get `f(a, xᵣ) ∈ ℝ[xᵣ]`. -/
def specialize (f : PolyR n) (a : Fin n → ℝ) : Polynomial ℝ :=
  f.map (evalBase a)

/-- Convert `PolyR n` to `MvPolynomial (Fin (n+1)) ℝ` via `finSuccEquiv`. -/
def toMvPoly (f : PolyR n) : MvPolynomial (Fin (n + 1)) ℝ :=
  (MvPolynomial.finSuccEquiv ℝ n).symm f

/-- Convert `MvPolynomial (Fin (n+1)) ℝ` to `PolyR n` via `finSuccEquiv`; the inverse of
`toMvPoly`. -/
def ofMvPoly (g : MvPolynomial (Fin (n + 1)) ℝ) : PolyR n :=
  MvPolynomial.finSuccEquiv ℝ n g

@[simp]
theorem toMvPoly_ofMvPoly (g : MvPolynomial (Fin (n + 1)) ℝ) :
    toMvPoly (ofMvPoly g) = g :=
  (MvPolynomial.finSuccEquiv ℝ n).symm_apply_apply g

@[simp]
theorem ofMvPoly_toMvPoly (f : PolyR n) :
    ofMvPoly (toMvPoly f) = f :=
  (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply f

end
