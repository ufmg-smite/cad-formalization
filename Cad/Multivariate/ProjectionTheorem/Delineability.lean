import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Analytic.Basic
import Cad.Multivariate.ProjectionTheorem.Basic

/-!
# Sections, root functions, and analytic delineability
-/

noncomputable section

open Polynomial Set Classical

variable {n : ℕ}

/-- The graph of `θ` over `S`, i.e., a **section**. -/
def SectionGraph (θ : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | p.1 ∈ S ∧ p.2 = θ p.1}

/-- `θ` is a **root function** of `G` on `S`. -/
def IsRootFunction (G : PolyR n) (θ : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) :
    Prop :=
  ∀ a ∈ S, (specialize G a).IsRoot (θ a)

/-- `f` is **analytically delineable** on `S`: there exist finitely many analytic
root functions `θ₀ < … < θ_{k-1}` on `S` whose graphs cover all roots of the specializations
`specialize f a`, with constant multiplicities `m i > 0`. -/
def AnalyticDelineable (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (k : ℕ) (θ : Fin k → ((Fin n → ℝ) → ℝ)) (m : Fin k → ℕ),
    (∀ i, AnalyticOn ℝ (θ i) S) ∧
    (∀ a ∈ S, ∀ i j : Fin k, i < j → θ i a < θ j a) ∧
    (∀ a ∈ S, ∀ y : ℝ,
      (specialize f a).IsRoot y ↔ ∃ i : Fin k, y = θ i a) ∧
    (∀ i, 0 < m i) ∧
    (∀ a ∈ S, ∀ i, (specialize f a).rootMultiplicity (θ i a) = m i)

end
