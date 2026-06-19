import Cad.Multivariate.ProjectionTheorem.Generalized.Lifting
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Translation infrastructure for the multi-cluster assembly

To apply the single-cluster machinery (stated at `t = 0`) at a general real root `t_j`, the section
family is shifted via `taylor t_j (g w) = (g w).comp (X + C t_j)` (root at `t_j` ↦ root at `0`).
Mathlib supplies the shift facts for roots (`rootMultiplicity_eq_rootMultiplicity`) and degree
(`natDegree_taylor`); the new ingredient is that the shifted coefficients stay analytic.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- The coefficients of the Taylor-shifted family stay real-analytic. -/
lemma analyticAt_taylor_coeff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (N : ℕ) (g : D → Polynomial ℝ) (x₀ : D)
    (hdeg : ∀ w, (g w).natDegree ≤ N)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) x₀) (c : ℝ) (j : ℕ) :
    AnalyticAt ℝ (fun w => (taylor c (g w)).coeff j) x₀ := by
  have hrepr : (fun w => (taylor c (g w)).coeff j)
      = fun w => ∑ i ∈ Finset.range (N + 1), (g w).coeff i * ((X + C c) ^ i).coeff j := by
    funext w
    conv_lhs => rw [as_sum_range' (g w) (N + 1) (by have := hdeg w; omega : (g w).natDegree < N + 1)]
    rw [map_sum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (monomial i ((g w).coeff i) : Polynomial ℝ) = (g w).coeff i • (X : Polynomial ℝ) ^ i from
        by rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial], map_smul, taylor_X_pow,
      Polynomial.coeff_smul, smul_eq_mul]
  rw [hrepr]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (hcoeff i).mul analyticAt_const

/-- Evaluation under the Taylor shift. -/
lemma eval_taylor {R : Type*} [CommRing R] (c b : R) (q : R[X]) :
    (taylor c q).eval b = q.eval (b + c) := by
  rw [taylor_apply, eval_comp, eval_add, eval_X, eval_C]


/-- Root multiplicity under the Taylor shift: `(taylor c q).rootMultiplicity b = q.rootMultiplicity (b+c)`. -/
lemma rootMultiplicity_taylor {R : Type*} [CommRing R] (c b : R) (q : R[X]) :
    (taylor c q).rootMultiplicity b = q.rootMultiplicity (b + c) := by
  have h1 : (taylor c q).rootMultiplicity b = ((taylor c q).comp (X + C b)).rootMultiplicity 0 :=
    Polynomial.rootMultiplicity_eq_rootMultiplicity
  have h2 : (taylor c q).comp (X + C b) = q.comp (X + C (b + c)) := by
    rw [taylor_apply, Polynomial.comp_assoc]
    congr 1
    rw [add_comp, X_comp, C_comp, C_add]; ring
  have h3 : q.rootMultiplicity (b + c) = (q.comp (X + C (b + c))).rootMultiplicity 0 :=
    Polynomial.rootMultiplicity_eq_rootMultiplicity
  rw [h1, h2, h3]

end
