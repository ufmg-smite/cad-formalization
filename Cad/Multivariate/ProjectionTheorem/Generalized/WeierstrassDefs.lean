import Cad.Multivariate.ProjectionTheorem.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Weierstrass-preparation definitions (axiom-free base)

The parameter space `CParam`, the Weierstrass polynomial `weierstrassPoly`, its discriminant
`weierstrassDiscFn`, and their basic algebraic/analytic properties (monic, degree, evaluation,
order on the section). This is the **axiom-free base** of the convergent-Weierstrass development:
it is imported both by the proof chain that *discharges* the division axiom (`CWeierstrassSynthesis`
and below) and by the file that packages the resulting theorems (`WeierstrassZariskiAxioms`), so the
latter can import the former without a cycle.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

/-- Complexified parameter space: `s` section variables × `e` transverse variables. -/
abbrev CParam (s e : ℕ) : Type := (Fin s → ℂ) × (Fin e → ℂ)

/-- The monic degree-`m` polynomial `t^m + ∑_{i<m} a_i(w)·t^i` (a Weierstrass polynomial in `t`
when `a_i(0) = 0`), with coefficients evaluated at the parameter point `w`. -/
def weierstrassPoly {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) (w : CParam s e) :
    Polynomial ℂ :=
  X ^ m + ∑ i : Fin m, C (a i w) * X ^ (i : ℕ)

/-- The discriminant of the section Weierstrass polynomial, as a function of the *full* parameter
`w` (its order along the section `T` is the Zariski equisingularity invariant). -/
def weierstrassDiscFn {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) :
    CParam s e → ℂ :=
  fun w => Polynomial.discr (weierstrassPoly m a w)

/-- A Weierstrass polynomial is **monic** (leading term `X^m`, the rest of degree `< m`). -/
theorem weierstrassPoly_monic {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) (w : CParam s e) :
    (weierstrassPoly m a w).Monic := by
  rw [weierstrassPoly]
  exact monic_X_pow_add (degree_sum_fin_lt (fun i => a i w))

/-- A Weierstrass polynomial has **degree exactly `m`**. -/
theorem weierstrassPoly_natDegree {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (w : CParam s e) : (weierstrassPoly m a w).natDegree = m := by
  rw [weierstrassPoly]
  have hdeg : (X ^ m + ∑ i : Fin m, C (a i w) * X ^ (i : ℕ) : Polynomial ℂ).degree = (m : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt (fun i => a i w)
  exact natDegree_eq_of_degree_eq_some hdeg

/-- Pointwise expansion of the Weierstrass polynomial's evaluation. -/
lemma weierstrassPoly_eval_eq {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (w : CParam s e) (t : ℂ) :
    (weierstrassPoly m a w).eval t = t ^ m + ∑ i : Fin m, a i w * t ^ (i : ℕ) := by
  simp only [weierstrassPoly, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]

/-- The Weierstrass polynomial's evaluation `(w,t) ↦ h(w,t)` is analytic at `0`. -/
lemma weierstrassPolyEval_analyticAt {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2) 0 := by
  have heq : (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
      = fun wt => wt.2 ^ m + ∑ i : Fin m, a i wt.1 * wt.2 ^ (i : ℕ) :=
    funext fun wt => weierstrassPoly_eval_eq m a wt.1 wt.2
  rw [heq]
  have hsnd : AnalyticAt ℂ (fun wt : CParam s e × ℂ => wt.2) 0 := analyticAt_snd
  have hfst : AnalyticAt ℂ (fun wt : CParam s e × ℂ => wt.1) 0 := analyticAt_fst
  refine (hsnd.pow m).add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
  exact ((ha_an i).comp_of_eq hfst rfl).mul (hsnd.pow (i : ℕ))

/-- On the distinguished line `w = 0`, the Weierstrass polynomial is `t ↦ t^m`, of order `m`. -/
lemma weierstrassPolyEval_order {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha0 : ∀ i, a i 0 = 0) :
    analyticOrderAt (fun t : ℂ => (weierstrassPoly m a (0 : CParam s e)).eval t) 0 = (m : ℕ∞) := by
  have heq : (fun t : ℂ => (weierstrassPoly m a (0 : CParam s e)).eval t) = fun t : ℂ => t ^ m := by
    funext t; rw [weierstrassPoly_eval_eq]; simp [ha0]
  rw [heq, show (fun t : ℂ => t ^ m) = (id : ℂ → ℂ) ^ m from rfl,
    analyticOrderAt_pow analyticAt_id m, analyticOrderAt_id]
  simp [nsmul_eq_mul]

end
