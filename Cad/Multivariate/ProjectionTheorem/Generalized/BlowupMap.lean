import Cad.Multivariate.ProjectionTheorem.Generalized.BlowupNormalForm
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs
import Mathlib.Analysis.Analytic.Constructions

/-!
# M5b — the blow-up substitution map

The thesis Case II quadratic transformation, with `e = k + 2`. The blow-up
`Q : (Fin s → ℂ) × (Fin (k+1) → ℂ) × ℂ → CParam s (k+2)` is
`Q (y, v, u) = (y, Fin.snoc (fun i => v i * u) u)`: it keeps the section `y`, scales the first `k+1`
transverse coordinates by the distinguished coordinate `u`, and keeps `u` as the last transverse
coordinate. This collapses the hyperplane `{u = 0}` onto the section `{transverse = 0}`.

The crucial **line identity** `Q (y, v, t) = (y, 0) + t • (0, Fin.snoc v 1)` exhibits, for fixed
`(y, v)`, the `u`-slice as a straight line in the transverse direction `(0, Fin.snoc v 1)`. Combined
with `BlowupNormalForm.iteratedDeriv_line_eq`, this turns the order-vanishing of the discriminant into
the jet hypothesis of `div_coord0_pow`.
-/

noncomputable section

open Filter
open scoped Topology

namespace BlowupMap

variable {s k : ℕ}

/-- The blow-up substitution `(y, v, u) ↦ (y, snoc (v·u) u)`. -/
def Q (p : (Fin s → ℂ) × (Fin (k + 1) → ℂ) × ℂ) : CParam s (k + 2) :=
  (p.1, Fin.snoc (fun i => p.2.1 i * p.2.2) p.2.2)

@[simp] lemma Q_apply (y : Fin s → ℂ) (v : Fin (k + 1) → ℂ) (u : ℂ) :
    Q (y, v, u) = (y, Fin.snoc (fun i => v i * u) u) := rfl

/-- The blow-up fixes the origin. -/
@[simp] lemma Q_zero : Q (0 : (Fin s → ℂ) × (Fin (k + 1) → ℂ) × ℂ) = 0 := by
  rw [show (0 : (Fin s → ℂ) × (Fin (k + 1) → ℂ) × ℂ) = ((0 : Fin s → ℂ), (0 : Fin (k+1) → ℂ), (0:ℂ))
    from rfl, Q_apply]
  refine Prod.ext rfl ?_
  funext i
  refine Fin.lastCases ?_ ?_ i <;> simp

/-- **The line identity.** For fixed `(y, v)`, the `u`-slice of `Q` is the straight transverse line
`(y, 0) + t • (0, Fin.snoc v 1)`. -/
lemma Q_line (y : Fin s → ℂ) (v : Fin (k + 1) → ℂ) (t : ℂ) :
    Q (y, v, t) = (((y, 0) : CParam s (k + 2))
      + t • ((0, (Fin.snoc v 1 : Fin (k + 2) → ℂ)) : CParam s (k + 2))) := by
  rw [Q_apply]
  refine Prod.ext (by simp) ?_
  show (Fin.snoc (fun i => v i * t) t : Fin (k + 2) → ℂ)
    = (0 : Fin (k + 2) → ℂ) + t • (Fin.snoc v 1 : Fin (k + 2) → ℂ)
  rw [zero_add]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j; simp [mul_comm]

end BlowupMap
