import Cad.Multivariate.ProjectionTheorem.Generalized.DiscNormalForm
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# M5 — coordinate translation infrastructure

Order-invariance of the analytic vanishing order under a continuous linear equivalence
(`order_comp_cle`). This is the central bridge for transporting the disc-order hypotheses of the
Zariski axiom (stated over `CParam s e`) to the `Fin (n+1) → ℂ` coordinates of M4/M5a.
-/

noncomputable section

open Filter
open scoped Topology

namespace CoordTranslate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Order is invariant under a continuous linear equivalence.** `order (f ∘ g) x = order f (g x)`
for `g` a CLE (the iterated Fréchet derivatives correspond bijectively). -/
lemma order_comp_cle (g : E ≃L[ℂ] F) (f : F → ℂ) (x : E) :
    order ℂ (f ∘ g) x = order ℂ f (g x) := by
  classical
  have hcomp : ∀ i, iteratedFDeriv ℂ i (f ∘ (g : E → F)) x
      = (iteratedFDeriv ℂ i f (g x)).compContinuousLinearMap fun _ => (g : E →L[ℂ] F) := by
    intro i
    have h := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right g f uniqueDiffOn_univ
      (Set.mem_univ (g x)) i
    rwa [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have hiff : ∀ i, iteratedFDeriv ℂ i (f ∘ (g : E → F)) x = 0
      ↔ iteratedFDeriv ℂ i f (g x) = 0 := by
    intro i
    rw [hcomp i]
    constructor
    · intro h
      ext m
      have hm := ContinuousMultilinearMap.ext_iff.mp h (fun j => g.symm (m j))
      simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousLinearEquiv.apply_symm_apply] using hm
    · intro h; rw [h]; ext m; simp
  have hneiff : ∀ i, iteratedFDeriv ℂ i (f ∘ (g : E → F)) x ≠ 0
      ↔ iteratedFDeriv ℂ i f (g x) ≠ 0 := fun i => (hiff i).not
  unfold order
  by_cases hex : ∃ i, iteratedFDeriv ℂ i (f ∘ (g : E → F)) x ≠ 0
  · have hex' : ∃ i, iteratedFDeriv ℂ i f (g x) ≠ 0 := by
      obtain ⟨i, hi⟩ := hex; exact ⟨i, (hneiff i).mp hi⟩
    rw [dif_pos hex, dif_pos hex']
    congr 1
    apply le_antisymm
    · exact Nat.find_min' hex ((hneiff _).mpr (Nat.find_spec hex'))
    · exact Nat.find_min' hex' ((hneiff _).mp (Nat.find_spec hex))
  · have hex' : ¬ ∃ i, iteratedFDeriv ℂ i f (g x) ≠ 0 := by
      push_neg at hex ⊢; intro i; exact (hiff i).mp (hex i)
    rw [dif_neg hex, dif_neg hex']

/-- The coordinate CLE `(Fin s → ℂ) × (Fin 1 → ℂ) ≃L (Fin (s+1) → ℂ)`, sending the `Fin 1` (transverse)
block to coordinate `0` and the `Fin s` (section) block to coordinates `1..s`. -/
def cparamEquiv (s : ℕ) : ((Fin s → ℂ) × (Fin 1 → ℂ)) ≃L[ℂ] (Fin (s + 1) → ℂ) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (Fin s → ℂ))
    (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ))).trans (coord0Equiv (n := s))

@[simp] lemma cparamEquiv_apply (s : ℕ) (y : Fin s → ℂ) (t : Fin 1 → ℂ) :
    cparamEquiv s (y, t) = Fin.cons (t 0) y := by
  simp only [cparamEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.piUnique_apply, coord0Equiv_apply]
  rfl

/-- `cparamEquiv` sends the section `{(y, 0)}` to the hyperplane `{z 0 = 0}` (coordinate `0`). -/
@[simp] lemma cparamEquiv_section (s : ℕ) (y : Fin s → ℂ) :
    cparamEquiv s (y, 0) 0 = 0 := by
  rw [cparamEquiv_apply, Fin.cons_zero]; rfl

/-- The inverse coordinate CLE: `z ↦ (tail z, constant z 0)`. -/
@[simp] lemma cparamEquiv_symm_apply (s : ℕ) (z : Fin (s + 1) → ℂ) :
    (cparamEquiv s).symm z = (Fin.tail z, fun _ : Fin 1 => z 0) := by
  simp only [cparamEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    coord0Equiv_symm_apply]
  refine Prod.ext rfl ?_
  ext i
  simp [ContinuousLinearEquiv.piUnique_symm_apply]

end CoordTranslate
