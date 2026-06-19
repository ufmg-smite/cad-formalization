import Cad.Multivariate.ProjectionTheorem.Order
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Vanishing order is invariant under a continuous linear equivalence

`order_comp_continuousLinearEquiv`: for a continuous linear equivalence `g : G ≃L[𝕜] E` and any
`f : E → F`, the vanishing `order` of `f ∘ g` at `x` equals the order of `f` at `g x`. This is the
exact transport tool used to move the `analyticAt_complexify` / order machinery (stated over
`Fin n → ·`) onto the *product* parameter space `CParam s e = (Fin s → ℂ) × (Fin e → ℂ)` via a
reindexing equivalence.

The proof uses `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`: each iterated derivative of
`f ∘ g` is the image of the corresponding derivative of `f` under the *equivalence*
`continuousMultilinearMapCongrLeft`, so one is zero iff the other is — hence the `Nat.find` indices
defining the order agree.
-/

noncomputable section

open Set
open scoped Topology

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Each iterated derivative of `f ∘ g` (for a continuous linear equiv `g`) is the image of the
corresponding derivative of `f` under the `continuousMultilinearMapCongrLeft` equivalence. -/
theorem iteratedFDeriv_comp_continuousLinearEquiv (g : G ≃L[𝕜] E) (f : E → F) (x : G) (n : ℕ) :
    iteratedFDeriv 𝕜 n (f ∘ g) x =
      ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F (fun _ : Fin n => g)
        (iteratedFDeriv 𝕜 n f (g x)) := by
  have h := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (g x)) n
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [h]; rfl

/-- **Order is invariant under a continuous linear equivalence (on the right).** -/
theorem order_comp_continuousLinearEquiv (g : G ≃L[𝕜] E) (f : E → F) (x : G) :
    order 𝕜 (f ∘ g) x = order 𝕜 f (g x) := by
  have hiff : ∀ n, iteratedFDeriv 𝕜 n (f ∘ g) x = 0 ↔ iteratedFDeriv 𝕜 n f (g x) = 0 := by
    intro n
    rw [iteratedFDeriv_comp_continuousLinearEquiv g f x n,
      map_eq_zero_iff _ (ContinuousLinearEquiv.injective _)]
  have hne : ∀ n, iteratedFDeriv 𝕜 n (f ∘ g) x ≠ 0 ↔ iteratedFDeriv 𝕜 n f (g x) ≠ 0 :=
    fun n => not_congr (hiff n)
  classical
  unfold order
  split_ifs with h1 h2 h2
  · exact congrArg _ (le_antisymm
      (Nat.find_le ((hne _).mpr (Nat.find_spec h2)))
      (Nat.find_le ((hne _).mp (Nat.find_spec h1))))
  · exact absurd (h1.imp fun n hn => (hne n).mp hn) h2
  · exact absurd (h2.imp fun n hn => (hne n).mpr hn) h1
  · rfl

end
