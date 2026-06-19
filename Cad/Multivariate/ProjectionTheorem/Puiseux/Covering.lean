import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Connected.LocPathConnected

/-!
# C1: the `uᵐ` reference cover and its transitive monodromy

The convergent/covering route to the Puiseux parametrization identifies the connected root-covering of
the punctured disc with the standard `m`-fold cover `u ↦ uᵐ : ℂ* → ℂ*` (`isCoveringMap_npow`, Mathlib).
This file lays the foundation:

* `transitive_monodromy_of_pathConnected` — path-connected total space ⟹ transitive monodromy
  (reusable; recalled from the archived monodromy work, fully proved);
* `Complex.instPathConnectedSpaceNeZero` — `ℂ* = {z ≠ 0}` is path-connected (`ℝ²` minus a point);
* `isCoveringMap_npow_transitive` — the `uᵐ` cover has transitive monodromy: any two points of one
  fiber are joined by a base loop whose lift carries one to the other. This is the structural input to
  the cover classification (C2).
-/

noncomputable section

open Topology

/-- **Path-connected total space ⟹ transitive monodromy.** For a covering `p : E → X` with `E`
path-connected, any two points `e₀, e₁` of the same fiber are joined by a base loop `γ` whose lift
from `e₀` ends at `e₁`. (A path `δ : e₀ ⤳ e₁` projects to a loop `p ∘ δ`; by uniqueness of lifts the
lift of `p ∘ δ` from `e₀` is `δ`, ending at `e₁`.) -/
theorem transitive_monodromy_of_pathConnected {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) [PathConnectedSpace E]
    {e₀ e₁ : E} (hpe : p e₀ = p e₁) :
    ∃ (γ : C(unitInterval, X)) (hγ0 : γ 0 = p e₀),
      γ 1 = p e₀ ∧ cov.liftPath γ e₀ hγ0 1 = e₁ := by
  let δ : Path e₀ e₁ := PathConnectedSpace.somePath e₀ e₁
  let dc : C(unitInterval, E) := δ.toContinuousMap
  have h0 : dc 0 = e₀ := δ.source
  have h1 : dc 1 = e₁ := δ.target
  have hγ0 : (⟨p ∘ dc, cov.continuous.comp dc.continuous⟩ : C(unitInterval, X)) 0 = p e₀ := by
    show p (dc 0) = p e₀; rw [h0]
  refine ⟨⟨p ∘ dc, cov.continuous.comp dc.continuous⟩, hγ0, ?_, ?_⟩
  · show p (dc 1) = p e₀; rw [h1, hpe]
  · have hdceq : dc = cov.liftPath ⟨p ∘ dc, cov.continuous.comp dc.continuous⟩ e₀ hγ0 :=
      (cov.eq_liftPath_iff' (Γ := dc) hγ0).mpr ⟨rfl, h0⟩
    rw [← hdceq]; exact h1

/-! ### The `exp` universal-cover lift -/

/-- `exp : ℂ → ℂ*` as a continuous map into the punctured plane (the universal covering map of `ℂ*`,
`isCoveringMap_exp`). -/
def Complex.expNeZero : C(ℂ, {z : ℂ // z ≠ 0}) :=
  ⟨fun z => ⟨z.exp, z.exp_ne_zero⟩, Complex.continuous_exp.subtype_mk _⟩

end
