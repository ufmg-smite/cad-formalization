import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Cad.Multivariate.ProjectionTheorem.Order
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic

/-!
# The local ring of holomorphic germs `𝒪ₙ` (Phase B1)

`AnalyticGerm n` is the subring of germs at `0 ∈ ℂⁿ` of functions analytic at `0`. It is the
base ring `𝒪ₙ` over which the Weierstrass polynomial lives in McCallum's proof (the substrate for
`norm_identity_elim` and the discriminant-order argument). Being a `Subring` of the germ ring, it
is automatically a `CommRing`.

Germs are the right object because Weierstrass preparation produces a factorization on an
*arbitrarily small* neighborhood; germs quotient out the shrinking neighborhood.
-/

noncomputable section

open Filter Topology

/-! ## B2 — the vanishing order / valuation on `𝒪ₙ` -/

/-- If all `< k` Fréchet derivatives of `f` vanish at `x`, then `k ≤ order f x` (field-generic). -/
theorem le_order_of_forall_iteratedFDeriv_eq_zero'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x : E} {k : ℕ∞}
    (h : ∀ j : ℕ, (↑j : ℕ∞) < k → iteratedFDeriv 𝕜 j f x = 0) :
    k ≤ order 𝕜 f x := by
  by_contra hlt
  push_neg at hlt
  have hfin : order 𝕜 f x ≠ ⊤ := ne_top_of_lt hlt
  have hm : order 𝕜 f x = ↑(order 𝕜 f x).toNat := (ENat.coe_toNat hfin).symm
  rw [hm] at hlt
  exact (((order_eq_natCast_iff).mp hm).2) (h _ hlt)

/-- The vanishing `order` depends only on the germ (field-generic version of
`order_congr_of_eventuallyEq`, which is fixed to `ℝ`). -/
theorem order_congr_of_eventuallyEq'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    order 𝕜 f₁ x = order 𝕜 f₂ x := by
  have key : ∀ m : ℕ, iteratedFDeriv 𝕜 m f₁ x = iteratedFDeriv 𝕜 m f₂ x :=
    fun m => (h.iteratedFDeriv 𝕜 m).eq_of_nhds
  apply le_antisymm
  · apply le_order_of_forall_iteratedFDeriv_eq_zero'
    intro j hj
    rw [← key]; exact iteratedFDeriv_eq_zero_of_lt_order hj
  · apply le_order_of_forall_iteratedFDeriv_eq_zero'
    intro j hj
    rw [key]; exact iteratedFDeriv_eq_zero_of_lt_order hj

end
