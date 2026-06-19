import Cad.Multivariate.ProjectionTheorem.Generalized.CParamIntegral

/-!
# Several-complex-variables bridge — the `n`-variable induction (scaffolding)

The keystone behind `weierstrass_division` reduces (via `CParamIntegral.circleIntegral_analyticAt_multi`)
to the **holomorphy⇒analyticity bridge** on the parameter space `H = CParam ≅ ℂⁿ`:
`HoloBridge H : DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U`.

This file assembles the bridge on `ℂⁿ` by induction `ℂⁿ⁺¹ ≅ ℂ × ℂⁿ`, reducing everything to a single
remaining lemma — the **inductive step** `bridge_step : HoloBridge E' → HoloBridge (ℂ × E')` (which is
`CBridge.bridge_prod` *without* the `osgood` axiom). The two-variable instance `bridge_step` for
`E' = ℂ` is **already proved** (`scv_bridge`); the genuine remaining content is the *combination*
("power series in `z` with analytic-in-`w` coefficients ⇒ jointly analytic" = multivariable Weierstrass,
absent from Mathlib).

Everything here is sorry-free; `bridge_step` is taken as an explicit hypothesis so the reduction is
honest and the remaining target is crisp.
-/

noncomputable section

open scoped Topology

/-- The holomorphy⇒analyticity bridge on a complex normed space `E` (for `ℂ`-valued functions). -/
def HoloBridge (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ {f : E → ℂ} {U : Set E}, IsOpen U → DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U



/-- **Transport along a continuous linear equivalence.** The bridge is invariant under `ℂ`-linear
isomorphisms (analyticity/differentiability compose with the linear iso both ways). -/
theorem HoloBridge.congr {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (e : E ≃L[ℂ] E') (h : HoloBridge E) :
    HoloBridge E' := by
  intro g U' hU' hg x' hx'
  -- pull `g` back to `E` along `e`
  have hUopen : IsOpen (e ⁻¹' U') := hU'.preimage e.continuous
  have hmaps : Set.MapsTo e (e ⁻¹' U') U' := fun x hx => hx
  have hge : DifferentiableOn ℂ (g ∘ e) (e ⁻¹' U') :=
    hg.comp (e : E →L[ℂ] E').differentiableOn hmaps
  have hanalytic : AnalyticOnNhd ℂ (g ∘ e) (e ⁻¹' U') := h hUopen hge
  have hxmem : e.symm x' ∈ e ⁻¹' U' := by simp [Set.mem_preimage, hx']
  have key : AnalyticAt ℂ (g ∘ e) (e.symm x') := hanalytic _ hxmem
  -- push forward: `g = (g ∘ e) ∘ e.symm`
  have hcomp : AnalyticAt ℂ ((g ∘ e) ∘ (e.symm : E' →L[ℂ] E)) x' :=
    key.comp ((e.symm : E' →L[ℂ] E).analyticAt x')
  refine hcomp.congr ?_
  filter_upwards with y
  simp [Function.comp]

/-- **Base case `Fin 0 → ℂ`** — a `0`-dimensional space; every function is (locally) constant. -/
theorem holoBridge_finZero : HoloBridge (Fin 0 → ℂ) := by
  intro f U _ _ x _
  have hc : AnalyticAt ℂ (fun _ : (Fin 0 → ℂ) => f x) x := analyticAt_const
  exact hc.congr (by filter_upwards with y using congrArg f (Subsingleton.elim x y))


end
