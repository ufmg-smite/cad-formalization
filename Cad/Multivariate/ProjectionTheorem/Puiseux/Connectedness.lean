import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Cad.Multivariate.ProjectionTheorem.Puiseux.RootFactor

open scoped Topology
open Filter

/-!
# C4.3 single-valuedness — clopen membership is locally constant along sheets

In the connectedness kernel (irreducible Weierstrass ⟹ root variety path-connected over the punctured
locus) we argue by contraposition: a clopen splitting `A` of the root cover `p : E → X` yields a
*partial product* `∏_{e ∈ fiber(w) ∩ A} (X - C (g e))` over the sheets belonging to `A`, and we must
know this is **single-valued** in `w` — i.e. that "which sheets lie in `A`" does not change as `w`
moves, so the local section-expressions of the partial product agree on overlaps and glue.

The topological heart of that single-valuedness is here: along a continuous section `s : X → E` of the
cover over a *preconnected* set `V`, membership in a clopen `A` is constant — if one sheet value lies
in `A`, all do. (The set `{w ∈ V : s w ∈ A}` is clopen in the preconnected `V`, nonempty, hence all of
`V`.) Applied to the local sheets of a covering map, this says the `A`-sheets over a connected base
neighbourhood are exactly those passing through `A` at any one point.
-/

/-- **Removable singularity (analytic update form).** If `f : ℂ → ℂ` is complex differentiable on a
punctured neighbourhood of `c` and bounded there (`‖f · - f c‖` bounded under `𝓝[≠] c`), then `f`
redefined at `c` to its limit is analytic at `c`. This is the extension across the discriminant point
`0` of the bounded, holomorphic-on-the-punctured-disc partial-product coefficients: it upgrades
`h_A`'s coefficients from holomorphic on `D∖{0}` to holomorphic on the full disc `D`. -/
theorem analyticAt_update_limUnder_of_bddUnder {f : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    AnalyticAt ℂ (Function.update f c (limUnder (𝓝[≠] c) f)) c := by
  set L := limUnder (𝓝[≠] c) f with hL
  set g := Function.update f c L with hg
  have hgd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ g z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hzf hzc
    have hzc' : z ≠ c := hzc
    have hgf : g =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hzc] with x hx
      exact Function.update_of_ne (hx : x ≠ c) L f
    exact (hgf.differentiableAt_iff).mpr hzf
  have htend : Filter.Tendsto f (𝓝[≠] c) (𝓝 L) :=
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hb
  have hgc : ContinuousAt g c := continuousAt_update_same.mpr htend
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc

/-- **Analytic extension across an isolated point (existence form).** A function analytic on a
punctured neighbourhood of `c` and bounded there extends to a function analytic *at* `c` that agrees
with it off `c`. This is the assembly-ready form of removable singularity: it turns the partial-product
coefficient (holomorphic on `D∖{0}`, bounded by root continuity) into a genuine holomorphic germ at
the discriminant point `0`, the coefficient of the Weierstrass factor `h_A`. -/
theorem exists_analyticAt_extend_of_bddUnder {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hb : Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F c ∧ F =ᶠ[𝓝[≠] c] f := by
  have hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z :=
    hf.mono fun _ hz => hz.differentiableAt
  refine ⟨Function.update f c (limUnder (𝓝[≠] c) f),
    analyticAt_update_limUnder_of_bddUnder hd hb, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact Function.update_of_ne (hz : z ≠ c) _ _

/-- **Analytic extension across an isolated point (uniform-bound form).** Variant of
`exists_analyticAt_extend_of_bddUnder` taking a plain uniform bound `‖f z‖ ≤ M` near `c` (rather than
`‖f z - f c‖`). This is the convenient form when `f` is only defined on the punctured neighbourhood and
its value at `c` carries no meaning — exactly the partial-product coefficient on the separable locus. -/
theorem exists_analyticAt_extend_of_bdd {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) {M : ℝ} (hb : ∀ᶠ z in 𝓝[≠] c, ‖f z‖ ≤ M) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F c ∧ F =ᶠ[𝓝[≠] c] f := by
  refine exists_analyticAt_extend_of_bddUnder hf ⟨M + ‖f c‖, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [hb] with z hz
  calc ‖f z - f c‖ ≤ ‖f z‖ + ‖f c‖ := norm_sub_le _ _
    _ ≤ M + ‖f c‖ := by linarith

/-- **Agreement off a point + at the point ⟹ agreement near the point.** If `H₁ = H₂` on a punctured
neighbourhood of `x` and `H₁ x = H₂ x`, then `H₁ = H₂` on a full neighbourhood of `x`. This is the
filter core of the identity-theorem propagation of the factorisation `q = H_A · H_B` from the
(dense) separable locus across the discriminant point `0`. -/
theorem eventuallyEq_nhds_of_nhdsWithin_ne {α β : Type*} [TopologicalSpace α]
    {H₁ H₂ : α → β} {x : α} (heq : H₁ =ᶠ[𝓝[≠] x] H₂) (hx : H₁ x = H₂ x) :
    H₁ =ᶠ[𝓝 x] H₂ := by
  have hdecomp : (𝓝 x : Filter α) = 𝓝[≠] x ⊔ 𝓝[{x}] x := by
    rw [← nhdsWithin_union, Set.compl_union_self, nhdsWithin_univ]
  rw [Filter.EventuallyEq, hdecomp, Filter.eventually_sup]
  exact ⟨heq, by rw [nhdsWithin_singleton, Filter.eventually_pure]; exact hx⟩

/-- **The punctured ball is path-connected (rank `> 1`).** Transported from the path-connectedness of
`E ∖ {0}` through the homeomorphism `univBall 0 r : E ≃ ball 0 r` (which fixes `0`). The connected
punctured disc is where the locally-constant factor degree `d_A` becomes globally constant. -/
theorem isPathConnected_ball_diff_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) {r : ℝ} (hr : 0 < r) :
    IsPathConnected ((Metric.ball (0 : E) r) \ {0}) := by
  have hcompl : IsPathConnected ({(0 : E)}ᶜ : Set E) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  have hcont : Continuous (OpenPartialHomeomorph.univBall (0 : E) r) :=
    OpenPartialHomeomorph.continuous_univBall 0 r
  have himg := hcompl.image hcont
  have himage : (OpenPartialHomeomorph.univBall (0 : E) r) '' ({(0 : E)}ᶜ)
      = Metric.ball (0 : E) r \ {0} := by
    have hinj : Set.InjOn (OpenPartialHomeomorph.univBall (0 : E) r) (Set.univ : Set E) := by
      have h := (OpenPartialHomeomorph.univBall (0 : E) r).injOn
      rwa [OpenPartialHomeomorph.univBall_source] at h
    rw [Set.compl_eq_univ_diff, hinj.image_diff]
    have htgt : (OpenPartialHomeomorph.univBall (0 : E) r) '' Set.univ = Metric.ball 0 r := by
      rw [← OpenPartialHomeomorph.univBall_source (0 : E) r,
        OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.univBall_target 0 hr]
    rw [htgt, Set.univ_inter, Set.image_singleton, OpenPartialHomeomorph.univBall_apply_zero]
  rw [← himage]; exact himg

/-- **Clopen membership is constant along a continuous map from a preconnected space.** The
subtype-friendly variant of `clopen_mem_const_of_continuousOn`: for `s : V' → E` continuous with `V'`
preconnected and `A` clopen, `s` lands entirely inside or outside `A`. Used with `V' = ↥V` and
`E = ↥(rootVariety q)` for the sheet sections `v ↦ (v, φ i v)`. -/
theorem clopen_mem_const_of_continuous {E V' : Type*} [TopologicalSpace E] [TopologicalSpace V']
    [PreconnectedSpace V'] {s : V' → E} (hs : Continuous s) {A : Set E} (hA : IsClopen A)
    {v₀ v₁ : V'} (hmem : s v₀ ∈ A) : s v₁ ∈ A := by
  have hcl : IsClopen (s ⁻¹' A) := ⟨hA.1.preimage hs, hA.2.preimage hs⟩
  have huniv := hcl.eq_univ ⟨v₀, hmem⟩
  have : v₁ ∈ s ⁻¹' A := huniv ▸ Set.mem_univ _
  exact this

open Classical Polynomial in
/-- **Single-valuedness of a filtered partial product (membership form).** If a sheet-membership
predicate `mem i ·` is *locally constant* near `y₀` (the abstract single-valuedness hypothesis, got
from `clopen_mem_const_of_continuousOn` when `mem` is membership in a clopen component), then the
partial product `∏_{i : mem i y} (X - C (φ i y))` has analytic coefficients at `y₀`. This is the
cover-agnostic core feeding the global factor `h_A`; it composes with `prod_X_sub_C_image_filter` to
turn a fiberwise root-set product into this section form. -/
theorem partialProd_mem_coeff_analyticAt
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {d : ℕ} (φ : Fin d → B → ℂ) (mem : Fin d → B → Prop) [∀ i, DecidablePred (mem i)]
    {V : Set B} {y₀ : B} (hVnhds : V ∈ 𝓝 y₀)
    (hconst : ∀ i, ∀ y ∈ V, (mem i y ↔ mem i y₀))
    (hφ : ∀ i, AnalyticAt ℂ (φ i) y₀) (j : ℕ) :
    AnalyticAt ℂ
      (fun y => (∏ i ∈ Finset.univ.filter (fun i => mem i y), (X - C (φ i y))).coeff j) y₀ := by
  set F₀ := Finset.univ.filter (fun i => mem i y₀) with hF₀
  have hbase : AnalyticAt ℂ (fun y => (∏ i ∈ F₀, (X - C (φ i y))).coeff j) y₀ :=
    analyticAt_coeff_prod_X_sub_C F₀ φ hφ j
  refine hbase.congr (Filter.eventually_of_mem hVnhds (fun y hy => ?_))
  have hfilter : Finset.univ.filter (fun i => mem i y) = F₀ := by
    rw [hF₀]; exact Finset.filter_congr (fun i _ => hconst i y hy)
  dsimp only
  rw [hfilter]

open Classical Polynomial in
/-- **The global fiberwise partial product is analytic at a separable point.** Over the separable
locus the roots of `q y` are the distinct values of analytic sections `φ i`; the partial product over
the roots in a (locally-constant) component `P` then agrees near `y₀` with the section form, hence is
analytic. This is the gluing step (d): it turns the global, fiberwise definition of the Weierstrass
factor `h_A` — a product over the actual root set of `q y` filtered by component membership — into a
holomorphic function on the separable locus.

Hypotheses (each dischargeable from the reactivated cover infrastructure
`separable_distinct_simple_roots` / `local_disjoint_root_sections`): on `V ∈ 𝓝 y₀` the sections
enumerate the roots (`hroots`), are distinct (`hinj`), the component membership is locally constant
along sheets (`hconst`), and the sections are analytic at `y₀` (`hφ`). -/
theorem globalPartialProd_analyticAt
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {d : ℕ} (q : B → Polynomial ℂ) (φ : Fin d → B → ℂ) (P : B → ℂ → Prop)
    {V : Set B} {y₀ : B} (hVnhds : V ∈ 𝓝 y₀)
    (hroots : ∀ y ∈ V, (q y).roots.toFinset = Finset.univ.image (fun i => φ i y))
    (hinj : ∀ y ∈ V, Function.Injective (fun i => φ i y))
    (hconst : ∀ i, ∀ y ∈ V, (P y (φ i y) ↔ P y₀ (φ i y₀)))
    (hφ : ∀ i, AnalyticAt ℂ (φ i) y₀) (j : ℕ) :
    AnalyticAt ℂ
      (fun y => ((q y).roots.toFinset.filter (P y)).prod (fun t => X - C t) |>.coeff j) y₀ := by
  have hmain := partialProd_mem_coeff_analyticAt φ (fun i y => P y (φ i y))
    hVnhds (fun i y hy => hconst i y hy) hφ j
  refine hmain.congr (Filter.eventually_of_mem hVnhds (fun y hy => ?_))
  dsimp only
  rw [hroots y hy, prod_X_sub_C_image_filter (fun i => φ i y) (hinj y hy) (P y)]
