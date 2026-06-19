import Cad.Multivariate.ProjectionTheorem.Generalized.ComplexCovering
import Cad.Multivariate.ProjectionTheorem.Puiseux.RootFactor
import Cad.Multivariate.ProjectionTheorem.Puiseux.Connectedness

/-!
# C4.3 instantiation — local root sections enumerate the fibre

This file connects the reactivated analytic covering infrastructure (`local_disjoint_root_sections`,
`separable_distinct_simple_roots`, `evalFamily_analyticAt`, `evalFamily_fderiv_t`) to the abstract
gluing lemma `globalPartialProd_analyticAt`: at a point `y₀` where the family `q` is separable, there
is a neighbourhood `V` on which `d` analytic sections `φ i` enumerate the roots of `q y` (distinctly).
This discharges the `hroots`/`hinj`/`hφ` hypotheses of the global factor's analyticity.
-/

open Polynomial

/-- **Clopen-over-a-subspace constancy.** Variant of `clopen_mem_const_of_continuous` where `A` is only
required to be clopen in a *subspace* `C` containing the whole range of the continuous map `s`. This is
what makes the connectedness arguments non-vacuous over the **branched** root variety: we take `C` to be
the cover over the separable locus (which excludes the branch points), where nontrivial clopens exist —
a clopen of the full `rootVariety` containing a branch point must contain every colliding sheet, which
would force one side of any split to be empty. -/
theorem clopen_mem_const_over_sub {E V' : Type*} [TopologicalSpace E] [TopologicalSpace V']
    [PreconnectedSpace V'] {s : V' → E} (hs : Continuous s) {C : Set E} (hsC : ∀ v, s v ∈ C)
    {A : Set E} (hA : IsClopen (Subtype.val ⁻¹' A : Set ↥C)) {v₀ v₁ : V'} (hmem : s v₀ ∈ A) :
    s v₁ ∈ A :=
  clopen_mem_const_of_continuous (s := fun v => (⟨s v, hsC v⟩ : ↥C)) (hs.subtype_mk hsC) hA
    (v₀ := v₀) (v₁ := v₁) hmem

/-- **`A` is clopen over the base `U`**: its restriction to the cover `rootProj⁻¹ U` (which excludes the
branch points when `q` is separable on `U`) is clopen. This is the non-vacuous replacement for
`IsClopen A` on the full branched `rootVariety`: over the punctured base the sheets no longer collide,
so genuine splittings exist and the count conditions `1 ≤ d_A`, `1 ≤ d_B` become satisfiable. -/
def IsClopenOverBase {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (U : Set (Fin n → ℂ))
    (A : Set ↥(rootVariety q)) : Prop :=
  IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U))

theorem IsClopenOverBase.compl {n : ℕ} {q : (Fin n → ℂ) → Polynomial ℂ} {U : Set (Fin n → ℂ)}
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) : IsClopenOverBase q U Aᶜ := by
  unfold IsClopenOverBase at hA ⊢
  rw [Set.preimage_compl]
  exact hA.compl

/-- **Local analytic root sections enumerating the fibre.** At a separable point `y₀` of a monic
degree-`d` analytic family `q`, there is an open neighbourhood `V ∋ y₀` and analytic sections
`φ : Fin d → (Fin n → ℂ) → ℂ` such that for every `y ∈ V`, the values `φ i y` are *distinct* and form
*exactly* the root set of `q y`. -/
theorem exists_local_root_sections {n d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {y₀ : Fin n → ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y₀)
    (hsep : (q y₀).Separable)
    (B : Set (Fin n → ℂ)) (hBopen : IsOpen B) (hy₀B : y₀ ∈ B) :
    ∃ (V : Set (Fin n → ℂ)) (φ : Fin d → (Fin n → ℂ) → ℂ),
      IsOpen V ∧ y₀ ∈ V ∧ IsPreconnected V ∧ V ⊆ B ∧
      (∀ i, AnalyticOn ℂ (φ i) V) ∧
      (∀ y ∈ V, Function.Injective (fun i => φ i y)) ∧
      (∀ y ∈ V, (q y).roots.toFinset = Finset.univ.image (fun i => φ i y)) := by
  classical
  -- the `d` distinct simple roots of `q y₀`
  obtain ⟨t, ht_inj, ht_roots, ht_simple⟩ :=
    separable_distinct_simple_roots (q y₀) d (hmonic y₀) (hdeg y₀) hsep
  set F : (Fin n → ℂ) × ℂ → ℂ := fun p => (q p.1).eval p.2 with hF
  have hroot : ∀ j, F (y₀, t j) = 0 := fun j => (ht_roots (t j)).mpr ⟨j, rfl⟩
  have hF_an : ∀ j, AnalyticAt ℂ F (y₀, t j) :=
    fun j => evalFamily_analyticAt q hdeg (t j) hcoeff
  have hsimple : ∀ j, fderiv ℂ F (y₀, t j) (0, 1) ≠ 0 := by
    intro j
    rw [evalFamily_fderiv_t q hdeg (t j) hcoeff]
    exact ht_simple j
  obtain ⟨U, φ, hUopen, hy₀U, hφan, _hφval, hφroot, hφdisj⟩ :=
    local_disjoint_root_sections F y₀ d t ht_inj hF_an hroot hsimple
  -- shrink `U ∩ B` to an open ball `V ⊆ U ∩ B` around `y₀` (preconnected, inside the base `B`)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hUopen.inter hBopen) y₀ ⟨hy₀U, hy₀B⟩
  have hballU : Metric.ball y₀ r ⊆ U := fun x hx => (hball hx).1
  refine ⟨Metric.ball y₀ r, φ, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball y₀ r).isPreconnected, fun x hx => (hball hx).2,
    fun i => (hφan i).mono hballU, ?_, ?_⟩
  · intro y hy i j hij
    by_contra hne
    exact hφdisj i j hne y (hballU hy) hij
  · intro y hy
    refine roots_toFinset_eq_image_of_monic (hmonic y) (hdeg y) (fun i => φ i y) ?_ ?_
    · intro i j hij
      by_contra hne
      exact hφdisj i j hne y (hballU hy) hij
    · intro i
      have := hφroot i y (hballU hy)
      rwa [hF] at this

open scoped Topology in
open Classical in
/-- **The Weierstrass factor of a clopen component is analytic on the separable locus.** For a clopen
component `A` of the root variety, the partial product over the roots of `q y` lying in `A` (`h_A`) has
analytic coefficients at every separable point `y₀`. Combines `exists_local_root_sections` (sections
enumerate the roots), `clopen_mem_const_of_continuous` (component membership is locally constant along
sheets — single-valuedness), and `globalPartialProd_analyticAt` (the gluing). -/
theorem factor_coeff_analyticAt {n d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {y₀ : Fin n → ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y₀)
    (hsep : (q y₀).Separable)
    {U : Set (Fin n → ℂ)} (hUopen : IsOpen U) (hy₀U : y₀ ∈ U)
    (A : Set ↥(rootVariety q)) (hA : IsClopenOverBase q U A) (j : ℕ) :
    AnalyticAt ℂ (fun y => ((q y).roots.toFinset.filter
        (fun t => (y, t) ∈ (Subtype.val '' A))).prod
        (fun t => X - C t) |>.coeff j) y₀ := by
  classical
  have hA' : IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U)) := hA
  obtain ⟨V, φ, hVopen, hy₀V, hVconn, hVU, hφan, hφinj, hφroots⟩ :=
    exists_local_root_sections q hmonic hdeg hcoeff hsep U hUopen hy₀U
  have hVnhds : V ∈ 𝓝 y₀ := hVopen.mem_nhds hy₀V
  have hroot : ∀ i, ∀ y, y ∈ V → (q y).eval (φ i y) = 0 := by
    intro i y hy
    have hmem : φ i y ∈ (q y).roots.toFinset := by
      rw [hφroots y hy]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic y).ne_zero] at hmem
    exact hmem
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hVconn
  let P : (Fin n → ℂ) → ℂ → Prop := fun y t => (y, t) ∈ (Subtype.val '' A)
  have hconst : ∀ i, ∀ y ∈ V, (P y (φ i y) ↔ P y₀ (φ i y₀)) := by
    intro i y hy
    set σ : V → ↥(rootVariety q) := fun v => ⟨(v.1, φ i v.1), hroot i v.1 v.2⟩ with hσ
    have hσcont : Continuous σ :=
      (continuous_subtype_val.prodMk ((hφan i).continuousOn.restrict)).subtype_mk
        (fun v => hroot i v.1 v.2)
    have hsC : ∀ v : V, σ v ∈ rootProj q ⁻¹' U := fun v => hVU v.2
    have hPσ : ∀ z (hz : z ∈ V), (P z (φ i z) ↔ σ ⟨z, hz⟩ ∈ A) := by
      intro z hz
      constructor
      · rintro ⟨a, ha, hav⟩
        have heq : a = σ ⟨z, hz⟩ := Subtype.ext hav
        rwa [heq] at ha
      · intro hmem; exact ⟨σ ⟨z, hz⟩, hmem, rfl⟩
    rw [hPσ y hy, hPσ y₀ hy₀V]
    exact ⟨fun h => clopen_mem_const_over_sub hσcont hsC hA' h,
      fun h => clopen_mem_const_over_sub hσcont hsC hA' h⟩
  have hφan₀ : ∀ i, AnalyticAt ℂ (φ i) y₀ := fun i => (hφan i).analyticAt hVnhds
  exact globalPartialProd_analyticAt q φ P hVnhds hφroots hφinj hconst hφan₀ j

/-- **The factorisation `q = h_A · h_B` on the separable locus.** At a separable point the family value
splits as the product over the `P`-roots times the product over the `¬P`-roots — the algebraic identity
that, propagated across `0` by the identity theorem, yields the Weierstrass factorisation contradicting
irreducibility. -/
theorem family_eq_factor_mul {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) {y : Fin n → ℂ} (hsep : (q y).Separable)
    (P : ℂ → Prop) [DecidablePred P] :
    q y = ((q y).roots.toFinset.filter P).prod (fun t => X - C t)
        * ((q y).roots.toFinset.filter (fun t => ¬ P t)).prod (fun t => X - C t) :=
  eq_prod_filter_mul_prod_filter_not_of_monic_separable (hmonic y) hsep P

open Classical in
/-- **Component membership of a sheet is locally constant.** Along a continuous root branch `φ` over a
preconnected `V`, membership of the sheet `(y, φ y)` in a clopen component `A` does not vary. This is
the single-section single-valuedness core, extracted for reuse in both `factor_coeff_analyticAt` (the
factor's coefficients) and `aRootCount_eventually_eq` (the factor's degree). -/
theorem sheet_mem_locally_const {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {V : Set (Fin n → ℂ)} (hVconn : IsPreconnected V) {φ : (Fin n → ℂ) → ℂ}
    (hφroot : ∀ y ∈ V, (q y).eval (φ y) = 0) (hφcont : ContinuousOn φ V)
    {U : Set (Fin n → ℂ)} (hVU : V ⊆ U)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A)
    {y₀ y : Fin n → ℂ} (hy₀ : y₀ ∈ V) (hy : y ∈ V) :
    ((y, φ y) ∈ (Subtype.val '' A) ↔ (y₀, φ y₀) ∈ (Subtype.val '' A)) := by
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hVconn
  have hA' : IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U)) := hA
  set σ : V → ↥(rootVariety q) := fun v => ⟨(v.1, φ v.1), hφroot v.1 v.2⟩ with hσ
  have hσcont : Continuous σ :=
    (continuous_subtype_val.prodMk (hφcont.restrict)).subtype_mk (fun v => hφroot v.1 v.2)
  have hsC : ∀ v : V, σ v ∈ rootProj q ⁻¹' U := fun v => hVU v.2
  have hPσ : ∀ z (hz : z ∈ V), ((z, φ z) ∈ (Subtype.val '' A) ↔ σ ⟨z, hz⟩ ∈ A) := by
    intro z hz
    constructor
    · rintro ⟨a, ha, hav⟩
      have heq : a = σ ⟨z, hz⟩ := Subtype.ext hav
      rwa [heq] at ha
    · intro hmem; exact ⟨σ ⟨z, hz⟩, hmem, rfl⟩
  rw [hPσ y hy, hPσ y₀ hy₀]
  exact ⟨fun h => clopen_mem_const_over_sub hσcont hsC hA' h,
    fun h => clopen_mem_const_over_sub hσcont hsC hA' h⟩

open scoped Topology in
open Classical in
/-- **The `A`-root count is locally constant.** Near a separable point `y₀`, the number of roots of
`q y` lying in a clopen component `A` is constant. (The roots are the distinct section values, and
component membership is locally constant by `sheet_mem_locally_const`.) Propagated over the connected
punctured disc, this gives the constant degree `d_A` of the Weierstrass factor `h_A`. -/
theorem aRootCount_eventually_eq {n d : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {y₀ : Fin n → ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y₀)
    (hsep : (q y₀).Separable)
    {U : Set (Fin n → ℂ)} (hUopen : IsOpen U) (hy₀U : y₀ ∈ U)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) :
    ∀ᶠ y in 𝓝 y₀, ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).card
        = ((q y₀).roots.toFinset.filter (fun t => (y₀, t) ∈ (Subtype.val '' A))).card := by
  obtain ⟨V, φ, hVopen, hy₀V, hVconn, hVU, hφan, hφinj, hφroots⟩ :=
    exists_local_root_sections q hmonic hdeg hcoeff hsep U hUopen hy₀U
  have hroot : ∀ i, ∀ y ∈ V, (q y).eval (φ i y) = 0 := by
    intro i y hy
    have hmem : φ i y ∈ (q y).roots.toFinset := by
      rw [hφroots y hy]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic y).ne_zero] at hmem
    exact hmem
  have key : ∀ z ∈ V, ((q z).roots.toFinset.filter (fun t => (z, t) ∈ (Subtype.val '' A))).card
      = (Finset.univ.filter (fun i => (z, φ i z) ∈ (Subtype.val '' A))).card := by
    intro z hz
    rw [hφroots z hz, Finset.filter_image, Finset.card_image_of_injective _ (hφinj z hz)]
  filter_upwards [hVopen.mem_nhds hy₀V] with y hy
  rw [key y hy, key y₀ hy₀V]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact sheet_mem_locally_const q hVconn (hroot i) ((hφan i).continuousOn) hVU hA hy₀V hy

/-- **`Aᶜ`-membership equals non-`A`-membership on the root variety.** For a root `t` of `q y` (so
`(y, t)` is a genuine sheet), the sheet lies in the complementary component `Aᶜ` iff it does not lie in
`A`. This identifies the `B = Aᶜ` partial product (`h_{Aᶜ}`) with the `¬A` factor of
`family_eq_factor_mul`. -/
theorem mem_image_compl_iff_not_mem_image {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ)
    {A : Set ↥(rootVariety q)} {y : Fin n → ℂ} {t : ℂ} (ht : (q y).eval t = 0) :
    ((y, t) ∈ (Subtype.val '' Aᶜ)) ↔ ¬ ((y, t) ∈ (Subtype.val '' A)) := by
  have hmem : ((y, t) : (Fin n → ℂ) × ℂ) ∈ rootVariety q := ht
  constructor
  · rintro ⟨a, ha, hav⟩ hAmem
    obtain ⟨b, hb, hbv⟩ := hAmem
    have hab : a = b := Subtype.ext (hav.trans hbv.symm)
    rw [hab] at ha
    exact ha hb
  · intro hnA
    exact ⟨⟨(y, t), hmem⟩, fun hb => hnA ⟨⟨(y, t), hmem⟩, hb, rfl⟩, rfl⟩

open Classical in
/-- The `Aᶜ`-partial product equals the `¬A` factor of `family_eq_factor_mul`. -/
theorem factor_compl_eq {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (hmonic : ∀ y, (q y).Monic)
    {A : Set ↥(rootVariety q)} (y : Fin n → ℂ) :
    ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' Aᶜ))).prod (fun t => X - C t)
      = ((q y).roots.toFinset.filter
          (fun t => ¬ ((y, t) ∈ (Subtype.val '' A)))).prod (fun t => X - C t) :=
  Finset.prod_congr (Finset.filter_congr (fun t ht => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic y).ne_zero] at ht
    exact mem_image_compl_iff_not_mem_image q ht)) (fun _ _ => rfl)
