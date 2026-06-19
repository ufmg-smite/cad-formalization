import Cad.Multivariate.ProjectionTheorem.Generalized.ConnectednessGen
import Cad.Multivariate.ProjectionTheorem.Generalized.Monodromy

/-!
# G3 — Lemma 4.2.5 over the general base `Fin (n+1) → ℂ`

Lifts the M1 chain (`rootCover_preconnected` → `rootCover_pathConnected` → `rootCover_exchange`) from the
degenerate base `Fin 1 → ℂ` to the general base `Fin (n+1) → ℂ`, using the generalized connectedness
kernel `clopen_split_contradiction'_gen` (`ConnectednessGen`) in place of the `Fin 1` one. The covering
machinery (`ComplexCovering`, `IsLocalHomeomorph.locPathConnectedSpace`,
`transitive_monodromy_of_pathConnected`) is already general-`n` and reused verbatim. The deleted-point
filter `𝓝[≠] 0` becomes the deleted-hyperplane filter `𝓝[{x 0 ≠ 0}] 0`.

This is Lemma 4.2.5 (transitive monodromy / root exchange) in the form the thesis proof of Theorem 4.2.2
actually needs (`rootCover_exchange_gen`).
-/

noncomputable section

open Polynomial Filter Set
open scoped Topology

variable {n : ℕ}

open Classical in
/-- The `W`-root count is `≥ 1` frequently along the deleted-hyperplane filter, given a witness sheet
`e ∈ W` over a point of `U`. `Fin (n+1)` analogue of `rootCover_count_pos_freq`. -/
private theorem rootCover_count_pos_freq_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {W : Set ↥(rootVariety q)} (hW : IsClopenOverBase q U W)
    {e : ↥(rootVariety q)} (heU : (e : (Fin (n + 1) → ℂ) × ℂ).1 ∈ U) (heW : e ∈ W) :
    ∃ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      1 ≤ ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' W))).card := by
  classical
  set cnt : (Fin (n + 1) → ℂ) → ℕ := fun x =>
    ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' W))).card with hcnt
  haveI : PreconnectedSpace (↥U) := Subtype.preconnectedSpace hUconn
  have hlc : IsLocallyConstant (fun v : ↥U => cnt v.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hev := aRootCount_eventually_eq q hmonic hdeg (fun i => hanaU i v.1 v.2) (hUsep v.1 v.2)
      hUopen v.2 (A := W) hW
    exact (continuous_subtype_val.continuousAt).eventually hev
  have hcnt_e : 1 ≤ cnt (e : (Fin (n + 1) → ℂ) × ℂ).1 := by
    rw [hcnt]
    apply Finset.card_pos.mpr
    refine ⟨(e : (Fin (n + 1) → ℂ) × ℂ).2, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic _).ne_zero]
      exact e.2
    · exact ⟨e, heW, rfl⟩
  refine Filter.Eventually.frequently ?_
  filter_upwards [hU0] with y hy
  have hconst : cnt y = cnt (e : (Fin (n + 1) → ℂ) × ℂ).1 :=
    hlc.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨_, heU⟩
  show 1 ≤ cnt y
  rw [hconst]; exact hcnt_e

open Classical in
/-- **G3 — the root cover over a general base is preconnected.** `Fin (n+1)` analogue of
`rootCover_preconnected`, resting on the generalized kernel `clopen_split_contradiction'_gen`. -/
theorem rootCover_preconnected_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducibleGen q)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε) :
    PreconnectedSpace ↥(rootProj q ⁻¹' U) := by
  classical
  have hsep : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → (q x).Separable :=
    eventually_nhdsWithin_iff.mp (by filter_upwards [hU0] with x hx using hUsep x hx)
  rw [preconnectedSpace_iff_clopen]
  intro A hAcl
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hAne_empty, hAne_univ⟩ := hcon
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hAne_empty
  obtain ⟨b, hb⟩ : (Aᶜ).Nonempty := Set.nonempty_compl.mpr hAne_univ
  set Arv : Set ↥(rootVariety q) := Subtype.val '' A with hArv
  have hArv_base : IsClopenOverBase q U Arv := by
    show IsClopen (Subtype.val ⁻¹' Arv : Set ↥(rootProj q ⁻¹' U))
    rw [hArv, Set.preimage_image_eq A Subtype.val_injective]
    exact hAcl
  have hAfreq := rootCover_count_pos_freq_gen q hmonic hdeg hUopen hUconn hUsep hU0 hanaU
    hArv_base (e := a.1) a.2 ⟨a, ha, rfl⟩
  have hBfreq := rootCover_count_pos_freq_gen q hmonic hdeg hUopen hUconn hUsep hU0 hanaU
    hArv_base.compl (e := b.1) b.2 (by
      intro hmem
      obtain ⟨x, hx, hxb⟩ := hmem
      exact hb (Subtype.ext hxb ▸ hx))
  exact clopen_split_contradiction'_gen q hmonic hdeg hq0 hana0 hsep hε hbdd hirr hUopen hUconn
    hUsep hU0 hanaU hArv_base hAfreq hBfreq

/-- The root cover over a separable base `U` is a covering map (`Fin (n+1)` packaging). -/
theorem rootCover_isCoveringMap_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    {U : Set (Fin (n + 1) → ℂ)}
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hUsep : ∀ y ∈ U, (q y).Separable) :
    IsCoveringMap (U.restrictPreimage (rootProj q)) :=
  rootProj_isCoveringMap_restrict q hmonic hdeg hcont U hanaU hUsep

/-- **G3 — the root cover over a general base is path-connected.** `Fin (n+1)` analogue of
`rootCover_pathConnected`. -/
theorem rootCover_pathConnected_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducibleGen q)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε) :
    PathConnectedSpace ↥(rootProj q ⁻¹' U) := by
  have cov : IsCoveringMap (U.restrictPreimage (rootProj q)) :=
    rootCover_isCoveringMap_gen q hmonic hdeg hcont hanaU hUsep
  haveI : LocPathConnectedSpace ↥U := hUopen.locPathConnectedSpace
  haveI : LocPathConnectedSpace ↥(rootProj q ⁻¹' U) := cov.isLocalHomeomorph.locPathConnectedSpace
  haveI : PreconnectedSpace ↥(rootProj q ⁻¹' U) :=
    rootCover_preconnected_gen q hmonic hdeg hana0 hq0 hirr hUopen hUconn hUsep hU0 hanaU hε hbdd
  haveI : Nonempty ↥(rootProj q ⁻¹' U) := by
    obtain ⟨y₀, hy₀⟩ := Filter.nonempty_of_mem hU0
    obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root (q y₀) (by
      rw [Polynomial.degree_eq_natDegree (hmonic y₀).ne_zero, hdeg y₀]
      exact_mod_cast hm.ne')
    exact ⟨⟨⟨(y₀, t₀), ht₀⟩, hy₀⟩⟩
  haveI : ConnectedSpace ↥(rootProj q ⁻¹' U) := ⟨inferInstance⟩
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- **G3 — Lemma 4.2.5 (root exchange) over the general base `Fin (n+1) → ℂ`.** For an irreducible
Weierstrass family of positive degree, any two sheets `e₀, e₁` of the root cover over the same base
point of `U` are joined by a base loop whose lift carries `e₀` to `e₁`. This is the transitive-monodromy
input to the thesis homotopy-deformation contradiction, now in the base dimension the proof requires. -/
theorem rootCover_exchange_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducibleGen q)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    {e₀ e₁ : ↥(rootProj q ⁻¹' U)}
    (hpe : U.restrictPreimage (rootProj q) e₀ = U.restrictPreimage (rootProj q) e₁) :
    ∃ (γ : C(unitInterval, ↥U)) (hγ0 : γ 0 = U.restrictPreimage (rootProj q) e₀),
      γ 1 = U.restrictPreimage (rootProj q) e₀ ∧
        (rootCover_isCoveringMap_gen q hmonic hdeg hcont hanaU hUsep).liftPath γ e₀ hγ0 1 = e₁ := by
  haveI : PathConnectedSpace ↥(rootProj q ⁻¹' U) :=
    rootCover_pathConnected_gen q hm hmonic hdeg hcont hana0 hq0 hirr hUopen hUconn hUsep hU0 hanaU
      hε hbdd
  exact transitive_monodromy_of_pathConnected
    (rootCover_isCoveringMap_gen q hmonic hdeg hcont hanaU hUsep) hpe

end

