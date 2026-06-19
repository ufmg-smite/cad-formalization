import Cad.Multivariate.ProjectionTheorem.Submanifold

/-!
# Refinement of analytic submanifolds (Brown's Lemma 8.2)

Given a connected analytic submanifold `S`, a point `p ∈ S`, and an open
neighborhood `N₀` of `p`, there is an open `N` with `p ∈ N ⊆ N₀` such that
`S ∩ N` is again a *connected* analytic submanifold.

This is Lemma 5.1 of `thesis/brown_generalized.tex`: take a straightening
chart `Φ` at `p`, pull back along `Ψ : y ↦ Φ⁻¹(y, 0)`, and pass to the
connected component of `0` in the (open) set of good chart parameters.  The
connectivity part of the argument already appears inline in
`Mccalum/Generalized/Delineable.lean`; here it is packaged as a standalone
lemma, together with the (easy) fact that `IsAnalyticSubmanifold` is stable
under intersection with open sets.
-/

noncomputable section

open Set

variable {n : ℕ}

/-- An analytic submanifold intersected with an open set is an analytic
submanifold, provided the intersection is nonempty.  The definition is
pointwise-local with a fixed dimension, so the same local data restricts. -/
theorem IsAnalyticSubmanifold.inter_open
    {S : Set (Fin n → ℝ)} (hS : IsAnalyticSubmanifold S)
    {N : Set (Fin n → ℝ)} (hN : IsOpen N) (hne : (S ∩ N).Nonempty) :
    IsAnalyticSubmanifold (S ∩ N) := by
  obtain ⟨-, s, hs, hdata⟩ := hS
  refine ⟨hne, s, hs, ?_⟩
  intro p hp
  obtain ⟨W, hW_open, hpW, F, hF_an, hF_surj, hF_zero⟩ := hdata p hp.1
  refine ⟨W ∩ N, hW_open.inter hN, ⟨hpW, hp.2⟩, F,
    hF_an.mono inter_subset_left, hF_surj, ?_⟩
  intro x hx
  constructor
  · intro hxSN
    exact (hF_zero x hx.1).mp hxSN.1
  · intro hFx
    exact ⟨(hF_zero x hx.1).mpr hFx, hx.2⟩

/-- **Brown's refinement lemma** (Lemma 8.2 of Brown 2001; Lemma 5.1 of the
notes).  Any open neighborhood of a point of an analytic submanifold can be
shrunk so that the intersection with `S` is a connected analytic submanifold. -/
theorem IsAnalyticSubmanifold.refine_connected
    {S : Set (Fin n → ℝ)} (hS : IsAnalyticSubmanifold S)
    {p : Fin n → ℝ} (hp : p ∈ S)
    {N₀ : Set (Fin n → ℝ)} (hN₀ : IsOpen N₀) (hpN₀ : p ∈ N₀) :
    ∃ N : Set (Fin n → ℝ), IsOpen N ∧ p ∈ N ∧ N ⊆ N₀ ∧
      IsAnalyticSubmanifold (S ∩ N) ∧ IsConnected (S ∩ N) := by
  obtain ⟨s, _hs, Φ, hΦ_source, hΦ_val, _hΦ_an_all, _hΦ_symm_an, hΦ_straight⟩ :=
    hS.straightening_chart p hp
  -- the chart-parameter embedding `Ψ y = Φ⁻¹(y, 0)`
  set Ψ : (Fin s → ℝ) → (Fin n → ℝ) := fun y => Φ.symm (y, 0) with hΨ_def
  have hΨ_zero : Ψ 0 = p := by
    show Φ.symm ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ)) = p
    rw [← hΦ_val]
    exact Φ.left_inv hΦ_source
  have hΦ_target_zero : ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ)) ∈ Φ.target := by
    rw [← hΦ_val]
    exact Φ.map_source hΦ_source
  -- good chart parameters: `(y,0)` in the target, `Ψ y` inside `N₀`
  set T₀ : Set (Fin s → ℝ) := {y | (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target} with hT₀_def
  have hT₀_open : IsOpen T₀ :=
    Φ.open_target.preimage (continuous_id.prodMk continuous_const)
  have hΨ_cont : ContinuousOn Ψ T₀ :=
    Φ.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hy => hy)
  set Vt : Set (Fin s → ℝ) := T₀ ∩ Ψ ⁻¹' N₀ with hVt_def
  have hVt_open : IsOpen Vt := hΨ_cont.isOpen_inter_preimage hT₀_open hN₀
  have h0Vt : (0 : Fin s → ℝ) ∈ Vt :=
    ⟨hΦ_target_zero, by rw [mem_preimage, hΨ_zero]; exact hpN₀⟩
  -- pass to the connected component of `0`
  set V' : Set (Fin s → ℝ) := connectedComponentIn Vt 0 with hV'_def
  have hV'_sub : V' ⊆ Vt := connectedComponentIn_subset Vt 0
  have hV'_open : IsOpen V' := hVt_open.connectedComponentIn
  have h0V' : (0 : Fin s → ℝ) ∈ V' := mem_connectedComponentIn h0Vt
  have hV'_preconn : IsPreconnected V' := isPreconnected_connectedComponentIn
  -- the open refinement `N`
  set N : Set (Fin n → ℝ) := (Φ.source ∩ (Prod.fst ∘ Φ) ⁻¹' V') ∩ N₀ with hN_def
  have hN_open : IsOpen N :=
    (Φ.continuousOn.fst.isOpen_inter_preimage Φ.open_source hV'_open).inter hN₀
  have hΦp_fst : (Φ p).1 = 0 := by rw [hΦ_val]
  have hpN : p ∈ N := by
    refine ⟨⟨hΦ_source, ?_⟩, hpN₀⟩
    show (Φ p).1 ∈ V'
    rw [hΦp_fst]
    exact h0V'
  have hN_sub : N ⊆ N₀ := fun x hx => hx.2
  -- helper facts about `Ψ`
  have hΨ_source : ∀ y ∈ T₀, Ψ y ∈ Φ.source := fun y hy => Φ.map_target hy
  have hΨ_S : ∀ y ∈ T₀, Ψ y ∈ S := by
    intro y hy
    refine (hΦ_straight (Ψ y) (Φ.map_target hy)).mpr ?_
    show (Φ (Φ.symm (y, (0 : Fin (n - s) → ℝ)))).2 = 0
    rw [Φ.right_inv hy]
  have hΨ_roundtrip : ∀ x ∈ S, x ∈ Φ.source → Ψ ((Φ x).1) = x := by
    intro x hxS hx_source
    have h2 : (Φ x).2 = 0 := (hΦ_straight x hx_source).mp hxS
    show Φ.symm ((Φ x).1, (0 : Fin (n - s) → ℝ)) = x
    conv_rhs => rw [← Φ.left_inv hx_source]
    congr 1
    exact Prod.ext rfl h2.symm
  -- `S ∩ N` is exactly the image of the component under `Ψ`
  have himg : S ∩ N = Ψ '' V' := by
    apply Subset.antisymm
    · rintro a ⟨haS, ⟨ha_source, haV'⟩, -⟩
      exact ⟨(Φ a).1, haV', hΨ_roundtrip a haS ha_source⟩
    · rintro x ⟨y, hyV', rfl⟩
      have hyT₀ : y ∈ T₀ := (hV'_sub hyV').1
      have hyN₀ : Ψ y ∈ N₀ := (hV'_sub hyV').2
      refine ⟨hΨ_S y hyT₀, ⟨hΨ_source y hyT₀, ?_⟩, hyN₀⟩
      show (Φ (Ψ y)).1 ∈ V'
      rw [show Φ (Ψ y) = (y, (0 : Fin (n - s) → ℝ)) from Φ.right_inv hyT₀]
      exact hyV'
  refine ⟨N, hN_open, hpN, hN_sub, ?_, ?_⟩
  · exact hS.inter_open hN_open ⟨p, hp, hpN⟩
  · rw [himg]
    exact ⟨⟨Ψ 0, mem_image_of_mem Ψ h0V'⟩,
      hV'_preconn.image Ψ (hΨ_cont.mono (hV'_sub.trans inter_subset_left))⟩

end
