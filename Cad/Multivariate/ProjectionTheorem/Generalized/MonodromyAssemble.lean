import Cad.Multivariate.ProjectionTheorem.Generalized.MonodromyDeform
import Cad.Multivariate.ProjectionTheorem.Generalized.RoucheSeparation

/-!
# M4 — assembling the single-factor nonsplitting (thesis Theorem 4.2.2)

This file wires together the four ingredients of the homotopy-deformation contradiction into the
per-irreducible-factor conclusion: the section polynomial of an irreducible normal-form Weierstrass
family has **at most one distinct root**.

* `rootCover_exchange_gen` (M1/G3) — the root-exchanging loop `Γ` over the punctured ball;
* `cluster_separation` (M2) — disjoint discs `Dⱼ` about the distinct section roots, with confinement and
  non-emptiness for transverse values near `0`;
* `deform_to_transverse_loop` (M3) — the deformation `Γ ≃ Γ''` onto a small transverse circle;
* `monodromy_exchange_contradiction` (the proved logical core).

The geometry: take the base neighbourhood `U = punctBall δ`. Fix a section point `a` (`a 0 = 0`). If
`q a` had two distinct roots `α₁ ≠ α₂`, M2 gives disjoint discs about them; at a small off-section base
point `w' = update a 0 r` (`0 < r` small) M2 supplies roots `α ∈ D₁`, `β ∈ D₂`, hence two distinct
sheets `e₀, e₁`; M1 joins them by a loop `Γ`; M3 deforms `Γ` to `Γ''` on the circle `|z₀| = r`; and the
lift of `Γ''` has its root coordinate a root of `q(γ''(t))`, confined by M2 to `⋃ⱼ Dⱼ`. With
`A = D₁`, `B = ⋃_{j≥2} Dⱼ` this contradicts `monodromy_exchange_contradiction`.
-/

noncomputable section

open Polynomial Filter Set Metric MonodromyDeform RoucheSeparation
open scoped Topology

namespace MonodromyAssemble

variable {n : ℕ}

/-- The slice family through the section point `a` along the transverse coordinate. -/
private def slice (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (a : Fin (n + 1) → ℂ) :
    ℂ → Polynomial ℂ := fun τ => q (Function.update a 0 τ)

/-- **M4 (codim-1 single root).** For an irreducible normal-form Weierstrass family `q` over the
punctured ball `punctBall δ`, the section polynomial `q a` at any small section point `a` (`a 0 = 0`,
`‖a‖ < δ`) has at most one distinct root. -/
theorem section_card_le_one {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducibleGen q)
    {δ : ℝ} (hδ : 0 < δ)
    (hana : ∀ i, ∀ y ∈ Metric.ball (0 : Fin (n + 1) → ℂ) δ,
      AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hUconn : IsPreconnected (punctBall (n := n) δ))
    (hsep : ∀ y ∈ punctBall (n := n) δ, (q y).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    (a : Fin (n + 1) → ℂ) (ha0 : a 0 = 0) (ha : ‖a‖ < δ) :
    (q a).roots.toFinset.card ≤ 1 := by
  classical
  -- analyticity at the section base point `a`, on the punctured ball `U`, and at `0`
  have ha_ball : a ∈ Metric.ball (0 : Fin (n + 1) → ℂ) δ := mem_ball_zero_iff.mpr ha
  have hanaU : ∀ i, ∀ y ∈ punctBall (n := n) δ, AnalyticAt ℂ (fun z => (q z).coeff i) y :=
    fun i y hy => hana i y (mem_ball_zero_iff.mpr (mem_punctBall.mp hy).1)
  have hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ) :=
    fun i => hana i 0 (Metric.mem_ball_self hδ)
  -- `U = punctBall δ` is open and a deleted-hyperplane neighbourhood of `0`
  have hUopen : IsOpen (punctBall (n := n) δ) :=
    isOpen_ball.inter (isOpen_ne.preimage (continuous_apply 0))
  have hU0 : punctBall (n := n) δ ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ) := by
    rw [punctBall, Set.inter_comm]
    exact inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hδ))
  -- the transverse slice and its hypotheses
  set P : ℂ → Polynomial ℂ := slice q a with hP
  have hupd_an : AnalyticAt ℂ (fun τ : ℂ => Function.update a 0 τ) 0 := by
    have he : (fun τ : ℂ => Function.update a 0 τ)
        = fun τ : ℂ => a + τ • Function.update (0 : Fin (n + 1) → ℂ) 0 1 := by
      funext τ; funext i
      rcases eq_or_ne i 0 with h | h
      · subst h; simp [ha0]
      · simp [Function.update_of_ne h]
    rw [he]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hupd0 : (fun τ : ℂ => Function.update a 0 τ) 0 = a := by
    funext i; rcases eq_or_ne i 0 with h | h
    · subst h; simp [ha0]
    · simp [Function.update_of_ne h]
  have hPmonic : ∀ τ, (P τ).Monic := fun τ => hmonic _
  have hPdeg : ∀ τ, (P τ).natDegree = m := fun τ => hdeg _
  have hPcoeff : ∀ i, AnalyticAt ℂ (fun τ => (P τ).coeff i) 0 := fun i =>
    (hana i a ha_ball).comp_of_eq hupd_an hupd0
  -- M2: discs + confinement/non-emptiness near `0`
  obtain ⟨ρ, hρ, hdisj, hev⟩ := cluster_separation P m hPmonic hPdeg hPcoeff
  have hP0 : P 0 = q a := congrArg q hupd0
  -- prove `card ≤ 1` by contradiction
  by_contra hcard
  rw [not_le] at hcard
  obtain ⟨α₁, hα₁, α₂, hα₂, hα₁₂⟩ := Finset.one_lt_card.mp hcard
  have hα₁' : α₁ ∈ (P 0).roots.toFinset := by rw [hP0]; exact hα₁
  have hα₂' : α₂ ∈ (P 0).roots.toFinset := by rw [hP0]; exact hα₂
  -- a small radius `r` with the confinement/non-emptiness neighbourhood
  obtain ⟨η, hη, hη_sub⟩ := Metric.mem_nhds_iff.mp hev
  set r : ℝ := min η δ / 2 with hr
  have hr_pos : 0 < r := by have := lt_min hη hδ; positivity
  have hr_η : r < η := by have : min η δ ≤ η := min_le_left _ _; rw [hr]; linarith
  have hr_δ : r < δ := by have : min η δ ≤ δ := min_le_right _ _; rw [hr]; linarith
  -- the off-section base point `w'`
  set w' : Fin (n + 1) → ℂ := Function.update a 0 (r : ℂ) with hw'
  have hw'0 : w' 0 = (r : ℂ) := Function.update_self 0 (r : ℂ) a
  have hw'i : ∀ i, i ≠ 0 → w' i = a i := fun i hi => Function.update_of_ne hi (r : ℂ) a
  have hw'_mem : w' ∈ punctBall (n := n) δ := by
    rw [mem_punctBall]
    refine ⟨?_, ?_⟩
    · rw [pi_norm_lt_iff hδ]
      intro i
      rcases eq_or_ne i 0 with h | h
      · subst h; rw [hw'0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]; exact hr_δ
      · rw [hw'i i h]; exact lt_of_le_of_lt (norm_le_pi_norm a i) ha
    · rw [hw'0]; exact_mod_cast hr_pos.ne'
  -- the confinement/non-emptiness facts hold at the transverse value `r` and on the circle `|·| = r`
  have hr_ball : (r : ℂ) ∈ ball (0 : ℂ) η := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]; exact hr_η
  have hQ_r := hη_sub hr_ball
  -- `P r = q w'`
  have hPr_eq : P (r : ℂ) = q w' := rfl
  -- two distinct roots `α ∈ D₁`, `β ∈ D₂` at `w'`
  obtain ⟨α, hα_root, hα_mem⟩ := hQ_r.2 α₁ hα₁'
  obtain ⟨β, hβ_root, hβ_mem⟩ := hQ_r.2 α₂ hα₂'
  have hα_eval : (q w').eval α = 0 := by
    have := hα_root; rwa [hPr_eq, Polynomial.IsRoot.def] at this
  have hβ_eval : (q w').eval β = 0 := by
    have := hβ_root; rwa [hPr_eq, Polynomial.IsRoot.def] at this
  -- the two sheets over `w'`
  let ev₀ : ↥(rootVariety q) := ⟨(w', α), hα_eval⟩
  let ev₁ : ↥(rootVariety q) := ⟨(w', β), hβ_eval⟩
  let e₀ : ↥(rootProj q ⁻¹' punctBall (n := n) δ) := ⟨ev₀, hw'_mem⟩
  let e₁ : ↥(rootProj q ⁻¹' punctBall (n := n) δ) := ⟨ev₁, hw'_mem⟩
  -- the covering map and the root-exchanging loop (M1)
  have hcov : IsCoveringMap ((punctBall (n := n) δ).restrictPreimage (rootProj q)) :=
    rootCover_isCoveringMap_gen q hmonic hdeg hcont hanaU hsep
  have hpe : (punctBall (n := n) δ).restrictPreimage (rootProj q) e₀
      = (punctBall (n := n) δ).restrictPreimage (rootProj q) e₁ := rfl
  obtain ⟨γ, hγ0, hγ1, hexch⟩ :=
    rootCover_exchange_gen q hm hmonic hdeg hcont hana0 hq0 hirr hUopen hUconn hsep hU0 hanaU hε hbdd
      hpe
  have hloop : γ 0 = γ 1 := hγ0.trans hγ1.symm
  -- the deformed loop on the transverse circle (M3)
  obtain ⟨Γ'', hsec, hmod, hhom⟩ := deform_to_transverse_loop hδ γ hloop
  -- the base point of `γ` is `w'`
  have hγ0_val : (γ 0 : Fin (n + 1) → ℂ) = w' := congrArg Subtype.val hγ0
  have he'' : Γ'' 0 = (punctBall (n := n) δ).restrictPreimage (rootProj q) e₀ :=
    (hhom.some.fst_eq_snd (Set.mem_insert _ _)).symm.trans hγ0
  -- the root-coordinate map and the two opens `A = D₁`, `B = ⋃_{j≥2} Dⱼ`
  set rc : ↥(rootProj q ⁻¹' punctBall (n := n) δ) → ℂ :=
    fun e => ((e : ↥(rootVariety q)) : (Fin (n + 1) → ℂ) × ℂ).2 with hrc
  have rc_cont : Continuous rc :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  set Bset : Set ℂ := ⋃ β' ∈ (P 0).roots.toFinset.erase α₁, ball β' ρ with hBset
  have hBset_open : IsOpen Bset := isOpen_biUnion fun _ _ => isOpen_ball
  set A : Set ↥(rootProj q ⁻¹' punctBall (n := n) δ) := rc ⁻¹' ball α₁ ρ with hA
  set B : Set ↥(rootProj q ⁻¹' punctBall (n := n) δ) := rc ⁻¹' Bset with hB
  have hA_open : IsOpen A := isOpen_ball.preimage rc_cont
  have hB_open : IsOpen B := hBset_open.preimage rc_cont
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro e heA heB
    rw [hA, Set.mem_preimage] at heA
    rw [hB, Set.mem_preimage, hBset, Set.mem_iUnion₂] at heB
    obtain ⟨β', hβ'_erase, hβ'_mem⟩ := heB
    have hβ'_ne : β' ≠ α₁ := (Finset.mem_erase.mp hβ'_erase).1
    have hβ'_S : β' ∈ (P 0).roots.toFinset := (Finset.mem_erase.mp hβ'_erase).2
    exact Set.disjoint_left.mp (hdisj α₁ hα₁' β' hβ'_S (Ne.symm hβ'_ne)) heA hβ'_mem
  have heA : e₀ ∈ A := by rw [hA, Set.mem_preimage]; exact hα_mem
  have heβB : e₁ ∈ B := by
    rw [hB, Set.mem_preimage, hBset]
    exact Set.mem_iUnion₂.mpr ⟨α₂, Finset.mem_erase.mpr ⟨hα₁₂.symm, hα₂'⟩, hβ_mem⟩
  -- the slice identity: `Γ'' t = update a 0 (Γ'' t 0)`, so `q (Γ'' t) = P (Γ'' t 0)`
  have hz_eq : ∀ t, (Γ'' t : Fin (n + 1) → ℂ) = Function.update a 0 ((Γ'' t : Fin (n + 1) → ℂ) 0) :=
    fun t => by
      funext i
      rcases eq_or_ne i 0 with h | h
      · subst h; rw [Function.update_self]
      · rw [Function.update_of_ne h, hsec t i h, hγ0_val]; exact hw'i i h
  -- confinement of the lift
  have hconf : ∀ t, hcov.liftPath Γ'' e₀ he'' t ∈ A ∪ B := by
    intro t
    set L := hcov.liftPath Γ'' e₀ he'' with hL
    -- the lift's base is `Γ'' t`
    have hbase : ((L t : ↥(rootVariety q)) : (Fin (n + 1) → ℂ) × ℂ).1 = (Γ'' t : Fin (n + 1) → ℂ) :=
      congrArg Subtype.val (congrFun (hcov.liftPath_lifts Γ'' e₀ he'') t)
    -- the root coordinate is a root of `q (Γ'' t)`
    have hroot_eq : (q (Γ'' t : Fin (n + 1) → ℂ)).eval (rc (L t)) = 0 := by
      have hmem : (q (((L t : ↥(rootVariety q)) : (Fin (n + 1) → ℂ) × ℂ).1)).eval
          (((L t : ↥(rootVariety q)) : (Fin (n + 1) → ℂ) × ℂ).2) = 0 :=
        (L t : ↥(rootVariety q)).2
      rw [hbase] at hmem
      exact hmem
    -- so the root coordinate is a root of the slice `P (Γ'' t 0)`
    have hslice_root : (P ((Γ'' t : Fin (n + 1) → ℂ) 0)).IsRoot (rc (L t)) := by
      rw [Polynomial.IsRoot.def, hP]
      show (q (Function.update a 0 ((Γ'' t : Fin (n + 1) → ℂ) 0))).eval (rc (L t)) = 0
      rw [← hz_eq t]; exact hroot_eq
    -- `Γ'' t 0` lies in the confinement neighbourhood
    have hball : (Γ'' t : Fin (n + 1) → ℂ) 0 ∈ ball (0 : ℂ) η := by
      rw [mem_ball_zero_iff, hmod t, hγ0_val, hw'0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr_pos]
      exact hr_η
    obtain ⟨α', hα'_S, hα'_mem⟩ := (hη_sub hball).1 (rc (L t)) hslice_root
    rcases eq_or_ne α' α₁ with h | h
    · left; rw [hA, Set.mem_preimage]; rw [← h]; exact hα'_mem
    · right; rw [hB, Set.mem_preimage, hBset]
      exact Set.mem_iUnion₂.mpr ⟨α', Finset.mem_erase.mpr ⟨h, hα'_S⟩, hα'_mem⟩
  exact monodromy_exchange_contradiction hcov hγ0 he'' hexch hhom hA_open hB_open hAB hconf heA heβB

end MonodromyAssemble
