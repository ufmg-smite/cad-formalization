import Cad.Multivariate.ProjectionTheorem.Generalized.MonodromyAssemble
import Cad.Multivariate.ProjectionTheorem.Generalized.CParamWiring
import Cad.Multivariate.ProjectionTheorem.Generalized.FamilyGlobalize
import Cad.Multivariate.ProjectionTheorem.Generalized.PunctBallConnected
import Cad.Multivariate.ProjectionTheorem.Generalized.SeparableDiscr
import Cad.Multivariate.ProjectionTheorem.Generalized.RootBound
import Cad.Multivariate.ProjectionTheorem.Generalized.CoordTranslate
import Cad.Multivariate.ProjectionTheorem.Generalized.A5Coincidence
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiFactorization

/-!
# M5 (e = 1) — discharging `irreducible_section_single_root_deg` for codimension-1 sections

The genuine monodromy kernel for an irreducible Weierstrass family `H` over `CParam s 1` is reduced to
the proved `MonodromyAssemble.section_card_le_one` (M4) by:

* coordinate translation `Φ := cparamEquiv s : CParam s 1 ≃L Fin (s+1) → ℂ`, `q := H ∘ Φ.symm`;
* globalization `qt` of `q` (`exists_globalized_family`) so the localized covering chain applies;
* separability on the punctured ball from the disc normal form (`sep_off_hyperplane` +
  `separable_of_discr_ne_zero`), with the disc-order hypotheses transported by `order_comp_cle`;
* preconnectedness (`punctBall_isPreconnected`), the root bound (`roots_bound_eventually`), and
  `UnivIrreducibleGen qt` from `WeierstrassIrreducible H` (`univIrreducibleGen_of_germ`).

`section_card_le_one` then bounds the number of distinct section roots by `1`, and
`single_root_of_card_le_one` packages it into the axiom's conclusion (translated back via `q∘Φ = H`).
-/

noncomputable section

open Polynomial Filter Metric Set MonodromyDeform CoordTranslate CParamWiring
open scoped Topology

/-- **e = 1 case of `irreducible_section_single_root_deg`.** For an irreducible Weierstrass family `H`
over `CParam s 1` of degree `d ≥ 2` with finite, section-constant discriminant order, the section
polynomial `H (y, 0)` has a single distinct root for `y` near `0`. -/
theorem irreducible_section_single_root_e1 {s : ℕ}
    (H : CParam s 1 → Polynomial ℂ) (d : ℕ) (hd : 2 ≤ d)
    (hH_fam : IsWeierstrassFamily H d) (hH_irr : WeierstrassIrreducible H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s 1) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s 1)
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s 1)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (H ((y, 0) : CParam s 1)).IsRoot β ↔ β = α := by
  classical
  set Φ := cparamEquiv s with hΦ
  have hΦsymm0 : Φ.symm 0 = 0 := by rw [hΦ]; exact map_zero _
  have hΦ0 : Φ (0 : CParam s 1) = 0 := by rw [hΦ]; exact map_zero _
  have hΦsym_an : AnalyticAt ℂ (fun z => Φ.symm z) (0 : Fin (s + 1) → ℂ) :=
    (Φ.symm : (Fin (s + 1) → ℂ) →L[ℂ] CParam s 1).analyticAt 0
  have hΦ_an : AnalyticAt ℂ (fun w => Φ w) (0 : CParam s 1) :=
    (Φ : CParam s 1 →L[ℂ] (Fin (s + 1) → ℂ)).analyticAt 0
  -- the family `q := H ∘ Φ.symm` over `Fin (s+1) → ℂ`
  set q : (Fin (s + 1) → ℂ) → Polynomial ℂ := fun z => H (Φ.symm z) with hq
  have hq_monic : ∀ z, (q z).Monic := fun z => hH_fam.monic _
  have hq_deg : ∀ z, (q z).natDegree = d := fun z => hH_fam.degree_eq _
  have hq_coeff0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (s + 1) → ℂ) := fun i =>
    (hH_fam.coeff_analyticAt i).comp_of_eq hΦsym_an hΦsymm0
  -- globalization
  obtain ⟨qt, r, hr0, hqt_monic, hqt_deg, hqt_cont, hqt_eq, hqt_ana⟩ :=
    FamilyGlobalize.exists_globalized_family q hq_monic hq_deg hq_coeff0
  have hq0 : q 0 = X ^ d := by
    show H (Φ.symm 0) = X ^ d
    rw [hΦsymm0]; exact hH_fam.eval_zero
  have hqt0 : qt 0 = X ^ d := by rw [hqt_eq 0 (mem_ball_self hr0)]; exact hq0
  -- the discriminant `D = disc(q ·)` and its order facts (transported through `Φ`)
  set D : (Fin (s + 1) → ℂ) → ℂ := fun z => (q z).discr with hD
  have hHdisc_an : AnalyticAt ℂ (fun w => (H w).discr) (0 : CParam s 1) :=
    familyDiscr_analyticAt H d (by omega) hH_fam.monic hH_fam.degree_eq hH_fam.coeff_analyticAt
  have hDan : AnalyticAt ℂ D 0 := hHdisc_an.comp_of_eq hΦsym_an hΦsymm0
  have hD0 : D 0 = 0 := by
    show (q 0).discr = 0
    rw [hq0]; exact discr_X_pow_eq_zero hd
  have hDw : ∀ w, order ℂ D w = order ℂ (fun u => (H u).discr) (Φ.symm w) := fun w =>
    order_comp_cle Φ.symm (fun u => (H u).discr) w
  have hord0 : order ℂ D 0 = order ℂ (fun w => (H w).discr) (0 : CParam s 1) := by
    rw [hDw 0, hΦsymm0]
  -- section-constancy of the order, transported from `hHdisc_oi`
  have hconst : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ),
      order ℂ D w = order ℂ D 0 := by
    have htail : Tendsto (fun w : Fin (s + 1) → ℂ => Fin.tail w)
        (𝓝[{z | z 0 = 0}] (0 : Fin (s + 1) → ℂ)) (𝓝 (0 : Fin s → ℂ)) := by
      have hc : Continuous (fun w : Fin (s + 1) → ℂ => Fin.tail w) :=
        continuous_pi (fun i => continuous_apply _)
      have h0 : Fin.tail (0 : Fin (s + 1) → ℂ) = 0 := by funext i; rfl
      exact (h0 ▸ hc.tendsto 0).mono_left nhdsWithin_le_nhds
    filter_upwards [htail.eventually hHdisc_oi, eventually_mem_nhdsWithin] with w hw_oi hw_mem
    have hw0 : w 0 = 0 := hw_mem
    have hΦw : Φ.symm w = (Fin.tail w, (0 : Fin 1 → ℂ)) := by
      rw [hΦ, cparamEquiv_symm_apply]; refine Prod.ext rfl ?_; funext i; simp [hw0]
    rw [hDw w, hΦw, hw_oi]; exact hord0.symm
  -- separability off the hyperplane
  have hsep_ev : ∀ᶠ z in 𝓝 (0 : Fin (s + 1) → ℂ), z 0 ≠ 0 → D z ≠ 0 :=
    DiscNormalForm.sep_off_hyperplane D hDan hD0 (by rw [hord0]; exact hHdisc_ne) hconst
  obtain ⟨δ₀, hδ₀, hsep_ball⟩ := Metric.eventually_nhds_iff.mp hsep_ev
  -- the working radius `δ`
  set δ : ℝ := min r δ₀ / 2 with hδdef
  have hδ : 0 < δ := by have := lt_min hr0 hδ₀; positivity
  have hδr : δ < r := by rw [hδdef]; have : min r δ₀ ≤ r := min_le_left _ _; linarith
  have hδδ₀ : δ < δ₀ := by rw [hδdef]; have : min r δ₀ ≤ δ₀ := min_le_right _ _; linarith
  -- M4 hypotheses for `qt`
  have hana : ∀ i, ∀ y ∈ ball (0 : Fin (s + 1) → ℂ) δ,
      AnalyticAt ℂ (fun z => (qt z).coeff i) y :=
    fun i y hy => hqt_ana i y (ball_subset_ball hδr.le hy)
  have hUconn : IsPreconnected (punctBall (n := s) δ) := punctBall_isPreconnected hδ
  have hsep : ∀ y ∈ punctBall (n := s) δ, (qt y).Separable := by
    intro y hy
    rw [mem_punctBall] at hy
    have hyr : y ∈ ball (0 : Fin (s + 1) → ℂ) r := mem_ball_zero_iff.mpr (lt_trans hy.1 hδr)
    rw [hqt_eq y hyr]
    have hdy : (q y).discr ≠ 0 := hsep_ball (by rw [dist_zero_right]; exact lt_trans hy.1 hδδ₀) hy.2
    exact separable_of_discr_ne_zero (hq_monic y) (by rw [hq_deg y]; omega) hdy
  obtain ⟨ε, hε, hbdd⟩ := roots_bound_eventually qt d (0 : Fin (s + 1) → ℂ) hqt_monic hqt_deg
    (fun i => (hqt_cont i).continuousAt)
  -- irreducibility of `qt` from `WeierstrassIrreducible H`
  have hirr : UnivIrreducibleGen qt := by
    refine univIrreducibleGen_of_germ qt hqt_deg (fun i => hqt_ana i 0 (mem_ball_self hr0)) ?_
    rintro ⟨dA, dB, HA, HB, hdA, hdB, hHAm, hHAd, hHAc, hHA0, hHBm, hHBd, hHBc, hHB0, heq⟩
    apply hH_irr.2
    have hfam : ∀ (HX : (Fin (s + 1) → ℂ) → Polynomial ℂ) (dX : ℕ),
        (∀ y, (HX y).Monic) → (∀ y, (HX y).natDegree = dX) →
        (∀ i, AnalyticAt ℂ (fun y => (HX y).coeff i) 0) → HX 0 = X ^ dX →
        IsWeierstrassFamily (fun w => HX (Φ w)) dX := by
      intro HX dX hm hdg hc h0
      refine ⟨fun w => hm _, fun w => hdg _, fun i => (hc i).comp_of_eq hΦ_an hΦ0, fun i hi => ?_⟩
      show (HX (Φ (0 : CParam s 1))).coeff i = 0
      rw [hΦ0, h0, Polynomial.coeff_X_pow, if_neg (by omega)]
    have hprod : ∀ᶠ w in 𝓝 (0 : CParam s 1), H w = HA (Φ w) * HB (Φ w) := by
      have hqeq : ∀ᶠ x in 𝓝 (0 : Fin (s + 1) → ℂ), q x = HA x * HB x := by
        filter_upwards [heq, isOpen_ball.mem_nhds (mem_ball_self hr0)] with x hx hxr
        rw [← hqt_eq x hxr]; exact hx
      have hΦtend : Tendsto (fun w : CParam s 1 => Φ w) (𝓝 0) (𝓝 (0 : Fin (s + 1) → ℂ)) := by
        have := Φ.continuous.tendsto (0 : CParam s 1); rwa [hΦ0] at this
      filter_upwards [hΦtend.eventually hqeq] with w hw
      have hqΦ : q (Φ w) = H w := by
        show H (Φ.symm (Φ w)) = H w; rw [Φ.symm_apply_apply]
      rw [← hqΦ]; exact hw
    exact ⟨dA, dB, fun w => HA (Φ w), fun w => HB (Φ w), hdA, hdB,
      hfam HA dA hHAm hHAd hHAc hHA0, hfam HB dB hHBm hHBd hHBc hHB0, hprod⟩
  -- assemble: for `y` near `0`, the section base point `a = Φ (y, 0)` lands the M4 bound
  have ha_tendsto : Tendsto (fun y : Fin s → ℂ => Φ (y, 0)) (𝓝 0) (𝓝 (0 : Fin (s + 1) → ℂ)) := by
    have hc : Continuous (fun y : Fin s → ℂ => Φ (y, 0)) :=
      Φ.continuous.comp (continuous_id.prodMk continuous_const)
    have h0 : Φ ((0 : Fin s → ℂ), (0 : Fin 1 → ℂ)) = 0 := hΦ0
    exact h0 ▸ hc.tendsto 0
  filter_upwards [ha_tendsto.eventually (ball_mem_nhds 0 hδ)] with y hy_mem
  set a : Fin (s + 1) → ℂ := Φ (y, 0) with ha
  have ha0 : a 0 = 0 := by rw [ha, hΦ]; exact cparamEquiv_section s y
  have ha_norm : ‖a‖ < δ := mem_ball_zero_iff.mp hy_mem
  have hcard := MonodromyAssemble.section_card_le_one qt (by omega : 0 < d) hqt_monic hqt_deg
    hqt_cont hqt0 hirr hδ hana hUconn hsep hε hbdd a ha0 ha_norm
  have hqta : qt a = H (y, 0) := by
    rw [hqt_eq a (mem_ball_zero_iff.mpr (lt_trans ha_norm hδr))]
    show H (Φ.symm a) = H (y, 0)
    rw [ha, Φ.symm_apply_apply]
  rw [← hqta]
  exact single_root_of_card_le_one (hqt_monic a) (by rw [hqt_deg a]; omega) hcard

/-- **e = 0 case of `irreducible_section_single_root_deg` (vacuous).** When `e = 0` the transverse factor
`Fin 0 → ℂ` is trivial, so the "section" is a full neighbourhood; the discriminant-order hypotheses then
contradict each other: a finite, *locally constant* order `≥ 1` would force `disc(H ·) ≡ 0` near `0`
(order `⊤`). The conclusion follows vacuously. -/
theorem irreducible_section_single_root_e0 {s : ℕ}
    (H : CParam s 0 → Polynomial ℂ) (d : ℕ) (hd : 2 ≤ d)
    (hH_fam : IsWeierstrassFamily H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s 0) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s 0)
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s 0)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (H ((y, 0) : CParam s 0)).IsRoot β ↔ β = α := by
  exfalso
  set D : CParam s 0 → ℂ := fun w => (H w).discr with hD
  have hD0 : D 0 = 0 := by show (H 0).discr = 0; rw [hH_fam.eval_zero]; exact discr_X_pow_eq_zero hd
  have hord_ne0 : order ℂ D 0 ≠ 0 := order_ne_zero_of_eq_zero D 0 hD0
  -- the transverse `Fin 0 → ℂ` is trivial, so order is locally constant on a full neighbourhood of `0`
  have hconst : ∀ᶠ w in 𝓝 (0 : CParam s 0), order ℂ D w = order ℂ D 0 := by
    have htend : Tendsto (fun w : CParam s 0 => w.1) (𝓝 0) (𝓝 (0 : Fin s → ℂ)) :=
      continuous_fst.tendsto 0
    filter_upwards [htend.eventually hHdisc_oi] with w hw
    have hweq : ((w.1, (0 : Fin 0 → ℂ)) : CParam s 0) = w := by
      refine Prod.ext rfl ?_; exact Subsingleton.elim _ _
    rwa [hweq] at hw
  -- order `≥ 1` everywhere near `0` ⟹ `D ≡ 0` near `0` ⟹ order `⊤`, contradiction
  have hDvanish : ∀ᶠ w in 𝓝 (0 : CParam s 0), D w = 0 := by
    filter_upwards [hconst] with w hw
    by_contra hDw
    exact hord_ne0 (hw.symm.trans (order_eq_zero_of_ne D w hDw))
  have htop : order ℂ D 0 = ⊤ := by
    rw [order_congr_of_eventuallyEq' (hDvanish : D =ᶠ[𝓝 (0 : CParam s 0)] (fun _ => 0))]
    exact order_eq_top_iff.mpr (fun n => by simp [iteratedFDeriv_zero_fun])
  exact hHdisc_ne htop

end
