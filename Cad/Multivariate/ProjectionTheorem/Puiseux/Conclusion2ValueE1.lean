import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2Value
import Cad.Multivariate.ProjectionTheorem.Generalized.CParamWiring
import Cad.Multivariate.ProjectionTheorem.Generalized.FamilyGlobalize
import Cad.Multivariate.ProjectionTheorem.Generalized.SeparableDiscr
import Cad.Multivariate.ProjectionTheorem.Generalized.CoordTranslate
import Cad.Multivariate.ProjectionTheorem.Generalized.A5Coincidence
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiFactorization
import Cad.Multivariate.ProjectionTheorem.Generalized.DiscNormalForm

/-!
# Conclusion 2, codim-1 — the order VALUE for the axiom family (e = 1)

`order_eval_value_e1_weierstrass` instantiates the `Fin (s+1)`-level value formula
`Puiseux.order_eval_value_eventually` to the actual axiom data: an irreducible Weierstrass family `H`
over `CParam s 1` with the single root section `ψ` (Conclusion 1) and finite, section-constant
discriminant order. It reuses the `branch_orders_constant_e1_weierstrass` setup (coordinate translation,
globalization, separability) and additionally extracts the discriminant normal form and the globalized
section `ρ = ψ ∘ radialClamp`, then transports the order back to `CParam` coordinates.
-/

noncomputable section

open Polynomial Filter Metric Set CoordTranslate CParamWiring
open scoped Topology

namespace Puiseux

theorem order_eval_value_e1_weierstrass {s : ℕ}
    (H : CParam s 1 → Polynomial ℂ) (d : ℕ) (hd : 2 ≤ d)
    (hH_fam : IsWeierstrassFamily H d) (hH_irr : WeierstrassIrreducible H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s 1) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s 1)
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s 1))
    (ψ : (Fin s → ℂ) → ℂ) (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (H ((y, 0) : CParam s 1)).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) (((y, 0) : CParam s 1), ψ y)
        = order ℂ (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) (((0, 0) : CParam s 1), ψ 0) := by
  classical
  have hd0 : 0 < d := by omega
  set Φ := cparamEquiv s with hΦ
  have hΦsymm0 : Φ.symm 0 = 0 := by rw [hΦ]; exact map_zero _
  have hΦsym_an : AnalyticAt ℂ (fun z => Φ.symm z) (0 : Fin (s + 1) → ℂ) :=
    (Φ.symm : (Fin (s + 1) → ℂ) →L[ℂ] CParam s 1).analyticAt 0
  have hΦ0 : Φ (0 : CParam s 1) = 0 := by rw [hΦ]; exact map_zero _
  have hΦ_an : AnalyticAt ℂ (fun w => Φ w) (0 : CParam s 1) :=
    (Φ : CParam s 1 →L[ℂ] (Fin (s + 1) → ℂ)).analyticAt 0
  set q : (Fin (s + 1) → ℂ) → Polynomial ℂ := fun z => H (Φ.symm z) with hq
  have hq_monic : ∀ z, (q z).Monic := fun z => hH_fam.monic _
  have hq_deg : ∀ z, (q z).natDegree = d := fun z => hH_fam.degree_eq _
  have hq_coeff0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (s + 1) → ℂ) := fun i =>
    (hH_fam.coeff_analyticAt i).comp_of_eq hΦsym_an hΦsymm0
  obtain ⟨qt, r, hr0, hqt_monic, hqt_deg, hqt_cont, hqt_eq, hqt_ana⟩ :=
    FamilyGlobalize.exists_globalized_family q hq_monic hq_deg hq_coeff0
  have hq0 : q 0 = X ^ d := by show H (Φ.symm 0) = X ^ d; rw [hΦsymm0]; exact hH_fam.eval_zero
  have hqt0 : qt 0 = X ^ d := by rw [hqt_eq 0 (mem_ball_self hr0)]; exact hq0
  set D : (Fin (s + 1) → ℂ) → ℂ := fun z => (q z).discr with hD
  have hHdisc_an : AnalyticAt ℂ (fun w => (H w).discr) (0 : CParam s 1) :=
    familyDiscr_analyticAt H d hd0 hH_fam.monic hH_fam.degree_eq hH_fam.coeff_analyticAt
  have hDan : AnalyticAt ℂ D 0 := hHdisc_an.comp_of_eq hΦsym_an hΦsymm0
  have hD0 : D 0 = 0 := by show (q 0).discr = 0; rw [hq0]; exact discr_X_pow_eq_zero hd
  have hDw : ∀ w, order ℂ D w = order ℂ (fun u => (H u).discr) (Φ.symm w) := fun w =>
    order_comp_cle Φ.symm (fun u => (H u).discr) w
  have hord0 : order ℂ D 0 = order ℂ (fun w => (H w).discr) (0 : CParam s 1) := by
    rw [hDw 0, hΦsymm0]
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
  have hsep_ev : ∀ᶠ z in 𝓝 (0 : Fin (s + 1) → ℂ), z 0 ≠ 0 → D z ≠ 0 :=
    DiscNormalForm.sep_off_hyperplane D hDan hD0 (by rw [hord0]; exact hHdisc_ne) hconst
  obtain ⟨δ₀, hδ₀, hsep_ball⟩ := Metric.eventually_nhds_iff.mp hsep_ev
  set R₀ : ℝ := min r δ₀ with hR₀
  have hR₀0 : 0 < R₀ := lt_min hr0 hδ₀
  have hR₀r : R₀ ≤ r := min_le_left _ _
  have hR₀δ₀ : R₀ ≤ δ₀ := min_le_right _ _
  set c : ℝ := Real.log (R₀ / 2) with hc
  have hexpc : Real.exp c = R₀ / 2 := by rw [hc, Real.exp_log (by positivity)]
  set δz : ℝ := R₀ / 2 with hδzdef
  have hδz : 0 < δz := by positivity
  have hbaseU_ball : ∀ y ∈ baseU s δz c, y ∈ ball (0 : Fin (s + 1) → ℂ) R₀ := by
    intro y hy
    rw [mem_ball_zero_iff]
    calc ‖y‖ ≤ max (‖y 0‖) (‖Fin.tail y‖) := norm_le_max_zero_tail y
      _ < R₀ := by
          refine max_lt ?_ ?_
          · have h := hy.2.1; rw [hexpc] at h; linarith [half_lt_self hR₀0]
          · have h := hy.2.2; rw [hδzdef] at h; linarith [half_lt_self hR₀0]
  have hanaU : ∀ i, ∀ y ∈ baseU s δz c, AnalyticAt ℂ (fun z => (qt z).coeff i) y :=
    fun i y hy => hqt_ana i y (ball_subset_ball hR₀r (hbaseU_ball y hy))
  have hsep_baseU : ∀ y ∈ baseU s δz c, (qt y).Separable := by
    intro y hy
    have hyR₀ : y ∈ ball (0 : Fin (s + 1) → ℂ) R₀ := hbaseU_ball y hy
    rw [hqt_eq y (ball_subset_ball hR₀r hyR₀)]
    have hdy : D y ≠ 0 := hsep_ball (by
      rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.mp hyR₀) hR₀δ₀)
      (norm_pos_iff.mp hy.1)
    exact separable_of_discr_ne_zero (hq_monic y) (by rw [hq_deg y]; omega) hdy
  have hirr : UnivIrreducibleGen qt := by
    refine univIrreducibleGen_of_germ qt hqt_deg
      (fun i => hqt_ana i 0 (mem_ball_self hr0)) ?_
    rintro ⟨dA, dB, HA, HB, hdA, hdB, hHAm, hHAd, hHAc, hHA0, hHBm, hHBd, hHBc, hHB0, heq⟩
    apply hH_irr.2
    have hfam : ∀ (HX : (Fin (s + 1) → ℂ) → Polynomial ℂ) (dX : ℕ),
        (∀ y, (HX y).Monic) → (∀ y, (HX y).natDegree = dX) →
        (∀ i, AnalyticAt ℂ (fun y => (HX y).coeff i) 0) → HX 0 = X ^ dX →
        IsWeierstrassFamily (fun w => HX (Φ w)) dX := by
      intro HX dX hm hdg hcf h0
      refine ⟨fun w => hm _, fun w => hdg _, fun i => (hcf i).comp_of_eq hΦ_an hΦ0, fun i hi => ?_⟩
      show (HX (Φ (0 : CParam s 1))).coeff i = 0
      rw [hΦ0, h0, Polynomial.coeff_X_pow, if_neg (by omega)]
    have hprod : ∀ᶠ w in 𝓝 (0 : CParam s 1), H w = HA (Φ w) * HB (Φ w) := by
      have hqeq : ∀ᶠ x in 𝓝 (0 : Fin (s + 1) → ℂ), q x = HA x * HB x := by
        filter_upwards [heq, isOpen_ball.mem_nhds (mem_ball_self hr0)] with x hx hxr
        rw [← hqt_eq x hxr]; exact hx
      have hΦtend : Tendsto (fun w : CParam s 1 => Φ w) (𝓝 0) (𝓝 (0 : Fin (s + 1) → ℂ)) := by
        have := Φ.continuous.tendsto (0 : CParam s 1); rwa [hΦ0] at this
      filter_upwards [hΦtend.eventually hqeq] with w hw
      have hqΦ : q (Φ w) = H w := by show H (Φ.symm (Φ w)) = H w; rw [Φ.symm_apply_apply]
      rw [← hqΦ]; exact hw
    exact ⟨dA, dB, fun w => HA (Φ w), fun w => HB (Φ w), hdA, hdB,
      hfam HA dA hHAm hHAd hHAc hHA0, hfam HB dB hHBm hHBd hHBc hHB0, hprod⟩
  -- discriminant obligations for `qt`, transferred from `D`
  have hqtD : ∀ w ∈ ball (0 : Fin (s + 1) → ℂ) r,
      (fun y => (qt y).discr) =ᶠ[𝓝 w] D := by
    intro w hw
    filter_upwards [isOpen_ball.mem_nhds hw] with y hy
    show (qt y).discr = (q y).discr; rw [hqt_eq y hy]
  have hord_ne0 : order ℂ D 0 ≠ 0 := order_ne_zero_of_eq_zero D 0 hD0
  have hsep_nbhd : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ),
      ∀ᶠ u in 𝓝[≠] (0 : ℂ), (qt (Fin.cons (u ^ d) z)).Separable := by
    have hκ : Continuous
        (fun p : (Fin s → ℂ) × ℂ => (Fin.cons (p.2 ^ d) p.1 : Fin (s + 1) → ℂ)) := by
      refine continuous_pi (fun j => ?_)
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; exact (continuous_pow d).comp continuous_snd
      · simp only [Fin.cons_succ]; exact (continuous_apply i).comp continuous_fst
    have hκ0 : (Fin.cons ((0 : ℂ) ^ d) (0 : Fin s → ℂ) : Fin (s + 1) → ℂ) = 0 := by
      funext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp [zero_pow hd0.ne']
    have htend : Tendsto (fun p : (Fin s → ℂ) × ℂ => (Fin.cons (p.2 ^ d) p.1 : Fin (s + 1) → ℂ))
        (𝓝 ((0 : Fin s → ℂ), (0 : ℂ))) (𝓝 0) := by
      have h1 := hκ.tendsto ((0 : Fin s → ℂ), (0 : ℂ))
      simpa only [hκ0] using h1
    have hpre : ∀ᶠ p in 𝓝 ((0 : Fin s → ℂ), (0 : ℂ)),
        (Fin.cons (p.2 ^ d) p.1 : Fin (s + 1) → ℂ) ∈ ball 0 R₀ :=
      htend.eventually (ball_mem_nhds 0 hR₀0)
    rw [nhds_prod_eq] at hpre
    filter_upwards [hpre.curry] with z hz_u
    filter_upwards [hz_u.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu_ball hu_ne
    have hune : u ≠ 0 := hu_ne
    have hyball : (Fin.cons (u ^ d) z : Fin (s + 1) → ℂ) ∈ ball 0 R₀ := hu_ball
    rw [hqt_eq _ (ball_subset_ball hR₀r hyball)]
    refine separable_of_discr_ne_zero (hq_monic _) (by rw [hq_deg _]; omega) ?_
    refine hsep_ball (by
      rw [dist_zero_right]
      exact lt_of_lt_of_le (mem_ball_zero_iff.mp hyball) hR₀δ₀) ?_
    rw [Fin.cons_zero]; exact pow_ne_zero d hune
  -- parametrization `φ`
  obtain ⟨φ, hroot, han, hiff⟩ :=
    exists_param_family qt d hd0 hqt_monic hqt_deg hqt_cont
      (fun i => hqt_ana i 0 (mem_ball_self hr0)) hqt0 hirr hδz hanaU hsep_baseU
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / d) with hζdef
  have hζ : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp d hd0.ne'
  -- discriminant normal form for `D`
  have hDvanish' : ∀ᶠ z in 𝓝 (0 : Fin (s + 1) → ℂ), z 0 = 0 → D z = 0 := by
    have hDvanish : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ), D w = 0 := by
      filter_upwards [hconst] with w hw
      by_contra hDw
      exact hord_ne0 (hw.symm.trans (order_eq_zero_of_ne D w hDw))
    rw [eventually_nhdsWithin_iff] at hDvanish
    exact hDvanish
  obtain ⟨G, hGan, hGne0, hDeq⟩ := DiscNormalForm.exists_coord0_pow_factor (order ℂ D 0).toNat D
    hDan hDvanish' rfl (by rw [hord0]; exact hHdisc_ne) hconst
  have hcomb : ∀ᶠ z in 𝓝 (0 : Fin (s + 1) → ℂ),
      (D z = (z 0) ^ (order ℂ D 0).toNat * G z) ∧ G z ≠ 0 ∧ z ∈ ball 0 r := by
    filter_upwards [hDeq, hGan.continuousAt.eventually_ne hGne0,
      isOpen_ball.mem_nhds (mem_ball_self hr0)] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := _root_.eventually_nhds_iff.mp hcomb
  have hGeq : ∀ y ∈ U, (qt y).discr = (y 0) ^ (order ℂ D 0).toNat * G y := by
    intro y hy
    obtain ⟨hDy, _, hyball⟩ := hUsub y hy
    show (qt y).discr = (y 0) ^ (order ℂ D 0).toNat * G y
    rw [hqt_eq y hyball]; exact hDy
  have hGne : ∀ y ∈ U, G y ≠ 0 := fun y hy => (hUsub y hy).2.1
  -- the globalized section `ρ = ψ ∘ radialClamp`
  obtain ⟨ρψ, hρψ0, hψball⟩ := Metric.eventually_nhds_iff.mp hψ_an.eventually_analyticAt
  set δz' : ℝ := min δz (ρψ / 2) with hδz'def
  have hδz' : 0 < δz' := lt_min hδz (by positivity)
  have hδz'δz : δz' ≤ δz := min_le_left _ _
  have hδz'ψ : δz' ≤ ρψ / 2 := min_le_right _ _
  set ρfun : (Fin s → ℂ) → ℂ := fun z => ψ (radialClamp (ρψ / 2) z) with hρfundef
  have hclampnn : (0 : ℝ) ≤ ρψ / 2 := by positivity
  have hψ_contOn : ContinuousOn ψ (Metric.closedBall 0 (ρψ / 2)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact (hψball ((by rw [dist_zero_right]; linarith) :
      dist z (0 : Fin s → ℂ) < ρψ)).continuousAt.continuousWithinAt
  have hmaps : ∀ z : Fin s → ℂ,
      radialClamp (ρψ / 2) z ∈ Metric.closedBall (0 : Fin s → ℂ) (ρψ / 2) := by
    intro z; rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_radialClamp_le_radius hclampnn z
  have hρ_cont : Continuous ρfun :=
    hψ_contOn.comp_continuous (continuous_radialClamp hclampnn) hmaps
  have hρ_eq : ∀ z : Fin s → ℂ, ‖z‖ ≤ ρψ / 2 → ρfun z = ψ z := fun z hz => by
    show ψ (radialClamp (ρψ / 2) z) = ψ z
    exact congrArg ψ (radialClamp_eq_self hz)
  have hρ_ana : ∀ z : Fin s → ℂ, ‖z‖ < δz' → AnalyticAt ℂ ρfun z := by
    intro z hz
    have hzψ : ‖z‖ < ρψ / 2 := lt_of_lt_of_le hz hδz'ψ
    have heq : ρfun =ᶠ[𝓝 z] ψ := by
      filter_upwards [Metric.ball_mem_nhds z (by linarith : (0 : ℝ) < ρψ / 2 - ‖z‖)] with w hw
      rw [mem_ball_iff_norm] at hw
      have hwn : ‖w‖ < ρψ / 2 := by
        calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
          _ < ρψ / 2 := by linarith
      exact hρ_eq w hwn.le
    exact (hψball ((by rw [dist_zero_right]; linarith) :
      dist z (0 : Fin s → ℂ) < ρψ)).congr heq.symm
  -- single-root section for `qt` on the hyperplane
  have hcons_cont : Continuous (fun z : Fin s → ℂ => (Fin.cons 0 z : Fin (s + 1) → ℂ)) :=
    continuous_pi (fun j => Fin.cases continuous_const (fun i => continuous_apply i) j)
  have hcons00 : (Fin.cons 0 (0 : Fin s → ℂ) : Fin (s + 1) → ℂ) = 0 := by
    funext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp
  have hcons_ball : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), (Fin.cons 0 z : Fin (s + 1) → ℂ) ∈ ball 0 r :=
    hcons_cont.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (by rw [hcons00]; exact mem_ball_self hr0))
  have hρψ_ev : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), ‖z‖ < ρψ / 2 :=
    (continuous_norm.tendsto 0).eventually_lt tendsto_const_nhds (by simpa using hρψ0)
  have hroot_single : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), ∀ β : ℂ,
      (qt (Fin.cons 0 z)).IsRoot β ↔ β = ρfun z := by
    filter_upwards [hψ_root, hcons_ball, hρψ_ev] with z hz hball hρz β
    have hΦsymcons : Φ.symm (Fin.cons 0 z) = ((z, 0) : CParam s 1) := by
      rw [hΦ, cparamEquiv_symm_apply]; refine Prod.ext rfl ?_; funext i; simp
    have hqtq : qt (Fin.cons 0 z) = H ((z, 0) : CParam s 1) := by
      rw [hqt_eq _ hball]; show H (Φ.symm (Fin.cons 0 z)) = H ((z, 0) : CParam s 1)
      rw [hΦsymcons]
    rw [hqtq, hρ_eq z hρz.le]; exact hz β
  -- apply the eventual value formula
  have key := order_eval_value_eventually (n := s) hd hqt_monic hqt_deg hqt_cont hδz'
    (fun z u hz => hroot z u (lt_of_lt_of_le hz hδz'δz))
    (fun z u hz => han z u (lt_of_lt_of_le hz hδz'δz))
    (fun z u t hz => hiff z u t (lt_of_lt_of_le hz hδz'δz))
    hζ
    (fun i z hz => hqt_ana i (Fin.cons 0 z) (by
      rw [mem_ball_zero_iff]
      calc ‖(Fin.cons 0 z : Fin (s + 1) → ℂ)‖ ≤ max (‖(Fin.cons 0 z : Fin (s + 1) → ℂ) 0‖)
            (‖Fin.tail (Fin.cons 0 z : Fin (s + 1) → ℂ)‖) := norm_le_max_zero_tail _
        _ = ‖z‖ := by simp [Fin.tail_cons]
        _ < r := by
            have : ‖z‖ < δz := lt_of_lt_of_le hz hδz'δz
            rw [hδzdef] at this; linarith [half_lt_self hR₀0, hR₀r]))
    hρ_cont hρ_ana hroot_single hUopen hUmem hGeq hGne hsep_nbhd
  -- contour radii for the branch-difference constancy (Lemma 4.2.7)
  set Rc : ℝ := min 1 (R₀ / 2) / 2 with hRcdef
  have hRc0 : 0 < Rc := by
    have := lt_min one_pos (show (0 : ℝ) < R₀ / 2 by positivity); positivity
  set ρc : ℝ := Rc / 2 with hρcdef
  have hρc : 0 < ρc := by positivity
  have hρcR : ρc < Rc := by rw [hρcdef]; linarith [half_lt_self hRc0]
  have hRcc : Rc ^ d < Real.exp c := by
    rw [hexpc]
    have hRle1 : Rc ≤ 1 := by
      rw [hRcdef]; have : min 1 (R₀ / 2) ≤ 1 := min_le_left _ _; linarith
    have hRleR₀4 : Rc ≤ R₀ / 4 := by
      rw [hRcdef]; have : min 1 (R₀ / 2) ≤ R₀ / 2 := min_le_right _ _; linarith
    calc Rc ^ d ≤ Rc ^ 1 := pow_le_pow_of_le_one hRc0.le hRle1 (by omega)
      _ = Rc := pow_one Rc
      _ ≤ R₀ / 4 := hRleR₀4
      _ < R₀ / 2 := by linarith [hR₀0]
  -- discriminant obligations for `qt`
  have hqtD0 : order ℂ (fun y => (qt y).discr) 0 = order ℂ D 0 :=
    order_congr_of_eventuallyEq' (hqtD 0 (mem_ball_self hr0))
  have hdisc_ne : order ℂ (fun y => (qt y).discr) (0 : Fin (s + 1) → ℂ) ≠ ⊤ := by
    rw [hqtD0, hord0]; exact hHdisc_ne
  have hdisc_const : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ),
      order ℂ (fun y => (qt y).discr) w = order ℂ (fun y => (qt y).discr) 0 := by
    filter_upwards [hconst, (nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr0)) :
      ball (0 : Fin (s + 1) → ℂ) r ∈ 𝓝[_] (0 : Fin (s + 1) → ℂ))] with w hw_const hw_ball
    rw [order_congr_of_eventuallyEq' (hqtD w hw_ball), hqtD0, hw_const]
  have hdisc_vanish : ∀ᶠ y in 𝓝 (0 : Fin (s + 1) → ℂ), y 0 = 0 → (qt y).discr = 0 := by
    have hDvanish2 : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ), D w = 0 := by
      filter_upwards [hconst] with w hw
      by_contra hDw; exact hord_ne0 (hw.symm.trans (order_eq_zero_of_ne D w hDw))
    rw [eventually_nhdsWithin_iff] at hDvanish2
    filter_upwards [hDvanish2, isOpen_ball.mem_nhds (mem_ball_self hr0)] with y hy_imp hy_ball hy0
    show (qt y).discr = 0; rw [hqt_eq y hy_ball]; exact hy_imp hy0
  -- branch-difference constancy (Lemma 4.2.7) with the SAME `φ`
  have hbranch := branchDiff_orders_eventually_constant_of_discNormalForm hd0 hqt_monic hqt_deg
    hqt_cont (fun i => hqt_ana i 0 (mem_ball_self hr0)) hroot han hiff hζ (by simpa using hδz)
    hsep_nbhd hρc hρcR hRcc hdisc_vanish hdisc_ne hdisc_const
  -- the order at each section point equals the central constant `C`
  set C : ℕ∞ := min (d : ℕ∞) (analyticOrderAt (fun u => φ ((0 : Fin s → ℂ), ζ ^ (0 : ℕ) * u)
    - φ ((0 : Fin s → ℂ), ζ ^ (1 : ℕ) * u)) 0) with hCdef
  have hclaim : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) (((y, 0) : CParam s 1), ψ y) = C := by
    filter_upwards [key, hρψ_ev, hcons_ball, hbranch, hroot_single]
      with y hyex hρy hbally hbr hsy
    obtain ⟨F, hFan, hFeq, hval⟩ := hyex
    have e1 : ρfun y = ψ y := hρ_eq y hρy.le
    set gE : ((Fin (s + 1) → ℂ) × ℂ) ≃L[ℂ] (CParam s 1 × ℂ) :=
      Φ.symm.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ) with hgEdef
    have hqeval_comp : (fun yx : (Fin (s + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
        = (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) ∘ gE := by funext yx; rfl
    have hcongr : (fun yx : (Fin (s + 1) → ℂ) × ℂ => (qt yx.1).eval yx.2)
        =ᶠ[𝓝 (Fin.cons 0 y, ψ y)] (fun yx => (q yx.1).eval yx.2) := by
      have hmem : ∀ᶠ yx in 𝓝 ((Fin.cons 0 y : Fin (s + 1) → ℂ), ψ y),
          yx.1 ∈ ball (0 : Fin (s + 1) → ℂ) r :=
        (continuous_fst.continuousAt).preimage_mem_nhds (isOpen_ball.mem_nhds hbally)
      filter_upwards [hmem] with yx hyx
      show (qt yx.1).eval yx.2 = (q yx.1).eval yx.2; rw [hqt_eq yx.1 hyx]
    have e2 : order ℂ (fun yx : (Fin (s + 1) → ℂ) × ℂ => (qt yx.1).eval yx.2)
          (Fin.cons 0 y, ρfun y)
        = order ℂ (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) (((y, 0) : CParam s 1), ψ y) := by
      have hgpt : gE (Fin.cons 0 y, ψ y) = (((y, 0) : CParam s 1), ψ y) := by
        show (Φ.symm (Fin.cons 0 y), ψ y) = (((y, 0) : CParam s 1), ψ y)
        refine Prod.ext ?_ rfl
        show Φ.symm (Fin.cons 0 y) = ((y, 0) : CParam s 1)
        rw [hΦ, cparamEquiv_symm_apply]; refine Prod.ext rfl ?_; funext i; simp
      rw [e1, order_congr_of_eventuallyEq_C hcongr, hqeval_comp,
        order_comp_cle gE (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) (Fin.cons 0 y, ψ y), hgpt]
    -- `F 0 = ρfun y` (the branch limit is the section root), from order ≥ 1 at the vanishing point
    have hpoint_vanish : (fun yx : (Fin (s + 1) → ℂ) × ℂ => (qt yx.1).eval yx.2)
        (Fin.cons 0 y, ρfun y) = 0 := by
      show (qt (Fin.cons 0 y)).eval (ρfun y) = 0
      rw [monic_eq_pow_of_unique_root (hqt_monic _) (hqt_deg _) hsy]
      simp only [eval_pow, eval_sub, eval_X, eval_C, sub_self]
      exact zero_pow hd0.ne'
    have hord_pos : order ℂ (fun yx : (Fin (s + 1) → ℂ) × ℂ => (qt yx.1).eval yx.2)
        (Fin.cons 0 y, ρfun y) ≠ 0 := order_ne_zero_of_eq_zero _ _ hpoint_vanish
    rw [hval] at hord_pos
    have hF0 : F 0 = ρfun y := by
      by_contra hne
      have hgan : AnalyticAt ℂ (fun w => F w - ρfun y) 0 := hFan.sub analyticAt_const
      have hz : analyticOrderAt (fun w => F w - ρfun y) 0 = 0 :=
        hgan.analyticOrderAt_eq_zero.mpr (show F 0 - ρfun y ≠ 0 from sub_ne_zero.mpr hne)
      rw [hz, min_eq_right (by exact_mod_cast Nat.zero_le d)] at hord_pos
      exact hord_pos rfl
    -- assemble the chain
    calc order ℂ (fun wt : CParam s 1 × ℂ => (H wt.1).eval wt.2) (((y, 0) : CParam s 1), ψ y)
        = order ℂ (fun yx : (Fin (s + 1) → ℂ) × ℂ => (qt yx.1).eval yx.2)
            (Fin.cons 0 y, ρfun y) := e2.symm
      _ = min (d : ℕ∞) (analyticOrderAt (fun w => F w - ρfun y) 0) := hval
      _ = min (d : ℕ∞) (analyticOrderAt (fun u => F u - F (ζ * u)) 0) :=
          min_order_displacement_eq_diff hFan (ρfun y) hF0 hd0 hζ
      _ = min (d : ℕ∞) (analyticOrderAt (fun u => φ (y, ζ ^ (0 : ℕ) * u)
            - φ (y, ζ ^ (1 : ℕ) * u)) 0) := by
          rw [analyticOrderAt_F_diff_eq_phi hFeq (hζ.ne_zero (by omega))]
      _ = C := by
          rw [hCdef]; congr 1
          exact hbr ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  -- constancy
  filter_upwards [hclaim] with y hy
  rw [hy, ← hclaim.self_of_nhds]

end Puiseux
