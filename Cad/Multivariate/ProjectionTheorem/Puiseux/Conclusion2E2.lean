import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2Factor
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiE2Main
import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2E2Transport

/-!
# Conclusion 2 — the `e ≥ 2` order-under-blow-up, discharged

This file discharges the last temporary axiom `Puiseux.order_eval_value_e2_blowup` (declared in
`Conclusion2General.lean`). It mirrors the Conclusion-1 blow-up
`ZariskiE2.irreducible_section_single_root_blowup_proof`, but concludes order-constancy of the
*evaluation* along the section instead of the single-root structure.

The geometric setup (globalize `fac → Ht`; transverse automorphism `M`; normal form on `disc`;
build the codimension-one blown family `a'`; transport its discriminant facts) is reused verbatim from
the Conclusion-1 template. The new ingredients are:

* apply the proved **`order_invariant_in_graph_e1`** to `a'` (which handles reducible families
  internally), obtaining constancy of `order` of `a'`'s evaluation along the *blown* section
  `{(append y 0, 0)}`;
* the **order transport** relating `order (fac-eval) ((y,0), ψ y)` to
  `order (a'-eval) ((append y 0, 0), ψ y)` through the degenerate blow-up `Ψ = idM ∘ Qcp`.
-/

noncomputable section

open Polynomial Filter BlowupNormalForm ZariskiE2 CoordTranslate BlowupMap
open scoped Topology

namespace Puiseux

variable {s k : ℕ}

/-- **The `e ≥ 2` order-under-blow-up, PROVED** — the discharge of `order_eval_value_e2_blowup`. -/
theorem order_eval_value_e2_blowup_proof {s k : ℕ} (fac : CParam s (k + 2) → Polynomial ℂ) (d : ℕ)
    (hd : 2 ≤ d) (hfam : IsWeierstrassFamily fac d)
    (hdisc_ne : order ℂ (fun w => (fac w).discr) (0 : CParam s (k + 2)) ≠ ⊤)
    (hdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (fac w).discr) ((y, 0) : CParam s (k + 2))
        = order ℂ (fun w => (fac w).discr) ((0, 0) : CParam s (k + 2)))
    (ψ : (Fin s → ℂ) → ℂ) (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (fac ((y, 0) : CParam s (k + 2))).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2)
          (((y, 0) : CParam s (k + 2)), ψ y)
        = order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2)
            (((0, 0) : CParam s (k + 2)), ψ 0) := by
  classical
  -- `r := ord₀(disc fac)`, finite, and the section order is `≥ r`
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hdisc_ne
  have hr' : order ℂ (fun w => (fac w).discr) (0 : CParam s (k + 2)) = (r : ℕ∞) := hr.symm
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h; swap; · exact h
    exfalso
    have hd0 : (fun w => (fac w).discr) (0 : CParam s (k + 2)) = 0 := by
      show (fac 0).discr = 0; rw [hfam.eval_zero]; exact discr_X_pow_eq_zero hd
    have := order_ne_zero_of_eq_zero (fun w => (fac w).discr) 0 hd0
    rw [hr', h0] at this; exact this rfl
  -- globalize `fac` to `Ht` (disc analytic on a ball)
  obtain ⟨Ht, ρ, hρ, htm, htd, _htc, hte, hta⟩ :=
    FamilyGlobalize.exists_globalized_family (q := fac) hfam.monic hfam.degree_eq
      hfam.coeff_analyticAt
  set g : CParam s (k + 2) → ℂ := fun w => (Ht w).discr with hg
  have hgH : g =ᶠ[𝓝 (0 : CParam s (k + 2))] fun w => (fac w).discr := by
    have hball : Metric.ball (0 : CParam s (k + 2)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
    filter_upwards [hball] with w hw
    show (Ht w).discr = (fac w).discr
    rw [hte w hw]
  have hg_ball : ∀ p ∈ Metric.ball (0 : CParam s (k + 2)) ρ, AnalyticAt ℂ g p := fun p hp =>
    familyDiscr_analyticAt_pt Ht d (by omega) htm htd p (fun i => hta i p hp)
  have hg0 : AnalyticAt ℂ g 0 := hg_ball 0 (Metric.mem_ball_self hρ)
  have hsec_tendsto : Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s (k + 2))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s (k + 2))) := by fun_prop
    simpa using hc.tendsto' 0 0 (by simp)
  have hg_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g ((y, 0) : CParam s (k + 2)) := by
    filter_upwards [hsec_tendsto.eventually (Metric.ball_mem_nhds 0 hρ)] with y hy
    exact hg_ball _ hy
  have horder_g : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ g ((y, 0) : CParam s (k + 2)) = (r : ℕ∞) := by
    filter_upwards [hdisc_oi, hsec_tendsto.eventually hgH.eventually_nhds]
      with y hy_oi hy_germ
    have h1 : order ℂ g ((y, 0) : CParam s (k + 2))
        = order ℂ (fun w => (fac w).discr) ((y, 0) : CParam s (k + 2)) :=
      order_congr_of_eventuallyEq' hy_germ
    rw [h1, hy_oi]; exact hr'
  have hord_g : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j < r, iteratedFDeriv ℂ j g ((y, 0) : CParam s (k + 2)) = 0 := by
    filter_upwards [horder_g] with y hy j hj
    exact iteratedFDeriv_eq_zero_of_lt_order (by rw [hy]; exact_mod_cast hj)
  have hord_ne_g : iteratedFDeriv ℂ r g (0 : CParam s (k + 2)) ≠ 0 := by
    have hg0ord : order ℂ g (0 : CParam s (k + 2)) = (r : ℕ∞) := by
      rw [order_congr_of_eventuallyEq' hgH, ← hr']
    exact (order_eq_natCast_iff.mp hg0ord).2
  -- genericity: a good transverse direction `ξ`
  obtain ⟨ξ, hξ⟩ := genericity_exists g r hg0 hg_at hord_g hord_ne_g
  have hξ_ne : ξ ≠ 0 := by
    intro h0; apply hξ; rw [h0]
    exact ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℂ r g 0) ⟨0, hr1⟩ rfl
  obtain ⟨M, hM⟩ := TransverseShear.exists_transverseCLE ξ hξ_ne
  set idM : CParam s (k + 2) ≃L[ℂ] CParam s (k + 2) :=
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (Fin s → ℂ)) M with hidM
  have hidM_apply : ∀ p : CParam s (k + 2), idM p = (p.1, M p.2) := fun p => rfl
  have hidM0 : idM 0 = 0 := map_zero _
  set g' : CParam s (k + 2) → ℂ := fun w => g (idM w) with hg'
  have hidM_an : AnalyticAt ℂ (fun w : CParam s (k + 2) => idM w) 0 :=
    (idM : CParam s (k + 2) →L[ℂ] CParam s (k + 2)).analyticAt 0
  have hg'0 : AnalyticAt ℂ g' 0 := hg0.comp_of_eq hidM_an hidM0
  have hg'_sec : ∀ y : Fin s → ℂ, idM ((y, 0) : CParam s (k + 2)) = ((y, 0) : CParam s (k + 2)) := by
    intro y; rw [hidM_apply]; simp [map_zero]
  have hg'_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g' ((y, 0) : CParam s (k + 2)) := by
    filter_upwards [hg_at] with y hy
    exact hy.comp_of_eq ((idM : CParam s (k + 2) →L[ℂ] CParam s (k + 2)).analyticAt _) (hg'_sec y)
  have hord_g' : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j < r, iteratedFDeriv ℂ j g' ((y, 0) : CParam s (k + 2)) = 0 := by
    filter_upwards [horder_g] with y hy j hj
    have hord' : order ℂ g' ((y, 0) : CParam s (k + 2)) = (r : ℕ∞) := by
      show order ℂ (g ∘ ⇑idM) ((y, 0) : CParam s (k + 2)) = (r : ℕ∞)
      rw [order_comp_cle idM g, hg'_sec y, hy]
    exact iteratedFDeriv_eq_zero_of_lt_order (by rw [hord']; exact_mod_cast hj)
  have hB_an : AnalyticAt ℂ (B (s := s) (k := k)) 0 := by
    have hΦsymm : AnalyticAt ℂ
        (fun Z : Fin (s + (k + 1) + 1) → ℂ => (cparamEquiv (s + (k + 1))).symm Z) 0 :=
      ((cparamEquiv (s + (k + 1))).symm :
        (Fin (s + (k + 1) + 1) → ℂ) →L[ℂ] CParam (s + (k + 1)) 1).analyticAt 0
    have hΦ0 : (cparamEquiv (s + (k + 1))).symm (0 : Fin (s + (k + 1) + 1) → ℂ) = 0 := map_zero _
    have coordFst : ∀ i : Fin (s + (k + 1)),
        AnalyticAt ℂ (fun W : CParam (s + (k + 1)) 1 => W.1 i) 0 := fun i =>
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin (s + (k + 1)) → ℂ) (Fin 1 → ℂ))).analyticAt 0
    have coordSnd : AnalyticAt ℂ (fun W : CParam (s + (k + 1)) 1 => W.2 0) 0 :=
      ((ContinuousLinearMap.proj (0 : Fin 1)).comp
        (ContinuousLinearMap.snd ℂ (Fin (s + (k + 1)) → ℂ) (Fin 1 → ℂ))).analyticAt 0
    have hQcp : AnalyticAt ℂ (Qcp (s := s) (k := k)) 0 := by
      unfold Qcp Q
      apply AnalyticAt.prod
      · rw [analyticAt_pi_iff]; intro j; exact coordFst _
      · rw [analyticAt_pi_iff]; intro a
        refine Fin.lastCases ?_ ?_ a
        · simp only [Fin.snoc_last]; exact coordSnd
        · intro i; simp only [Fin.snoc_castSucc]; exact (coordFst _).mul coordSnd
    exact hQcp.comp_of_eq hΦsymm hΦ0
  have hg'B_an : AnalyticAt ℂ (fun Z => g' (B Z)) 0 :=
    hg'0.comp_of_eq hB_an (B_zero)
  obtain ⟨N, hN_an, hfact⟩ := normalForm g' r hg'B_an hg'_at hord_g'
  have hξOf0 : idM (ξOf (0 : Fin (s + (k + 1) + 1) → ℂ)) = ((0 : Fin s → ℂ), ξ) := by
    rw [hidM_apply]
    refine Prod.ext rfl ?_
    show M (ξOf (0 : Fin (s + (k + 1) + 1) → ℂ)).2 = ξ
    have h2 : (ξOf (0 : Fin (s + (k + 1) + 1) → ℂ)).2
        = (Pi.single (Fin.last (k + 1)) 1 : Fin (k + 2) → ℂ) := by
      show (Fin.snoc (Fin.tail (0 : Fin (s + (k + 1) + 1) → ℂ) ∘ Fin.natAdd s) 1 : Fin (k + 2) → ℂ)
        = Pi.single (Fin.last (k + 1)) 1
      rw [show (Fin.tail (0 : Fin (s + (k + 1) + 1) → ℂ) ∘ Fin.natAdd s) = (0 : Fin (k + 1) → ℂ)
        by funext i; simp [Fin.tail]]
      exact snoc_zero_one_eq_single
    rw [h2, hM]
  have hN0 : N 0 ≠ 0 := by
    have hL : (pderiv0)^[r] (fun Z => g' (B Z)) 0 = (r.factorial : ℂ) * N 0 := by
      rw [(pderiv0_iterate_congr r hfact).self_of_nhds, pderiv0_iterate_pow_mul_eval hN_an r]
    have hR : (pderiv0)^[r] (fun Z => g' (B Z)) 0
        = iteratedFDeriv ℂ r g' 0 (fun _ => ξOf 0) := by
      rw [(pderiv0_iterate_eq_iteratedDeriv hg'B_an r).self_of_nhds]
      have hslice : (fun t : ℂ => g' (B ((0 : Fin (s + (k + 1) + 1) → ℂ) + t • e0 (s + (k + 1)))))
          = fun t : ℂ => g' ((0 : CParam s (k + 2)) + t • ξOf 0) := by
        funext t
        rw [B_line 0 (by simp) t]
        congr 1
      rw [hslice, iteratedDeriv_line_eq (ξOf 0) hg'0 r]
    have hfd : iteratedFDeriv ℂ r g' 0 (fun _ => ξOf 0)
        = iteratedFDeriv ℂ r g 0 (fun _ => ((0 : Fin s → ℂ), ξ)) := by
      rw [← iteratedDeriv_line_eq (ξOf 0) hg'0 r,
        ← iteratedDeriv_line_eq ((0, ξ) : CParam s (k + 2)) hg0 r]
      congr 1
      funext t
      show g (idM ((0 : CParam s (k + 2)) + t • ξOf 0)) = g ((0 : CParam s (k + 2)) + t • (0, ξ))
      rw [zero_add, zero_add, map_smul, hξOf0]
    rw [hR, hfd] at hL
    intro hN0'
    rw [hN0', mul_zero] at hL
    exact hξ hL
  -- the codimension-one family `a'`
  set Ht'' : CParam s (k + 2) → Polynomial ℂ := fun w => Ht (idM w) with hHt''
  have hHt''_monic : ∀ w, (Ht'' w).Monic := fun w => htm _
  have hHt''_deg : ∀ w, (Ht'' w).natDegree = d := fun w => htd _
  set a' : Fin d → (CParam (s + (k + 1)) 1 → ℂ) :=
    fun i W => (Ht'' (Qcp W)).coeff (i : ℕ) with ha'
  have hwp : ∀ W, weierstrassPoly d a' W = Ht'' (Qcp W) := fun W =>
    weierstrassPoly_recon (fun W => Ht'' (Qcp W)) d (fun W => hHt''_monic _)
      (fun W => hHt''_deg _) W
  have hWD : ∀ W, weierstrassDiscFn d a' W = g' (Qcp W) := by
    intro W
    show (weierstrassPoly d a' W).discr = g (idM (Qcp W))
    rw [hwp]
  have hQcp_an : AnalyticAt ℂ (Qcp (s := s) (k := k)) 0 := by
    have coordFst : ∀ i : Fin (s + (k + 1)),
        AnalyticAt ℂ (fun W : CParam (s + (k + 1)) 1 => W.1 i) 0 := fun i =>
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin (s + (k + 1)) → ℂ) (Fin 1 → ℂ))).analyticAt 0
    have coordSnd : AnalyticAt ℂ (fun W : CParam (s + (k + 1)) 1 => W.2 0) 0 :=
      ((ContinuousLinearMap.proj (0 : Fin 1)).comp
        (ContinuousLinearMap.snd ℂ (Fin (s + (k + 1)) → ℂ) (Fin 1 → ℂ))).analyticAt 0
    unfold Qcp Q
    apply AnalyticAt.prod
    · rw [analyticAt_pi_iff]; intro j; exact coordFst _
    · rw [analyticAt_pi_iff]; intro a
      refine Fin.lastCases ?_ ?_ a
      · simp only [Fin.snoc_last]; exact coordSnd
      · intro i; simp only [Fin.snoc_castSucc]; exact (coordFst _).mul coordSnd
  have hQcp0 : Qcp (0 : CParam (s + (k + 1)) 1) = 0 := Qcp_zero
  have hidM_an' : AnalyticAt ℂ (fun w : CParam s (k + 2) => idM w) 0 :=
    (idM : CParam s (k + 2) →L[ℂ] CParam s (k + 2)).analyticAt 0
  have ha_an : ∀ i, AnalyticAt ℂ (a' i) 0 := by
    intro i
    have hHtc : AnalyticAt ℂ (fun w : CParam s (k + 2) => (Ht w).coeff (i : ℕ)) 0 :=
      hta (i : ℕ) 0 (Metric.mem_ball_self hρ)
    have hcomp : AnalyticAt ℂ
        (fun W : CParam (s + (k + 1)) 1 => idM (Qcp W)) 0 :=
      hidM_an'.comp_of_eq hQcp_an hQcp0
    exact hHtc.comp_of_eq hcomp (by rw [hQcp0]; exact hidM0)
  have ha0 : ∀ i, a' i 0 = 0 := by
    intro i
    show (Ht'' (Qcp 0)).coeff (i : ℕ) = 0
    rw [hQcp0]
    show (Ht (idM 0)).coeff (i : ℕ) = 0
    rw [hidM0, hte 0 (Metric.mem_ball_self hρ), hfam.eval_zero, Polynomial.coeff_X_pow,
      if_neg (by have := i.isLt; omega)]
  -- transport the section disc facts through `Φ' = cparamEquiv (s+(k+1))`
  have horderB := order_gB g' r N hN_an hfact hN0
  have htrans : ∀ W : CParam (s + (k + 1)) 1,
      order ℂ (fun W => g' (Qcp W)) W
        = order ℂ (fun Z => g' (B Z)) (cparamEquiv (s + (k + 1)) W) := by
    intro W
    have h := order_comp_cle (cparamEquiv (s + (k + 1))).symm (fun U => g' (Qcp U))
      (cparamEquiv (s + (k + 1)) W)
    rw [(cparamEquiv (s + (k + 1))).symm_apply_apply] at h
    exact h.symm
  have hcoord0 : ∀ Y : Fin (s + (k + 1)) → ℂ,
      (cparamEquiv (s + (k + 1)) ((Y, 0) : CParam (s + (k + 1)) 1)) 0 = 0 := by
    intro Y; rw [cparamEquiv_apply, Fin.cons_zero]; rfl
  have hΦsec_tendsto : Tendsto
      (fun Y : Fin (s + (k + 1)) → ℂ =>
        cparamEquiv (s + (k + 1)) ((Y, 0) : CParam (s + (k + 1)) 1)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun Y : Fin (s + (k + 1)) → ℂ =>
        cparamEquiv (s + (k + 1)) ((Y, 0) : CParam (s + (k + 1)) 1)) :=
      (cparamEquiv (s + (k + 1))).continuous.comp (continuous_id.prodMk continuous_const)
    have h0 : cparamEquiv (s + (k + 1))
        (((0 : Fin (s + (k + 1)) → ℂ), (0 : Fin 1 → ℂ)) : CParam (s + (k + 1)) 1) = 0 := map_zero _
    simpa [h0] using hc.tendsto 0
  have hWDeq : weierstrassDiscFn d a' = fun W => g' (Qcp W) := funext hWD
  have hWD0 : order ℂ (weierstrassDiscFn d a') (0 : CParam (s + (k + 1)) 1) = (r : ℕ∞) := by
    rw [hWDeq, htrans 0,
      show cparamEquiv (s + (k + 1)) (0 : CParam (s + (k + 1)) 1) = 0 from map_zero _]
    exact horderB.self_of_nhds (by simp)
  have hWDsec : ∀ᶠ Y in 𝓝 (0 : Fin (s + (k + 1)) → ℂ),
      order ℂ (weierstrassDiscFn d a') ((Y, 0) : CParam (s + (k + 1)) 1) = (r : ℕ∞) := by
    filter_upwards [hΦsec_tendsto.eventually horderB] with Y hY
    rw [hWDeq, htrans (Y, 0)]
    exact hY (hcoord0 Y)
  have hdisc_ne' : order ℂ (weierstrassDiscFn d a') (0 : CParam (s + (k + 1)) 1) ≠ ⊤ := by
    rw [hWD0]; exact ENat.coe_ne_top r
  have hdisc' : ∀ᶠ y in 𝓝 (0 : Fin (s + (k + 1)) → ℂ),
      order ℂ (weierstrassDiscFn d a') ((y, 0) : CParam (s + (k + 1)) 1)
        = order ℂ (weierstrassDiscFn d a') (0 : CParam (s + (k + 1)) 1) := by
    filter_upwards [hWDsec] with Y hY; rw [hY, hWD0]
  -- ψ' = ψ ∘ firstₛ, the section root of `a'`
  set firstₛ : (Fin (s + (k + 1)) → ℂ) → (Fin s → ℂ) :=
    fun Y => Y ∘ Fin.castAdd (k + 1) with hfirstₛ
  set ψ' : (Fin (s + (k + 1)) → ℂ) → ℂ := fun Y => ψ (firstₛ Y) with hψ'def
  -- the blown-section poly identity: `weierstrassPoly d a' (Y,0) = Ht (firstₛ Y, 0)`
  have hsecpoly : ∀ Y : Fin (s + (k + 1)) → ℂ,
      weierstrassPoly d a' ((Y, 0) : CParam (s + (k + 1)) 1)
        = Ht ((firstₛ Y, 0) : CParam s (k + 2)) := by
    intro Y
    rw [hwp]
    show Ht (idM (Qcp ((Y, 0) : CParam (s + (k + 1)) 1))) = Ht ((firstₛ Y, 0) : CParam s (k + 2))
    congr 1
    have hQ : Qcp ((Y, 0) : CParam (s + (k + 1)) 1) = ((firstₛ Y, 0) : CParam s (k + 2)) := by
      show Q (Y ∘ Fin.castAdd (k + 1), Y ∘ Fin.natAdd s, (0 : Fin 1 → ℂ) 0)
        = ((firstₛ Y, 0) : CParam s (k + 2))
      rw [Q_apply]
      refine Prod.ext rfl ?_
      funext i; refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc]
    rw [hQ, hg'_sec]
  -- `firstₛ 0 = 0`, continuity, and convergence to `0`
  have hfirstₛ0 : firstₛ (0 : Fin (s + (k + 1)) → ℂ) = 0 := by funext i; simp [hfirstₛ]
  have hfirstₛ_an : AnalyticAt ℂ firstₛ 0 := by
    show AnalyticAt ℂ (fun Y : Fin (s + (k + 1)) → ℂ => fun i => Y (Fin.castAdd (k + 1) i)) 0
    rw [analyticAt_pi_iff]
    intro i
    exact (ContinuousLinearMap.proj (Fin.castAdd (k + 1) i) :
      (Fin (s + (k + 1)) → ℂ) →L[ℂ] ℂ).analyticAt 0
  have hfirstₛ_cont : Continuous firstₛ := by rw [hfirstₛ]; fun_prop
  have hfirstₛ_tendsto : Tendsto firstₛ (𝓝 0) (𝓝 0) := by
    simpa [hfirstₛ0] using hfirstₛ_cont.tendsto 0
  -- `ψ' = ψ ∘ firstₛ` is the section root of `a'`
  have hψ0 : ψ 0 = 0 := by
    have h := hψ_root.self_of_nhds
    have hroot0 : (fac ((0, 0) : CParam s (k + 2))).IsRoot 0 := by
      rw [show ((0, 0) : CParam s (k + 2)) = 0 from rfl, hfam.eval_zero]
      simp [Polynomial.IsRoot.def, zero_pow (show d ≠ 0 by omega)]
    exact ((h 0).mp hroot0).symm
  have hψ'0val : ψ' (0 : Fin (s + (k + 1)) → ℂ) = ψ 0 := by simp only [hψ'def, hfirstₛ0]
  have hψ'_an : AnalyticAt ℂ ψ' 0 := by
    have := hψ_an.comp_of_eq hfirstₛ_an hfirstₛ0
    simpa [hψ'def, Function.comp_def] using this
  have hψ'0 : ψ' (0 : Fin (s + (k + 1)) → ℂ) = 0 := by rw [hψ'0val, hψ0]
  have hsec2_tendsto : Tendsto (fun Y : Fin (s + (k + 1)) → ℂ => ((firstₛ Y, 0) : CParam s (k + 2)))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun Y : Fin (s + (k + 1)) → ℂ => ((firstₛ Y, 0) : CParam s (k + 2))) := by
      exact (hfirstₛ_cont.prodMk continuous_const)
    simpa using hc.tendsto' 0 0 (by simp [hfirstₛ0])
  have hψ'_root : ∀ᶠ Y in 𝓝 (0 : Fin (s + (k + 1)) → ℂ), ∀ α : ℂ,
      (weierstrassPoly d a' ((Y, 0) : CParam (s + (k + 1)) 1)).IsRoot α ↔ α = ψ' Y := by
    filter_upwards [hfirstₛ_tendsto.eventually hψ_root,
      hsec2_tendsto.eventually (Metric.ball_mem_nhds 0 hρ)] with Y hY_root hY_mem
    intro α
    rw [hsecpoly Y, hte _ hY_mem]
    exact hY_root α
  -- apply the proved codimension-one order-invariance to `a'`
  have he1 := order_invariant_in_graph_e1 d (by omega) a' ha_an ha0 hdisc_ne' hdisc'
    ψ' hψ'_an hψ'_root
  -- push to the *blown* section `{(append y 0, 0)}`
  set emb : (Fin s → ℂ) → (Fin (s + (k + 1)) → ℂ) :=
    fun y => Fin.append y (0 : Fin (k + 1) → ℂ) with hemb
  have hemb0 : emb (0 : Fin s → ℂ) = 0 := by
    funext i
    show Fin.append (0 : Fin s → ℂ) (0 : Fin (k + 1) → ℂ) i = (0 : Fin (s + (k + 1)) → ℂ) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  have hfirstₛemb : ∀ y : Fin s → ℂ, firstₛ (emb y) = y := by
    intro y; funext i; simp [hfirstₛ, hemb, Fin.append_left]
  have hψ'emb : ∀ y : Fin s → ℂ, ψ' (emb y) = ψ y := by
    intro y; simp only [hψ'def, hfirstₛemb]
  have hemb_tendsto : Tendsto emb (𝓝 0) (𝓝 (0 : Fin (s + (k + 1)) → ℂ)) := by
    have hc : Continuous emb := by
      rw [hemb]; apply continuous_pi; intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]; exact continuous_apply j
      · simp only [Fin.append_right]; exact continuous_const
    simpa [hemb0] using hc.tendsto 0
  have hblown : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
          (((emb y, 0) : CParam (s + (k + 1)) 1), ψ y)
        = order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
          (((0, 0) : CParam (s + (k + 1)) 1), ψ 0) := by
    filter_upwards [hemb_tendsto.eventually he1] with y hy
    rw [← hψ'emb y, ← hψ'0val]; exact hy
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- THE ORDER TRANSPORT (the one remaining deep step). `a'-eval = fac-eval ∘ (Ψ × id)` near the
  -- section, with `Ψ = idM ∘ Qcp` and `Ψ (emb y, 0) = (y, 0)`. Since `Q` is *degenerate* at the
  -- section (its Jacobian drops rank where `u = 0`), `order_le_order_comp_C` gives only the easy
  -- inequality `order (fac-eval) ((y,0),ψy) ≤ order (a'-eval) ((emb y,0),ψy)`. The reverse
  -- inequality is the genuine content: the blow-up multiplicity correction must be shown constant
  -- in `y`. Equivalently, the disc-generic transverse direction `ξ = M (e_last)` realizes the
  -- evaluation order along the `u`-slices uniformly in `y` (thesis "`t ≥ ord h'`" homogeneous Taylor
  -- part tracking). This is the only gap; everything above is verified, axiom-clean infrastructure.
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- the transport map `Θ = (idM ∘ Qcp) × id` and the exact identity `a'-eval = (Ht-eval) ∘ Θ`
  set Θ : CParam (s + (k + 1)) 1 × ℂ → CParam s (k + 2) × ℂ :=
    fun Wt => (idM (Qcp Wt.1), Wt.2) with hΘ
  have haΘ : (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
      = (fun wt : CParam s (k + 2) × ℂ => (Ht wt.1).eval wt.2) ∘ Θ := by
    funext Wt
    show (weierstrassPoly d a' Wt.1).eval Wt.2 = (Ht (idM (Qcp Wt.1))).eval Wt.2
    rw [hwp]
  have hQcpsec : ∀ Y : Fin (s + (k + 1)) → ℂ,
      Qcp ((Y, 0) : CParam (s + (k + 1)) 1) = ((firstₛ Y, 0) : CParam s (k + 2)) := by
    intro Y
    show Q (Y ∘ Fin.castAdd (k + 1), Y ∘ Fin.natAdd s, (0 : Fin 1 → ℂ) 0)
      = ((firstₛ Y, 0) : CParam s (k + 2))
    rw [Q_apply]
    refine Prod.ext rfl ?_
    funext i; refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc]
  -- `Ht-eval` is analytic (hence `ContDiffOn`) on `ball ρ ×ˢ univ`
  have hHteval_an : AnalyticOnNhd ℂ (fun wt : CParam s (k + 2) × ℂ => (Ht wt.1).eval wt.2)
      (Metric.ball (0 : CParam s (k + 2)) ρ ×ˢ (Set.univ : Set ℂ)) := by
    intro p hp
    have hp1 : p.1 ∈ Metric.ball (0 : CParam s (k + 2)) ρ := hp.1
    have heq : (fun wt : CParam s (k + 2) × ℂ => (Ht wt.1).eval wt.2)
        = fun wt => ∑ i ∈ Finset.range (d + 1), (Ht wt.1).coeff i * wt.2 ^ i := by
      funext wt
      exact Polynomial.eval_eq_sum_range' (by rw [htd]; omega) wt.2
    rw [heq]
    refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
    refine AnalyticAt.mul ?_ ?_
    · exact (hta i p.1 hp1).comp_of_eq
        ((ContinuousLinearMap.fst ℂ (CParam s (k + 2)) ℂ).analyticAt p) rfl
    · exact ((ContinuousLinearMap.snd ℂ (CParam s (k + 2)) ℂ).analyticAt p).pow i
  -- `Θ` is `ContDiff` everywhere
  have hΘ_cd : ContDiff ℂ (⊤ : WithTop ℕ∞) Θ := by
    rw [hΘ]
    refine ContDiff.prodMk ?_ contDiff_snd
    refine (idM : CParam s (k + 2) →L[ℂ] CParam s (k + 2)).contDiff.comp ?_
    have hQcp_cd : ContDiff ℂ (⊤ : WithTop ℕ∞) (Qcp (s := s) (k := k)) := by
      unfold Qcp Q
      refine ContDiff.prodMk ?_ ?_
      · fun_prop
      · refine contDiff_pi.2 (fun a => ?_)
        refine Fin.lastCases ?_ ?_ a
        · simp only [Fin.snoc_last]; fun_prop
        · intro i; simp only [Fin.snoc_castSucc]; fun_prop
    exact hQcp_cd.comp contDiff_fst
  have hΘ_cont : Continuous Θ := hΘ_cd.continuous
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- THE ORDER TRANSPORT. The EASY inequality `order (fac-eval) ≤ order (a'-eval)` is proved below
  -- via `order_le_order_comp_C` (`a'-eval = Ht-eval ∘ Θ`, with `Θ` analytic). The REVERSE
  -- inequality `order (a'-eval) ≤ order (fac-eval)` is the one remaining deep step: because `Q` is
  -- *degenerate* at the section (its Jacobian drops rank where `u = 0`), composition does not
  -- decrease the order for free. It requires the disc-generic transverse direction `ξ = M (e_last)`
  -- to realize the evaluation order along the `u`-slices uniformly in `y` (thesis "`t ≥ ord h'`"
  -- homogeneous Taylor-part tracking). Everything else in this file is verified, axiom-clean.
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  have htransport : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2)
          (((y, 0) : CParam s (k + 2)), ψ y)
        = order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
          (((emb y, 0) : CParam (s + (k + 1)) 1), ψ y) := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he1
    filter_upwards [hsec_tendsto.eventually (Metric.ball_mem_nhds 0 hρ), hψ_root,
      Metric.ball_mem_nhds (0 : Fin s → ℂ) hε] with y hy_ball hy_root hy_ε
    -- replace `fac-eval` by `Ht-eval` at the section point (germ equality on the ball)
    have hford : order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2)
          (((y, 0) : CParam s (k + 2)), ψ y)
        = order ℂ (fun wt : CParam s (k + 2) × ℂ => (Ht wt.1).eval wt.2)
          (((y, 0) : CParam s (k + 2)), ψ y) := by
      refine order_congr_of_eventuallyEq' ?_
      have hopen : IsOpen {wt : CParam s (k + 2) × ℂ |
          wt.1 ∈ Metric.ball (0 : CParam s (k + 2)) ρ} := Metric.isOpen_ball.preimage continuous_fst
      filter_upwards [hopen.mem_nhds (show _ ∈ _ from hy_ball)] with wt hwt
      show (fac wt.1).eval wt.2 = (Ht wt.1).eval wt.2
      rw [hte wt.1 hwt]
    -- `Θ ((emb y,0), ψ y) = ((y,0), ψ y)`
    have hΘx : Θ (((emb y, 0) : CParam (s + (k + 1)) 1), ψ y) = (((y, 0) : CParam s (k + 2)), ψ y) := by
      rw [hΘ]
      refine Prod.ext ?_ rfl
      show idM (Qcp ((emb y, 0) : CParam (s + (k + 1)) 1)) = ((y, 0) : CParam s (k + 2))
      rw [hQcpsec (emb y), hfirstₛemb y, hg'_sec]
    rw [hford, haΘ]
    -- the easy direction; the reverse inequality is the deep gap
    refine le_antisymm ?_ ?_
    · -- `order (Ht-eval) ((y,0),ψy) ≤ order (Ht-eval ∘ Θ) ((emb y,0),ψy)`
      set t : Set (CParam s (k + 2) × ℂ) :=
        Metric.ball (0 : CParam s (k + 2)) ρ ×ˢ (Set.univ : Set ℂ) with ht_def
      have ht_open : IsOpen t := Metric.isOpen_ball.prod isOpen_univ
      have hxt : Θ (((emb y, 0) : CParam (s + (k + 1)) 1), ψ y) ∈ t := by
        rw [hΘx, ht_def]; exact ⟨hy_ball, Set.mem_univ _⟩
      set sset : Set (CParam (s + (k + 1)) 1 × ℂ) := Θ ⁻¹' t with hsset
      have hs_open : IsOpen sset := ht_open.preimage hΘ_cont
      have hx_s : (((emb y, 0) : CParam (s + (k + 1)) 1), ψ y) ∈ sset := hxt
      have hcomp := order_le_order_comp_C (g := fun wt : CParam s (k + 2) × ℂ => (Ht wt.1).eval wt.2)
        (f := Θ) hs_open ht_open hx_s (hHteval_an.contDiffOn_of_completeSpace)
        (hΘ_cd.contDiffOn) (Set.mapsTo_preimage Θ t)
      rwa [hΘx] at hcomp
    · -- THE REVERSE INEQUALITY — thesis stage 8 "t ≥ ord h'" TERM-TRACKING (thesis.tex 2388–2487).
      set p : CParam (s + (k + 1)) 1 × ℂ := (((emb y, 0) : CParam (s + (k + 1)) 1), ψ y) with hp
      set Geval : CParam s (k + 2) × ℂ → ℂ := fun wt => (Ht wt.1).eval wt.2 with hGeval
      have hG_an : AnalyticAt ℂ Geval ((y, 0), ψ y) := hHteval_an _ ⟨hy_ball, Set.mem_univ _⟩
      -- `Qcp` analytic everywhere, hence `Θ` analytic at every blown point `((Y,0), x)`
      have hQcp_an_all : ∀ q : CParam (s + (k + 1)) 1, AnalyticAt ℂ (Qcp (s := s) (k := k)) q := by
        intro q
        have coordFst : ∀ i : Fin (s + (k + 1)),
            AnalyticAt ℂ (fun W : CParam (s + (k + 1)) 1 => W.1 i) q := fun i =>
          ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.fst ℂ (Fin (s + (k + 1)) → ℂ) (Fin 1 → ℂ))).analyticAt q
        have coordSnd : AnalyticAt ℂ (fun W : CParam (s + (k + 1)) 1 => W.2 0) q :=
          ((ContinuousLinearMap.proj (0 : Fin 1)).comp
            (ContinuousLinearMap.snd ℂ (Fin (s + (k + 1)) → ℂ) (Fin 1 → ℂ))).analyticAt q
        unfold Qcp Q
        apply AnalyticAt.prod
        · rw [analyticAt_pi_iff]; intro j; exact coordFst _
        · rw [analyticAt_pi_iff]; intro a
          refine Fin.lastCases ?_ ?_ a
          · simp only [Fin.snoc_last]; exact coordSnd
          · intro i; simp only [Fin.snoc_castSucc]; exact (coordFst _).mul coordSnd
      have hΘ_an : ∀ q : CParam (s + (k + 1)) 1 × ℂ, AnalyticAt ℂ Θ q := by
        intro q
        rw [hΘ]
        refine AnalyticAt.prod ?_ ?_
        · exact ((idM : CParam s (k + 2) →L[ℂ] CParam s (k + 2)).analyticAt (Qcp q.1)).comp_of_eq
            ((hQcp_an_all q.1).comp_of_eq
              ((ContinuousLinearMap.fst ℂ (CParam (s + (k + 1)) 1) ℂ).analyticAt q) rfl) rfl
        · exact (ContinuousLinearMap.snd ℂ (CParam (s + (k + 1)) 1) ℂ).analyticAt q
      -- (A) finiteness: `t := order Geval ((y,0),ψy) ≤ d` (the `x`-axis line is `τ ↦ τᵈ`)
      have hHty0 : Ht ((y, 0) : CParam s (k + 2)) = (X - C (ψ y)) ^ d := by
        rw [hte ((y, 0) : CParam s (k + 2)) hy_ball]
        exact monic_eq_pow_of_unique_root (hfam.monic _) (hfam.degree_eq _) (fun β => hy_root β)
      have hord_td : analyticOrderAt (fun τ : ℂ => τ ^ d) 0 = (d : ℕ∞) := by
        have han : AnalyticAt ℂ (fun τ : ℂ => τ ^ d) 0 := by fun_prop
        refine han.analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
        filter_upwards with τ; simp
      obtain ⟨t, ht⟩ : ∃ t : ℕ, order ℂ Geval ((y, 0), ψ y) = (t : ℕ∞) := by
        have hxeq : (fun τ : ℂ => Geval (((y, 0), ψ y) + τ • ((0 : CParam s (k + 2)), (1 : ℂ))))
            = fun τ => τ ^ d := by
          funext τ
          have h1 : (((y, 0) : CParam s (k + 2)), ψ y) + τ • ((0 : CParam s (k + 2)), (1 : ℂ))
              = (((y, 0) : CParam s (k + 2)), ψ y + τ) := by
            rw [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero]
          rw [hGeval]
          show (Ht ((((y, 0) : CParam s (k + 2)), ψ y) + τ • ((0 : CParam s (k + 2)), (1 : ℂ))).1).eval
            ((((y, 0) : CParam s (k + 2)), ψ y) + τ • ((0 : CParam s (k + 2)), (1 : ℂ))).2 = τ ^ d
          rw [h1]
          show (Ht ((y, 0) : CParam s (k + 2))).eval (ψ y + τ) = τ ^ d
          rw [hHty0]; simp [Polynomial.eval_pow, add_sub_cancel_left]
        have hle : order ℂ Geval ((y, 0), ψ y) ≤ (d : ℕ∞) := by
          have hlin := order_le_line Geval ((y, 0), ψ y) ((0 : CParam s (k + 2)), (1 : ℂ)) hG_an
          rwa [hxeq, hord_td] at hlin
        exact ⟨_, (ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top d) hle)).symm⟩
      -- (B) the dense transverse direction family `g (w'',a,c,b) = ((a, c • M (snoc w'' 1)), b)`
      set g : (Fin (k + 1) → ℂ) × (Fin s → ℂ) × ℂ × ℂ → CParam s (k + 2) × ℂ :=
        fun q => ((q.2.1, q.2.2.1 • M (Fin.snoc q.1 1)), q.2.2.2) with hgdef
      have hg : ∀ q, AnalyticAt ℂ g q := by
        intro q
        rw [hgdef]
        refine AnalyticAt.prod (AnalyticAt.prod ?_ ?_) ?_
        · exact ((ContinuousLinearMap.fst ℂ (Fin s → ℂ) (ℂ × ℂ)).comp
            (ContinuousLinearMap.snd ℂ (Fin (k + 1) → ℂ) ((Fin s → ℂ) × ℂ × ℂ))).analyticAt q
        · refine AnalyticAt.smul
            (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp ((ContinuousLinearMap.snd ℂ (Fin s → ℂ) (ℂ × ℂ)).comp
              (ContinuousLinearMap.snd ℂ (Fin (k + 1) → ℂ) ((Fin s → ℂ) × ℂ × ℂ)))).analyticAt q) ?_
          refine (M : (Fin (k + 2) → ℂ) →L[ℂ] (Fin (k + 2) → ℂ)).analyticAt _ |>.comp ?_
          rw [analyticAt_pi_iff]; intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.snoc_last]; exact analyticAt_const
          · intro j; simp only [Fin.snoc_castSucc]
            exact ((ContinuousLinearMap.proj j).comp
              (ContinuousLinearMap.fst ℂ (Fin (k + 1) → ℂ) ((Fin s → ℂ) × ℂ × ℂ))).analyticAt q
        · exact ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp ((ContinuousLinearMap.snd ℂ (Fin s → ℂ) (ℂ × ℂ)).comp
            (ContinuousLinearMap.snd ℂ (Fin (k + 1) → ℂ) ((Fin s → ℂ) × ℂ × ℂ)))).analyticAt q
      have hdense : DenseRange g := by
        have hMD : DenseRange (fun cw : ℂ × (Fin (k + 1) → ℂ) => cw.1 • M (Fin.snoc cw.2 1)) := by
          have heq : (fun cw : ℂ × (Fin (k + 1) → ℂ) => cw.1 • M (Fin.snoc cw.2 1))
              = ⇑M ∘ (fun cw : ℂ × (Fin (k + 1) → ℂ) => cw.1 • (Fin.snoc cw.2 1 : Fin (k + 2) → ℂ)) := by
            funext cw; simp [map_smul]
          rw [heq]
          exact (M.surjective.denseRange).comp dense_smul_snoc M.continuous
        rw [Metric.denseRange_iff]
        rintro ⟨⟨a₀, T₀⟩, b₀⟩ r hr
        obtain ⟨⟨c₀, w₀⟩, hcw⟩ := Metric.denseRange_iff.mp hMD T₀ r hr
        refine ⟨(w₀, a₀, c₀, b₀), ?_⟩
        show dist (((a₀, T₀), b₀) : CParam s (k + 2) × ℂ) (g (w₀, a₀, c₀, b₀)) < r
        rw [hgdef]
        have hdd : dist (((a₀, T₀), b₀) : CParam s (k + 2) × ℂ)
              ((a₀, c₀ • M (Fin.snoc w₀ 1)), b₀) = dist T₀ (c₀ • M (Fin.snoc w₀ 1)) := by
          rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, max_eq_right dist_nonneg,
            max_eq_left dist_nonneg]
        rw [hdd]; exact hcw
      -- (C) apply the parametrized order transport: a good ratio point `w''` in `ball ε`
      obtain ⟨⟨w'', a, c, b⟩, hqV, hline_le⟩ := exists_param_line_order_le hG_an ht hg hdense
        (V := Metric.ball (0 : Fin (k + 1) → ℂ) ε ×ˢ (Set.univ : Set ((Fin s → ℂ) × ℂ × ℂ)))
        (Metric.isOpen_ball.prod isOpen_univ) ⟨0, Metric.mem_ball_self hε, Set.mem_univ _⟩
      have hw''ε : ‖w''‖ < ε := by
        have := hqV.1; rwa [Metric.mem_ball, dist_zero_right] at this
      have hyε : ‖y‖ < ε := by rwa [Metric.mem_ball, dist_zero_right] at hy_ε
      -- norm of an `append` (sup metric)
      have hnorm_app : ∀ (v : Fin s → ℂ) (w : Fin (k + 1) → ℂ), ‖v‖ < ε → ‖w‖ < ε →
          ‖Fin.append v w‖ < ε := by
        intro v w hv hw
        have hle_app : ‖Fin.append v w‖ ≤ max ‖v‖ ‖w‖ := by
          rw [pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg v) (le_max_left _ _))]
          intro i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · rw [Fin.append_left]; exact le_trans (norm_le_pi_norm v j) (le_max_left _ _)
          · rw [Fin.append_right]; exact le_trans (norm_le_pi_norm w j) (le_max_right _ _)
        exact lt_of_le_of_lt hle_app (max_lt hv hw)
      have hψ'app : ∀ w : Fin (k + 1) → ℂ, ψ' (Fin.append y w) = ψ y := by
        intro w; simp only [hψ'def]; congr 1; funext i; simp [hfirstₛ, Fin.append_left]
      -- (D) the blown point and the `u`-line direction; the line identity
      set blownPt : CParam (s + (k + 1)) 1 × ℂ :=
        (((Fin.append y w'', (0 : Fin 1 → ℂ)) : CParam (s + (k + 1)) 1), ψ y) with hblownPt
      set dirA : CParam (s + (k + 1)) 1 × ℂ :=
        (((Fin.append a (0 : Fin (k + 1) → ℂ), (fun _ => c : Fin 1 → ℂ)) : CParam (s + (k + 1)) 1), b)
        with hdirA
      have hlineid : (fun τ : ℂ => (Geval ∘ Θ) (blownPt + τ • dirA))
          = (fun τ : ℂ => Geval (((y, 0), ψ y) + τ • g (w'', a, c, b))) := by
        funext τ
        show Geval (Θ (blownPt + τ • dirA)) = Geval (((y, 0), ψ y) + τ • g (w'', a, c, b))
        refine congrArg Geval ?_
        have hbase : (blownPt + τ • dirA).1
            = ((Fin.append (y + τ • a) w'', (fun _ => τ • c)) : CParam (s + (k + 1)) 1) := by
          rw [hblownPt, hdirA]
          refine Prod.ext ?_ ?_
          · funext i
            refine Fin.addCases (fun j => ?_) (fun j => ?_) i
            · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, Fin.append_left]
            · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, Fin.append_right,
                Pi.zero_apply, smul_zero, add_zero]
          · funext i; fin_cases i
            simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
              Pi.smul_apply, Pi.zero_apply, zero_add]
        have hx : (blownPt + τ • dirA).2 = ψ y + τ • b := rfl
        rw [hΘ]
        refine Prod.ext ?_ hx
        show idM (Qcp (blownPt + τ • dirA).1) = (((y, 0), ψ y) + τ • g (w'', a, c, b)).1
        rw [hbase]
        have hQcp1 : Qcp ((Fin.append (y + τ • a) w'', (fun _ => τ • c)) : CParam (s + (k + 1)) 1)
            = ((y + τ • a, (τ • c) • (Fin.snoc w'' 1 : Fin (k + 2) → ℂ)) : CParam s (k + 2)) := by
          show Q ((Fin.append (y + τ • a) w'') ∘ Fin.castAdd (k + 1),
              (Fin.append (y + τ • a) w'') ∘ Fin.natAdd s, ((fun _ => τ • c) : Fin 1 → ℂ) 0)
            = (y + τ • a, (τ • c) • (Fin.snoc w'' 1 : Fin (k + 2) → ℂ))
          rw [Q_apply]
          refine Prod.ext ?_ ?_
          · funext i; simp [Fin.append_left]
          · funext i
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc_last, smul_eq_mul]
            · intro j; simp [Fin.snoc_castSucc, Fin.append_right, smul_eq_mul, mul_comm]
        rw [hQcp1, hidM_apply, hgdef]
        refine Prod.ext rfl ?_
        show M ((τ • c) • (Fin.snoc w'' 1 : Fin (k + 2) → ℂ))
          = (0 : Fin (k + 2) → ℂ) + τ • (c • M (Fin.snoc w'' 1 : Fin (k + 2) → ℂ))
        rw [zero_add, map_smul, smul_smul, smul_eq_mul]
      -- (E) `order_le_line` at the blown point
      have hΘblown : Θ blownPt = ((y, 0), ψ y) := by
        rw [hΘ, hblownPt]
        refine Prod.ext ?_ rfl
        show idM (Qcp ((Fin.append y w'', (0 : Fin 1 → ℂ)) : CParam (s + (k + 1)) 1))
          = ((y, 0) : CParam s (k + 2))
        rw [hQcpsec (Fin.append y w''),
          show firstₛ (Fin.append y w'') = y by funext i; simp [hfirstₛ, Fin.append_left], hg'_sec]
      have hGΘblown_an : AnalyticAt ℂ (Geval ∘ Θ) blownPt :=
        hG_an.comp_of_eq (hΘ_an blownPt) hΘblown
      have hblown_le : order ℂ (Geval ∘ Θ) blownPt ≤ (t : ℕ∞) := by
        calc order ℂ (Geval ∘ Θ) blownPt
            ≤ analyticOrderAt (fun τ : ℂ => (Geval ∘ Θ) (blownPt + τ • dirA)) 0 :=
              order_le_line _ blownPt dirA hGΘblown_an
          _ = analyticOrderAt (fun τ : ℂ => Geval (((y, 0), ψ y) + τ • g (w'', a, c, b))) 0 := by
              rw [hlineid]
          _ ≤ (t : ℕ∞) := hline_le
      -- (F) `e1` transport: `order(GΘ)(p) = order(GΘ)(blownPt)` (both on the blown graph)
      have hpb : order ℂ (Geval ∘ Θ) p = order ℂ (Geval ∘ Θ) blownPt := by
        rw [← haΘ]
        have hp_const : order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ =>
              (weierstrassPoly d a' wt.1).eval wt.2) p
            = order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
                (((0, 0) : CParam (s + (k + 1)) 1), ψ' 0) := by
          have h := hball (show dist (Fin.append y (0 : Fin (k + 1) → ℂ)) 0 < ε by
            rw [dist_zero_right]; exact hnorm_app y 0 hyε (by simpa using hε))
          rw [hψ'app] at h
          rw [hp]; exact h
        have hb_const : order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ =>
              (weierstrassPoly d a' wt.1).eval wt.2) blownPt
            = order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
                (((0, 0) : CParam (s + (k + 1)) 1), ψ' 0) := by
          have h := hball (show dist (Fin.append y w'') 0 < ε by
            rw [dist_zero_right]; exact hnorm_app y w'' hyε hw''ε)
          rw [hψ'app] at h
          rw [hblownPt]; exact h
        rw [hp_const, hb_const]
      rw [ht, hpb]; exact hblown_le
  -- assemble: `order (fac-eval) (y) = order (a'-eval) (blown y) = C = order (fac-eval) (0)`
  have htr0 : order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2)
        (((0, 0) : CParam s (k + 2)), ψ 0)
      = order ℂ (fun wt : CParam (s + (k + 1)) 1 × ℂ => (weierstrassPoly d a' wt.1).eval wt.2)
        (((0, 0) : CParam (s + (k + 1)) 1), ψ 0) := by
    have h := htransport.self_of_nhds
    rwa [hemb0] at h
  filter_upwards [htransport, hblown] with y hy_tr hy_bl
  rw [hy_tr, hy_bl, ← htr0]

end Puiseux
