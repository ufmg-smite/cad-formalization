import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiE2
import Cad.Multivariate.ProjectionTheorem.Generalized.TransverseShear
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiNonsplittingE1
import Cad.Multivariate.ProjectionTheorem.Generalized.FamilyGlobalize
import Cad.Multivariate.ProjectionTheorem.Generalized.A5Coincidence

/-!
# M5b — discharging the `e ≥ 2` blow-up axiom

Assembles the blow-up reduction: globalize `H`, apply a transverse automorphism `M` (so the blow-up
direction is generic), run the normal form on `disc`, obtain `N(0) ≠ 0` from the genericity, build the
codimension-one family `h' = (H ∘ (id × M)) ∘ Q`, transport its discriminant-order facts, invoke the
axiom-free `zariski_nonsplitting_e1`, and push down to `H (y, 0)`.
-/

noncomputable section

open Polynomial Filter BlowupNormalForm ZariskiE2 CoordTranslate BlowupMap
open scoped Topology

namespace ZariskiE2

variable {s e : ℕ}

/-- The blow-up's special direction `Fin.snoc 0 1` is the last coordinate basis vector. -/
lemma snoc_zero_one_eq_single {m : ℕ} :
    (Fin.snoc (0 : Fin m → ℂ) (1 : ℂ) : Fin (m + 1) → ℂ) = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last, Pi.single_eq_same]
  · intro j
    rw [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne, Pi.zero_apply]

/-- Pointwise discriminant analyticity at an arbitrary base point (via translation to `0`). -/
lemma familyDiscr_analyticAt_pt (H : CParam s e → Polynomial ℂ) (d : ℕ) (hd : 0 < d)
    (hmonic : ∀ w, (H w).Monic) (hdeg : ∀ w, (H w).natDegree = d) (p : CParam s e)
    (hc : ∀ i, AnalyticAt ℂ (fun w => (H w).coeff i) p) :
    AnalyticAt ℂ (fun w => (H w).discr) p := by
  set H' : CParam s e → Polynomial ℂ := fun w => H (w + p) with hH'
  have hc' : ∀ i, AnalyticAt ℂ (fun w => (H' w).coeff i) 0 := fun i =>
    (hc i).comp_of_eq (by fun_prop) (by simp)
  have hdisc' : AnalyticAt ℂ (fun w => (H' w).discr) 0 :=
    familyDiscr_analyticAt H' d hd (fun w => hmonic _) (fun w => hdeg _) hc'
  have hshift : AnalyticAt ℂ (fun w : CParam s e => w - p) p := by fun_prop
  have hshift0 : (fun w : CParam s e => w - p) p = 0 := by simp
  have hcomp := hdisc'.comp_of_eq hshift hshift0
  have heq : (fun w => (H' w).discr) ∘ (fun w : CParam s e => w - p) = fun w => (H w).discr := by
    funext w; show (H' (w - p)).discr = (H w).discr; rw [hH']; congr 2; abel_nf
  rwa [heq] at hcomp

/-- A monic family of constant degree `d` is the Weierstrass polynomial of its low coefficients. -/
lemma weierstrassPoly_recon (P : CParam s e → Polynomial ℂ) (d : ℕ)
    (hmonic : ∀ w, (P w).Monic) (hdeg : ∀ w, (P w).natDegree = d) (w : CParam s e) :
    weierstrassPoly d (fun (i : Fin d) (w : CParam s e) => (P w).coeff (i : ℕ)) w = P w := by
  ext j
  rw [weierstrassPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff]
  rcases lt_trichotomy j d with hjd | hjd | hjd
  · rw [if_neg (by omega), zero_add,
      Finset.sum_eq_single (⟨j, hjd⟩ : Fin d)
        (fun b _ hb => by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hb (Fin.ext h.symm)),
            mul_zero])
        (fun h => absurd (Finset.mem_univ _) h),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · subst hjd
    rw [if_pos rfl, Finset.sum_eq_zero (fun b _ => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by have := b.isLt; omega),
          mul_zero]), add_zero]
    have hm := (hmonic w).coeff_natDegree; rw [hdeg w] at hm; exact hm.symm
  · rw [if_neg (by omega), Finset.sum_eq_zero (fun b _ => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by have := b.isLt; omega),
          mul_zero]), add_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg w]; omega)]

/-- **The `e ≥ 2` blow-up case of `irreducible_section_single_root_deg`, PROVED.** -/
theorem irreducible_section_single_root_blowup_proof {s k : ℕ}
    (H : CParam s (k + 2) → Polynomial ℂ) (d : ℕ) (hd : 2 ≤ d)
    (hH_fam : IsWeierstrassFamily H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s (k + 2)) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s (k + 2))
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s (k + 2))) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (H ((y, 0) : CParam s (k + 2))).IsRoot β ↔ β = α := by
  classical
  -- `r := ord₀(disc H)`, finite, and the section order is `≥ r`
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hHdisc_ne
  have hr' : order ℂ (fun w => (H w).discr) (0 : CParam s (k + 2)) = (r : ℕ∞) := hr.symm
  -- `r ≥ 1` since `disc(H 0) = disc(Xᵈ) = 0`
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h; swap; · exact h
    exfalso
    have hd0 : (fun w => (H w).discr) (0 : CParam s (k + 2)) = 0 := by
      show (H 0).discr = 0; rw [hH_fam.eval_zero]; exact discr_X_pow_eq_zero hd
    have := order_ne_zero_of_eq_zero (fun w => (H w).discr) 0 hd0
    rw [hr', h0] at this; exact this rfl
  -- globalize `H` to `Ht` (disc analytic on a ball)
  obtain ⟨Ht, ρ, hρ, htm, htd, _htc, hte, hta⟩ :=
    FamilyGlobalize.exists_globalized_family (q := H) hH_fam.monic hH_fam.degree_eq
      hH_fam.coeff_analyticAt
  set g : CParam s (k + 2) → ℂ := fun w => (Ht w).discr with hg
  -- `g = disc H` near `0` (since `Ht = H` on the ball)
  have hgH : g =ᶠ[𝓝 (0 : CParam s (k + 2))] fun w => (H w).discr := by
    have hball : Metric.ball (0 : CParam s (k + 2)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
    filter_upwards [hball] with w hw
    show (Ht w).discr = (H w).discr
    rw [hte w hw]
  -- `g` is analytic on the ball
  have hg_ball : ∀ p ∈ Metric.ball (0 : CParam s (k + 2)) ρ, AnalyticAt ℂ g p := fun p hp =>
    familyDiscr_analyticAt_pt Ht d (by omega) htm htd p (fun i => hta i p hp)
  have hg0 : AnalyticAt ℂ g 0 := hg_ball 0 (Metric.mem_ball_self hρ)
  -- analyticity of `g` at section points near `0`
  have hsec_tendsto : Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s (k + 2))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s (k + 2))) := by fun_prop
    simpa using hc.tendsto' 0 0 (by simp)
  have hg_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g ((y, 0) : CParam s (k + 2)) := by
    filter_upwards [hsec_tendsto.eventually (Metric.ball_mem_nhds 0 hρ)] with y hy
    exact hg_ball _ hy
  -- order of `g` along the section equals `r`
  have horder_g : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ g ((y, 0) : CParam s (k + 2)) = (r : ℕ∞) := by
    filter_upwards [hHdisc_oi, hsec_tendsto.eventually hgH.eventually_nhds]
      with y hy_oi hy_germ
    have h1 : order ℂ g ((y, 0) : CParam s (k + 2))
        = order ℂ (fun w => (H w).discr) ((y, 0) : CParam s (k + 2)) :=
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
  -- the transverse automorphism `M` (so `e_last ↦ ξ`) and `idM := id × M`
  obtain ⟨M, hM⟩ := TransverseShear.exists_transverseCLE ξ hξ_ne
  set idM : CParam s (k + 2) ≃L[ℂ] CParam s (k + 2) :=
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (Fin s → ℂ)) M with hidM
  have hidM_apply : ∀ p : CParam s (k + 2), idM p = (p.1, M p.2) := fun p => rfl
  have hidM0 : idM 0 = 0 := map_zero _
  -- `g' = disc(Ht ∘ idM) = g ∘ idM`
  set g' : CParam s (k + 2) → ℂ := fun w => g (idM w) with hg'
  have hidM_an : AnalyticAt ℂ (fun w : CParam s (k + 2) => idM w) 0 :=
    (idM : CParam s (k + 2) →L[ℂ] CParam s (k + 2)).analyticAt 0
  have hg'0 : AnalyticAt ℂ g' 0 := hg0.comp_of_eq hidM_an hidM0
  -- `g'` agrees with `g` on the section, so its order/jets along the section match
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
  -- `B` is analytic (a polynomial map composed with the coordinate equivalence)
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
  -- the normal form `g' ∘ B = (z 0)ʳ · N`
  obtain ⟨N, hN_an, hfact⟩ := normalForm g' r hg'B_an hg'_at hord_g'
  -- `idM (ξOf 0) = (0, ξ)` (the blow-up direction is the good transverse direction)
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
  -- `N 0 ≠ 0`
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
  -- the codimension-one family `h' = (Ht ∘ idM) ∘ Qcp`, as a `weierstrassPoly`
  set Ht'' : CParam s (k + 2) → Polynomial ℂ := fun w => Ht (idM w) with hHt''
  have hHt''_monic : ∀ w, (Ht'' w).Monic := fun w => htm _
  have hHt''_deg : ∀ w, (Ht'' w).natDegree = d := fun w => htd _
  set a' : Fin d → (CParam (s + (k + 1)) 1 → ℂ) :=
    fun i W => (Ht'' (Qcp W)).coeff (i : ℕ) with ha'
  -- `weierstrassPoly d a' W = Ht'' (Qcp W)`
  have hwp : ∀ W, weierstrassPoly d a' W = Ht'' (Qcp W) := fun W =>
    weierstrassPoly_recon (fun W => Ht'' (Qcp W)) d (fun W => hHt''_monic _)
      (fun W => hHt''_deg _) W
  -- `weierstrassDiscFn d a' = g' ∘ Qcp`
  have hWD : ∀ W, weierstrassDiscFn d a' W = g' (Qcp W) := by
    intro W
    show (weierstrassPoly d a' W).discr = g (idM (Qcp W))
    rw [hwp]
  -- `Qcp` is analytic at `0`
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
  -- `a' i` analytic at `0`, vanishing at `0`
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
    rw [hidM0, hte 0 (Metric.mem_ball_self hρ), hH_fam.eval_zero, Polynomial.coeff_X_pow,
      if_neg (by have := i.isLt; omega)]
  -- transport the section order facts through `Φ' = cparamEquiv (s+(k+1))`
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
  -- apply the axiom-free codimension-one nonsplitting
  have hns := zariski_nonsplitting_e1 d (by omega) a' ha_an ha0 hdisc_ne' hdisc'
  -- push down to `H (y, 0)`
  have hemb_tendsto : Tendsto (fun y : Fin s → ℂ => Fin.append y (0 : Fin (k + 1) → ℂ))
      (𝓝 0) (𝓝 (0 : Fin (s + (k + 1)) → ℂ)) := by
    have hc : Continuous (fun y : Fin s → ℂ => Fin.append y (0 : Fin (k + 1) → ℂ)) := by
      apply continuous_pi; intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]; exact continuous_apply j
      · simp only [Fin.append_right]; exact continuous_const
    have h0 : Fin.append (0 : Fin s → ℂ) (0 : Fin (k + 1) → ℂ) = 0 := by
      funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    simpa [h0] using hc.tendsto 0
  filter_upwards [hemb_tendsto.eventually hns,
    hsec_tendsto.eventually (Metric.ball_mem_nhds 0 hρ)] with y hy_root hy_mem
  -- `weierstrassPoly d a' (append y 0, 0) = H (y, 0)`
  have hQcp_sec : Qcp ((Fin.append y (0 : Fin (k + 1) → ℂ), 0) : CParam (s + (k + 1)) 1)
      = ((y, 0) : CParam s (k + 2)) := by
    show Q (Fin.append y (0 : Fin (k + 1) → ℂ) ∘ Fin.castAdd (k + 1),
        Fin.append y (0 : Fin (k + 1) → ℂ) ∘ Fin.natAdd s, (0 : Fin 1 → ℂ) 0)
      = ((y, 0) : CParam s (k + 2))
    rw [Q_apply]
    refine Prod.ext ?_ ?_
    · funext i; simp [Fin.append_left]
    · funext i; refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc]
  have hpoly : weierstrassPoly d a' ((Fin.append y (0 : Fin (k + 1) → ℂ), 0)
      : CParam (s + (k + 1)) 1) = H ((y, 0) : CParam s (k + 2)) := by
    rw [hwp, hQcp_sec]
    show Ht (idM ((y, 0) : CParam s (k + 2))) = H ((y, 0) : CParam s (k + 2))
    rw [hg'_sec y]
    exact hte ((y, 0) : CParam s (k + 2)) hy_mem
  rw [← hpoly]
  exact hy_root

end ZariskiE2
