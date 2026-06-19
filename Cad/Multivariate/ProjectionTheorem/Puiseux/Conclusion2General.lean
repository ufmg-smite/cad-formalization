import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2Factor
import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2E2

/-!
# Conclusion 2 — general codimension `e`, assembled from the per-`e` cases

This file assembles the full general-`e` order-invariance (`order_invariant_in_graph`) from the per-factor
dispatcher `order_eval_constant_factor`, which handles `e = 0` (`order_eval_value_e0`), `e = 1`
(`order_eval_value_e1_weierstrass`), and `e ≥ 2` via `order_eval_value_e2_blowup` (the order-under-blow-up
reduction), now a THEOREM proved in `Conclusion2E2.lean` (thesis stage-8 term-tracking). All three cases
are axiom-clean, so `order_invariant_in_graph` — and hence `mccallum_3_2_3_generalized` — is fully
axiom-free.
-/

noncomputable section

open Polynomial Filter Metric Set
open scoped Topology

namespace Puiseux

/-- **The `e ≥ 2` order-under-blow-up reduction, PROVED** (no longer an axiom). The exact analogue of
`order_eval_value_e1_weierstrass` for codimension `k + 2`: for an irreducible Weierstrass family over
`CParam s (k+2)` of degree `d ≥ 2` with finite, section-constant discriminant order and single section
root `ψ`, the evaluation order is constant along the section. Discharged by the quadratic blow-up to
codimension one (`Conclusion2E2.order_eval_value_e2_blowup_proof`, thesis stage-8 term-tracking). -/
theorem order_eval_value_e2_blowup {s k : ℕ} (fac : CParam s (k + 2) → Polynomial ℂ) (d : ℕ) (hd : 2 ≤ d)
    (hfam : IsWeierstrassFamily fac d)
    (hdisc_ne : order ℂ (fun w => (fac w).discr) (0 : CParam s (k + 2)) ≠ ⊤)
    (hdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (fac w).discr) ((y, 0) : CParam s (k + 2))
        = order ℂ (fun w => (fac w).discr) ((0, 0) : CParam s (k + 2)))
    (ψ : (Fin s → ℂ) → ℂ) (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (fac ((y, 0) : CParam s (k + 2))).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s (k + 2)), ψ y)
        = order ℂ (fun wt : CParam s (k + 2) × ℂ => (fac wt.1).eval wt.2)
            (((0, 0) : CParam s (k + 2)), ψ 0) :=
  order_eval_value_e2_blowup_proof fac d hd hfam hdisc_ne hdisc_oi ψ hψ_an hψ_root

/-- **Per-factor order constancy (general codimension `e`).** Dispatches `d = 1` (`order_eval_deg1`) and
`d ≥ 2` on the codimension `e` (`order_eval_value_e0` / `order_eval_value_e1_weierstrass` /
`order_eval_value_e2_blowup`). -/
theorem order_eval_constant_factor {s e : ℕ} {fac : CParam s e → Polynomial ℂ} {d : ℕ} (hd : 1 ≤ d)
    (hfam : IsWeierstrassFamily fac d) (hirr : WeierstrassIrreducible fac d)
    (hdisc_ne : order ℂ (fun w => (fac w).discr) (0 : CParam s e) ≠ ⊤)
    (hdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (fac w).discr) ((y, 0) : CParam s e)
        = order ℂ (fun w => (fac w).discr) ((0, 0) : CParam s e))
    {ψ : (Fin s → ℂ) → ℂ} (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (fac ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s e), ψ y)
        = order ℂ (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2) (((0, 0) : CParam s e), ψ 0) := by
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have hd1' : d = 1 := by omega
    have h1 : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s e), ψ y) = 1 := by
      filter_upwards [hψ_root, eval_analyticAt_section_eventually hfam ψ] with y hsy han
      refine order_eval_deg1 (hfam.monic _) (by rw [hfam.degree_eq]; exact hd1') ?_ han
      exact Polynomial.IsRoot.def.mp ((hsy (ψ y)).mpr rfl)
    filter_upwards [h1] with y hy; rw [hy, h1.self_of_nhds]
  · match e, fac, hfam, hirr, hdisc_ne, hdisc_oi, hψ_root with
    | 0, fac, hfam, _, hdisc_ne, hdisc_oi, _ =>
        exact order_eval_value_e0 hd2 hfam hdisc_ne hdisc_oi ψ
    | 1, fac, hfam, hirr, hdisc_ne, hdisc_oi, hψ_root =>
        exact order_eval_value_e1_weierstrass fac d hd2 hfam hirr hdisc_ne hdisc_oi ψ hψ_an hψ_root
    | (k + 2), fac, hfam, hirr, hdisc_ne, hdisc_oi, hψ_root =>
        exact order_eval_value_e2_blowup fac d hd2 hfam hdisc_ne hdisc_oi ψ hψ_an hψ_root

/-- **Zariski 4.1.1 Conclusion (2) — order-invariance in the graph, general codimension `e`.** The
full axiom-shaped statement, discharged modulo the single `e ≥ 2` blow-up axiom
`order_eval_value_e2_blowup`. Same factorization assembly as `order_invariant_in_graph_e1`, but the
per-factor constancy now goes through the general-`e` dispatcher `order_eval_constant_factor`. -/
theorem order_invariant_in_graph {s e : ℕ} (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (ψ : (Fin s → ℂ) → ℂ) (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
          (((y, 0) : CParam s e), ψ y)
        = order ℂ (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
          (((0, 0) : CParam s e), ψ 0) := by
  obtain ⟨k, deg, fac, hk, hdeg1, hfac_fam, hfac_irr, hfac_eq⟩ :=
    weierstrass_irreducible_factorization (weierstrassPoly m a) m
      (weierstrassPoly_isWeierstrassFamily m a ha_an ha0) hm_pos
  refine order_eval_constant_of_factors hfac_eq
    (fun j => eval_analyticAt_section_eventually (hfac_fam j) ψ) ?_
  intro j
  have hDj : order ℂ (fun w => (fac j w).discr) (0 : CParam s e) ≠ ⊤ ∧
      ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
          = order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e) := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hk1' : k = 1 := by omega
      subst hk1'
      have hj0 : j = 0 := Subsingleton.elim j 0
      have hfe : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = fac j w := by
        filter_upwards [hfac_eq] with w hw; rw [hw, hj0, Fin.prod_univ_one]
      have hgerm_base : order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e)
          = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s e) :=
        order_congr_of_eventuallyEq' (by
          filter_upwards [hfe] with w hw
          show (fac j w).discr = (weierstrassPoly m a w).discr; rw [hw])
      refine ⟨?_, ?_⟩
      · rw [show ((0 : CParam s e)) = ((0, 0) : CParam s e) from rfl, hgerm_base]; exact hdisc_ne
      · have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
          simpa using hc.tendsto' 0 0 (by simp)
        have hsec_germ : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
            ∀ᶠ w' in 𝓝 ((y, 0) : CParam s e), weierstrassPoly m a w' = fac j w' :=
          hι.eventually hfe.eventually_nhds
        filter_upwards [hdisc, hsec_germ] with y hy_disc hy_germ
        have e1 : order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
            = order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e) :=
          order_congr_of_eventuallyEq' (by
            filter_upwards [hy_germ] with w' hw'
            show (fac j w').discr = (weierstrassPoly m a w').discr; rw [hw'])
        rw [e1, hy_disc]; exact hgerm_base.symm
    · exact factor_disc_order_inv m a hdisc_ne hdisc k deg fac hfac_fam hdeg1 hfac_eq j hk2
  exact order_eval_constant_factor (hdeg1 j) (hfac_fam j) (hfac_irr j) hDj.1 hDj.2 hψ_an
    (factor_single_root_of_prod m a hdeg1 hfac_fam hfac_eq hψ_root j)

end Puiseux
