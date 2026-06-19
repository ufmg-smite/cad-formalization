import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiShareRoot
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiCodim1
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiFactorization
import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiE1

/-!
# Reducible nonsplitting at codimension one, free of the `e ≥ 2` axiom

`zariski_nonsplitting` (the reducible single-root theorem) routes its per-irreducible-factor step
through `irreducible_section_single_root_deg`, which at `e ≥ 2` invokes the temporary axiom
`irreducible_section_single_root_blowup`. The M5b blow-up reduction needs the reducible single-root
result **at codimension one** to feed `h' = H ∘ Q`, and must not depend on the `e ≥ 2` axiom (that would
be circular). Here we re-state the gluing chain (A4 → common → nonsplitting) **parametrized over the
per-factor single-root** (`hfactor`), reusing the axiom-free pieces (A5 resultant coincidence, the
disc-descent, the final assembly), and instantiate at `e = 1` with the proved
`irreducible_section_single_root_e1`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **Single-family codimension-one nonsplitting (axiom-free).** For an irreducible Weierstrass family
over `CParam s 1` of degree `d ≥ 1` with finite, section-constant discriminant order, the section
polynomial has a single distinct root. The `d = 1` case is trivial; `d ≥ 2` is the proved
`irreducible_section_single_root_e1` (which does **not** go through `irreducible_section_single_root_deg`,
so this is free of the `e ≥ 2` blow-up axiom). -/
theorem single_root_codim1 {s : ℕ}
    (H : CParam s 1 → Polynomial ℂ) (d : ℕ) (hd : 1 ≤ d)
    (hH_fam : IsWeierstrassFamily H d) (hH_irr : WeierstrassIrreducible H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s 1) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s 1)
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s 1)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (H ((y, 0) : CParam s 1)).IsRoot β ↔ β = α := by
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have hd1' : d = 1 := le_antisymm (by omega) hd
    refine Filter.Eventually.of_forall fun y => ?_
    set p := H ((y, 0) : CParam s 1) with hp
    have hmonic : p.Monic := hH_fam.monic _
    have hdeg : p.natDegree = 1 := by rw [hp, hH_fam.degree_eq, hd1']
    have hlc : p.coeff 1 = 1 := by have := hmonic.coeff_natDegree; rwa [hdeg] at this
    refine ⟨-p.coeff 0, fun β => ?_⟩
    have heval : p.eval β = β + p.coeff 0 := by
      rw [eval_eq_sum_range' (n := 2) (by rw [hdeg]; omega),
        Finset.sum_range_succ, Finset.sum_range_one, hlc]; ring
    rw [Polynomial.IsRoot.def, heval, add_eq_zero_iff_eq_neg]
  · exact irreducible_section_single_root_e1 H d hd2 hH_fam hH_irr hHdisc_ne hHdisc_oi

/-- **A4 parametrized over the per-factor single-root** (`hfactor`). Identical to
`irreducible_factor_section_single_root` except the per-factor single-root is supplied as a hypothesis
rather than via `irreducible_section_single_root`. -/
theorem irreducible_factor_section_single_root_of {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hk : 0 < k) (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_irr : ∀ j, WeierstrassIrreducible (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j : Fin k, fac j w)
    (hfactor : ∀ j : Fin k,
      order ℂ (fun w => (fac j w).discr) (0 : CParam s e) ≠ ⊤ →
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
          = order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e)) →
      ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        ∃ α : ℂ, ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β ↔ β = α) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j : Fin k, ∃ α : ℂ, ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β ↔ β = α := by
  rw [Filter.eventually_all]
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
        filter_upwards [hfac_eq] with w hw
        rw [hw, hj0, Fin.prod_univ_one]
      have hgerm_base : order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e)
          = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s e) :=
        order_congr_of_eventuallyEq' (by
          filter_upwards [hfe] with w hw
          show (fac j w).discr = (weierstrassPoly m a w).discr
          rw [hw])
      refine ⟨?_, ?_⟩
      · rw [show ((0 : CParam s e)) = ((0, 0) : CParam s e) from rfl, hgerm_base]; exact hdisc_ne
      · have hfe_nhds := hfe.eventually_nhds
        have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
          simpa using hc.tendsto' 0 0 (by simp)
        have hsec_germ : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
            ∀ᶠ w' in 𝓝 ((y, 0) : CParam s e), weierstrassPoly m a w' = fac j w' :=
          hι.eventually hfe_nhds
        filter_upwards [hdisc, hsec_germ] with y hy_disc hy_germ
        have e1 : order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
            = order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e) :=
          order_congr_of_eventuallyEq' (by
            filter_upwards [hy_germ] with w' hw'
            show (fac j w').discr = (weierstrassPoly m a w').discr
            rw [hw'])
        rw [e1, hy_disc]; exact hgerm_base.symm
    · exact factor_disc_order_inv m a hdisc_ne hdisc k deg fac hfac_fam
        (fun l => (hfac_irr l).1) hfac_eq j hk2
  exact hfactor j hDj.1 hDj.2

/-- **Common single section root parametrized over `hfactor`.** -/
theorem irreducible_factors_common_section_root_of {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hk : 0 < k) (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_irr : ∀ j, WeierstrassIrreducible (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j : Fin k, fac j w)
    (hfactor : ∀ j : Fin k,
      order ℂ (fun w => (fac j w).discr) (0 : CParam s e) ≠ ⊤ →
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
          = order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e)) →
      ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        ∃ α : ℂ, ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β ↔ β = α) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ j : Fin k, ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β ↔ β = α := by
  filter_upwards
    [irreducible_factor_section_single_root_of m a hdisc_ne hdisc k deg fac hk hfac_fam
      hfac_irr hfac_eq hfactor,
     irreducible_factors_section_share_root m a hdisc_ne hdisc k deg fac hfac_fam
      hfac_irr hfac_eq] with y h4 h5
  obtain ⟨α₀, hα₀⟩ := h4 ⟨0, hk⟩
  refine ⟨α₀, fun j => ?_⟩
  obtain ⟨αj, hαj⟩ := h4 j
  obtain ⟨γ, hγj, hγ0⟩ := h5 j ⟨0, hk⟩
  have hαj_eq : αj = α₀ := ((hαj γ).mp hγj).symm.trans ((hα₀ γ).mp hγ0)
  rw [← hαj_eq]
  exact hαj

/-- **Reducible nonsplitting at codimension one, free of the `e ≥ 2` axiom.** Same statement as
`zariski_nonsplitting` for `e = 1`, but proved through `single_root_codim1` (hence `e1`) rather than
`irreducible_section_single_root_deg`. -/
theorem zariski_nonsplitting_e1 {s : ℕ}
    (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s 1 → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s 1) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s 1)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s 1)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (weierstrassPoly m a ((y, 0) : CParam s 1)).IsRoot β ↔ β = α := by
  have hH : IsWeierstrassFamily (weierstrassPoly m a) m :=
    weierstrassPoly_isWeierstrassFamily m a ha_an ha0
  obtain ⟨k, deg, fac, hk, _hdeg1, hfac_fam, hfac_irr, hfac_eq⟩ :=
    weierstrass_irreducible_factorization (weierstrassPoly m a) m hH hm_pos
  have hcommon := irreducible_factors_common_section_root_of m a hdisc_ne hdisc
    k deg fac hk hfac_fam hfac_irr hfac_eq
    (fun j hne hoi => single_root_codim1 (fac j) (deg j) (hfac_irr j).1 (hfac_fam j) (hfac_irr j)
      hne hoi)
  have hsec : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s 1)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s 1)) := by fun_prop
    simpa using hcont.tendsto 0
  apply nonsplitting_of_common_single_root m a
  filter_upwards [hsec.eventually hfac_eq, hcommon] with y hy_eq hy_common
  obtain ⟨α, hα⟩ := hy_common
  exact ⟨k, fun j => fac j ((y, 0) : CParam s 1), α, hk, hy_eq, hα⟩
