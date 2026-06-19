import Cad.Multivariate.ProjectionTheorem.Generalized.MultiCluster
import Cad.Multivariate.ProjectionTheorem.Generalized.OrderFullBridge

/-!
# Analytic pseudopolynomial delineability + codim order-invariance — proved from the Zariski axioms

`analytic_pseudopoly_delineable'` is the delineation result, a **theorem** (no longer the
`analytic_pseudopoly_delineable_nonsep` axiom): the separable case via the analytic IFT
(`separable_family_locally_delineable`), the non-separable case via `multi_cluster_real_delineation`
(Weierstrass + Zariski). It additionally carries the **per-branch section order-invariance**
conjunct (separable case: order `≡ 1` at simple roots via `order_section_eq_one_of_simple`;
non-separable: threaded from `multi_cluster_real_delineation`).

`lifting_generalized_codim_local` then **proves** the section-graph order-invariance that was
formerly the temporary axiom `codim_section_order_invariant`: an arbitrary continuous root function
`θ` tracks a single delineation branch `η i₀` across the preconnected `S ∩ U` (a connectivity
argument on the locally-constant branch index), and `orderFull_eq_order_section_chart` (L_bridge)
transports the threaded order-invariance to `orderFull f a (θ a)`. With this, the whole
Weierstrass–Zariski transport is complete and the main theorem depends only on the two genuine
Zariski-equisingularity axioms (`zariski_single_branch`, `zariski_order_invariant_in_graph`).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **Local delineability of a real-analytic pseudopolynomial family**, proved from `{C, E, A2}`. -/
theorem analytic_pseudopoly_delineable'
    (Ng : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (hg_deg_bound : ∀ w, (g w).natDegree ≤ Ng)
    (hg_coeff_an : ∀ i : ℕ, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    (hg_pos : 0 < (g 0).natDegree)
    (hg_deg : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree)
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hP_an : AnalyticAt ℝ P 0) (hP_ne : order ℝ P 0 ≠ ⊤)
    (NA NB : ℕ) (A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hA_deg : ∀ w, (A w).natDegree ≤ NA) (hB_deg : ∀ w, (B w).natDegree ≤ NB)
    (hA_coeff : ∀ i, AnalyticAt ℝ (fun w => (A w).coeff i) 0)
    (hB_coeff : ∀ i, AnalyticAt ℝ (fun w => (B w).coeff i) 0)
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w))
    (hP_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0) :
    ∃ (V : Set (Fin s → ℝ)), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧
      ∃ (k : ℕ) (η : Fin k → (Fin s → ℝ) → ℝ) (mult : Fin k → ℕ),
        (∀ i, AnalyticOn ℝ (η i) V) ∧
        (∀ y ∈ V, ∀ i j : Fin k, i < j → η i y < η j y) ∧
        (∀ y ∈ V, ∀ α : ℝ, (g (y, 0)).IsRoot α ↔ ∃ i : Fin k, α = η i y) ∧
        (∀ i, 0 < mult i) ∧
        (∀ y ∈ V, ∀ i, (g (y, 0)).rootMultiplicity (η i y) = mult i) ∧
        (∀ i : Fin k, ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
          order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2) ((y, 0), η i y)
            = order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
                ((0, 0), η i 0)) := by
  by_cases hsep : (g 0).Separable
  · -- Separable case: every branch is a *simple* root, so the section order is `≡ 1` (constant).
    have hcoeff' : ∀ i, AnalyticAt ℝ (fun y => (g (y, 0)).coeff i) 0 := fun i =>
      (hg_coeff_an i).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    obtain ⟨V, hVopen, hV0, k, η, mult, hη_an, hη_ord, hη_roots, hmult_pos, hmult_const⟩ :=
      separable_family_locally_delineable (fun y => g (y, 0)) 0 hg_deg hg_pos hcoeff' hsep
    refine ⟨V, hVopen, hV0, k, η, mult, hη_an, hη_ord, hη_roots, hmult_pos, hmult_const, ?_⟩
    have hg0_ne : g 0 ≠ 0 := hsep.ne_zero
    have hV_mem : V ∈ 𝓝 (0 : Fin s → ℝ) := hVopen.mem_nhds hV0
    -- separability ⟹ every branch multiplicity is `1`
    have hmult_one : ∀ i, mult i = 1 := by
      intro i
      have hroot0 : (g 0).IsRoot (η i 0) := (hη_roots 0 hV0 (η i 0)).mpr ⟨i, rfl⟩
      have h1 : (g 0).rootMultiplicity (η i 0) = mult i := hmult_const 0 hV0 i
      have hle := Polynomial.rootMultiplicity_le_one_of_separable hsep (η i 0)
      have hpos := (Polynomial.rootMultiplicity_pos hg0_ne).mpr hroot0
      omega
    -- coefficients of `g` are analytic at `(y, 0)` for `y` near `0`
    have hι : Filter.Tendsto (fun y : Fin s → ℝ => ((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)))
        (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun y : Fin s → ℝ => ((y, 0) : (Fin s → ℝ) × (Fin e → ℝ))) := by
        fun_prop
      simpa using hcont.tendsto 0
    have hcoeff_ev : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
        ∀ j, AnalyticAt ℝ (fun w => (g w).coeff j) (y, 0) := by
      have hfin : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ j ∈ Finset.range (Ng + 1),
          AnalyticAt ℝ (fun w => (g w).coeff j) (y, 0) := by
        rw [Finset.eventually_all]
        intro j _
        exact hι.eventually (hg_coeff_an j).eventually_analyticAt
      filter_upwards [hfin] with y hy j
      by_cases hj : j ≤ Ng
      · exact hy j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      · push_neg at hj
        have hzero : (fun w : (Fin s → ℝ) × (Fin e → ℝ) => (g w).coeff j) = fun _ => 0 := by
          funext w
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hg_deg_bound w) hj)
        rw [hzero]; exact analyticAt_const
    -- per branch: section order is `1` at both endpoints, hence constant
    intro i
    have hval0 : order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
        ((0, 0), η i 0) = 1 := by
      apply order_section_eq_one_of_simple g Ng hg_deg_bound (0, 0) (η i 0) hg_coeff_an
      · exact (hη_roots 0 hV0 (η i 0)).mpr ⟨i, rfl⟩
      · intro hd
        have hroot0 : (g 0).IsRoot (η i 0) := (hη_roots 0 hV0 (η i 0)).mpr ⟨i, rfl⟩
        have h1lt : 1 < (g 0).rootMultiplicity (η i 0) :=
          (Polynomial.one_lt_rootMultiplicity_iff_isRoot hg0_ne).mpr ⟨hroot0, hd⟩
        have h1 : (g 0).rootMultiplicity (η i 0) = mult i := hmult_const 0 hV0 i
        rw [h1, hmult_one i] at h1lt
        exact absurd h1lt (lt_irrefl 1)
    filter_upwards [hV_mem, hg_deg, hcoeff_ev] with y hyV hdeg_y hcoeff_y
    rw [hval0]
    apply order_section_eq_one_of_simple g Ng hg_deg_bound (y, 0) (η i y) hcoeff_y
    · exact (hη_roots y hyV (η i y)).mpr ⟨i, rfl⟩
    · intro hd
      have hgy_ne : g (y, 0) ≠ 0 := by
        intro h
        rw [h, Polynomial.natDegree_zero] at hdeg_y
        omega
      have hroot_y : (g (y, 0)).IsRoot (η i y) := (hη_roots y hyV (η i y)).mpr ⟨i, rfl⟩
      have h1lt : 1 < (g (y, 0)).rootMultiplicity (η i y) :=
        (Polynomial.one_lt_rootMultiplicity_iff_isRoot hgy_ne).mpr ⟨hroot_y, hd⟩
      rw [hmult_const y hyV i, hmult_one i] at h1lt
      exact absurd h1lt (lt_irrefl 1)
  · obtain ⟨V, hVopen, hV0, k, η, mult, h1, h2, h3, h4, h5, hoi⟩ :=
      multi_cluster_real_delineation Ng g hg_deg_bound hg_coeff_an hg_pos P hP_an hP_ne
        NA NB A B hA_deg hB_deg hA_coeff hB_coeff hmem hP_oi hg_deg
    exact ⟨V, hVopen, hV0, k, η, mult, h1, h2, h3, h4, h5, hoi⟩

open MvPolynomial Set Classical

variable {n : ℕ}

theorem lifting_generalized_codim_local
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (p : Fin n → ℝ) (hp : p ∈ S)
    (hdeg : DegreeInvariant f S)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ p ∈ U ∧
      AnalyticDelineable f (S ∩ U) ∧
      (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ (S ∩ U) → IsRootFunction f θ (S ∩ U) →
        OrderInvariantFull f (SectionGraph θ (S ∩ U))) := by
  -- Case split: if specialized degree is 0, delineation is trivial (no roots).
  by_cases h_deg_pos : 0 < (specialize f p).natDegree
  swap
  · -- Degree 0: specialize f a is a nonzero constant for all a ∈ S, hence has no roots
    have h_deg_zero : (specialize f p).natDegree = 0 := by omega
    have no_roots : ∀ a ∈ S, ∀ y : ℝ, ¬ (specialize f a).IsRoot y := by
      intro a ha y
      have hdeg_a : (specialize f a).natDegree = 0 := by rw [hdeg a ha p hp]; exact h_deg_zero
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_a, Polynomial.IsRoot, Polynomial.eval_C]
      intro hc0
      exact hspec_ne a ha (by rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_a, hc0, map_zero])
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_, ?_⟩
    · refine ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i,
        fun a ha y => ?_, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩
      exact ⟨fun h => absurd h (no_roots a (Set.inter_univ S ▸ ha) y),
        fun ⟨i, _⟩ => Fin.elim0 i⟩
    · intro θ _ hθ_root
      exfalso
      exact no_roots p hp (θ p) (hθ_root p (Set.mem_inter hp (Set.mem_univ _)))
  -- Step 1: Apply the straightening chart (Theorem 2.2.1)
  obtain ⟨s, hs, Φ, hΦ_source, hΦ_val, hΦ_an_all, hΦ_symm_an, hΦ_straight⟩ :=
    hS_submfld.straightening_chart p hp
  have hΦ_an : AnalyticAt ℝ Φ p := hΦ_an_all p hΦ_source
  -- Step 2: Define the chart-to-submanifold map Ψ : ℝˢ → ℝⁿ
  -- Ψ(y) = Φ⁻¹(y, 0) embeds ℝˢ into S near p.
  let Ψ : (Fin s → ℝ) → (Fin n → ℝ) := fun y => Φ.symm (y, 0)
  have hΨ_zero : Ψ 0 = p := by
    show Φ.symm ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ)) = p
    rw [← hΦ_val]; exact Φ.left_inv hΦ_source
  have hΨ_an : AnalyticAt ℝ Ψ 0 := by
    let emb : (Fin s → ℝ) → (Fin s → ℝ) × (Fin (n - s) → ℝ) := fun y => (y, 0)
    have h_emb : AnalyticAt ℝ emb 0 := analyticAt_id.prod analyticAt_const
    have h_chart : AnalyticAt ℝ Φ.symm (emb 0) := by
      change AnalyticAt ℝ Φ.symm (0, 0); exact hΦ_val ▸ hΦ_symm_an
    exact h_chart.comp h_emb
  -- Step 3: Define the section family g(y) = specialize f (Ψ y) (used downstream)
  let g : (Fin s → ℝ) → Polynomial ℝ := fun y => specialize f (Ψ y)
  -- g(0) = specialize f p
  have hg_zero : g 0 = specialize f p := by show specialize f (Ψ 0) = _; rw [hΨ_zero]
  -- Step 4: Ψ maps into S for y near 0
  have hΦ_target_zero : ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ)) ∈ Φ.target := by
    rw [← hΦ_val]; exact Φ.map_source hΦ_source
  have hΨ_source : ∀ y, (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target → Ψ y ∈ Φ.source :=
    fun y hy => Φ.map_target hy
  have hΨ_S : ∀ y, (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target → Ψ y ∈ S := by
    intro y hy
    exact (hΦ_straight (Ψ y) (Φ.map_target hy)).mpr (by
      show (Φ (Φ.symm (y, (0 : Fin (n - s) → ℝ)))).2 = 0
      rw [Φ.right_inv hy])
  -- Step 5: Round-trip: for x ∈ S ∩ Φ.source, Ψ((Φ x).1) = x
  have hΨ_roundtrip : ∀ x ∈ S, x ∈ Φ.source → Ψ ((Φ x).1) = x := by
    intro x hxS hx_source
    have h2 : (Φ x).2 = 0 := (hΦ_straight x hx_source).mp hxS
    show Φ.symm ((Φ x).1, (0 : Fin (n - s) → ℝ)) = x
    conv_rhs => rw [← Φ.left_inv hx_source]
    congr 1
    exact Prod.ext rfl h2.symm
  -- Step 6: g(y) = specialize f x for x = Ψ y, so roots of g(y) = roots of f at x
  -- For x ∈ S ∩ Φ.source: specialize f x = g((Φ x).1)
  have hg_spec : ∀ x ∈ S, x ∈ Φ.source → specialize f x = g ((Φ x).1) := by
    intro x hxS hx_source
    show specialize f x = specialize f (Ψ ((Φ x).1))
    rw [hΨ_roundtrip x hxS hx_source]
  -- Step 7: g has constant degree d = f.natDegree for y near 0
  have hg_deg : ∀ y, (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target →
      (g y).natDegree = (g 0).natDegree := by
    intro y hy
    show (specialize f (Ψ y)).natDegree = (specialize f (Ψ 0)).natDegree
    exact hdeg (Ψ y) (hΨ_S y hy) (Ψ 0) (hΨ_zero ▸ hp)
  -- Step 8: Build the full-base family `gfull` over `ℝˢ × ℝⁿ⁻ˢ` and the transferred `Pfull`.
  -- On the section, `gfull (y, 0) = g y` and `Pfull (y, 0) = P (Ψ y)` definitionally.
  let gfull : (Fin s → ℝ) × (Fin (n - s) → ℝ) → Polynomial ℝ :=
    fun w => specialize f (Φ.symm w)
  let Pfull : (Fin s → ℝ) × (Fin (n - s) → ℝ) → ℝ :=
    fun w => MvPolynomial.eval (Φ.symm w) P
  have hΦsymm_an0 : AnalyticAt ℝ Φ.symm (0 : (Fin s → ℝ) × (Fin (n - s) → ℝ)) := by
    show AnalyticAt ℝ Φ.symm ((0 : Fin s → ℝ), (0 : Fin (n - s) → ℝ))
    exact hΦ_val ▸ hΦ_symm_an
  -- `eval · P` is globally smooth (it is a polynomial map)
  have hP_contdiff : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun a => MvPolynomial.eval a P) :=
    (show AnalyticOnNhd ℝ (fun a => MvPolynomial.eval a P) Set.univ from
      fun a _ => AnalyticOnNhd.eval_mvPolynomial P a (Set.mem_univ a)).contDiff
  -- Step 8a: `gfull` hypotheses (analytic coefficients; degree constant along the section)
  have hgfull_coeff_an : ∀ i : ℕ, AnalyticAt ℝ (fun w => (gfull w).coeff i) 0 := by
    intro i
    show AnalyticAt ℝ (fun w => (specialize f (Φ.symm w)).coeff i) 0
    simp only [specialize, Polynomial.coeff_map]
    exact (AnalyticOnNhd.eval_mvPolynomial (f.coeff i) (Φ.symm 0) (Set.mem_univ _)).comp hΦsymm_an0
  have hgfull_pos : 0 < (gfull 0).natDegree := by
    show 0 < (g 0).natDegree; exact hg_zero ▸ h_deg_pos
  have hgfull_deg : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      (gfull (y, 0)).natDegree = (gfull 0).natDegree := by
    filter_upwards [(Φ.open_target.preimage (continuous_id.prodMk continuous_const)).mem_nhds
      hΦ_target_zero] with y hy
    exact hg_deg y hy
  -- Step 8b: `Pfull` hypotheses, with the (finite) order supplied by the chart transfer
  have hPfull_an : AnalyticAt ℝ Pfull 0 :=
    (AnalyticOnNhd.eval_mvPolynomial P (Φ.symm 0) (Set.mem_univ _)).comp hΦsymm_an0
  have hPfull_ne : order ℝ Pfull 0 ≠ ⊤ := by
    have htr : order ℝ Pfull 0 = order ℝ (fun a => MvPolynomial.eval a P) (Φ.symm 0) :=
      order_comp_partialHomeomorph_symm Φ (fun a => MvPolynomial.eval a P) 0
        hΦ_target_zero hΦ_an_all hΦsymm_an0 hP_contdiff
    rw [htr]; exact polyOrder_ne_top_of_ne_zero P hP_ne (Φ.symm 0)
  have hPfull_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ Pfull (y, 0) = order ℝ Pfull 0 := by
    obtain ⟨W, hW_sub, hW_open, hxW⟩ := eventually_nhds_iff.mp hΦsymm_an0.eventually_analyticAt
    have hΦsymm_p : Φ.symm (0 : (Fin s → ℝ) × (Fin (n - s) → ℝ)) = p := hΨ_zero
    have hnbhd : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
        (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target ∩ W :=
      ((Φ.open_target.inter hW_open).preimage
        (continuous_id.prodMk continuous_const)).mem_nhds ⟨hΦ_target_zero, hxW⟩
    filter_upwards [hnbhd] with y hy
    have htr_y : order ℝ Pfull (y, 0)
        = order ℝ (fun a => MvPolynomial.eval a P) (Φ.symm (y, 0)) :=
      order_comp_partialHomeomorph_symm Φ (fun a => MvPolynomial.eval a P) (y, 0)
        hy.1 hΦ_an_all (hW_sub _ hy.2) hP_contdiff
    have htr_0 : order ℝ Pfull 0
        = order ℝ (fun a => MvPolynomial.eval a P) (Φ.symm 0) :=
      order_comp_partialHomeomorph_symm Φ (fun a => MvPolynomial.eval a P) 0
        hΦ_target_zero hΦ_an_all hΦsymm_an0 hP_contdiff
    rw [htr_y, htr_0]
    exact hP_oi (Φ.symm (y, 0)) (hΨ_S y hy.1) (Φ.symm 0) (by rw [hΦsymm_p]; exact hp)
  -- Step 9: Apply the delineation theorem (proved on `{C, E, A2}`) to the full-base family,
  -- supplying the analytic Bézout cofactors and degree bounds.
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hP_mem
  have hA_cof : ∀ k, AnalyticAt ℝ
      (fun w => (a.map (MvPolynomial.eval (Φ.symm w))).coeff k) 0 := fun k => by
    simp only [Polynomial.coeff_map]
    exact (AnalyticOnNhd.eval_mvPolynomial (a.coeff k) (Φ.symm 0) (Set.mem_univ _)).comp hΦsymm_an0
  have hB_cof : ∀ k, AnalyticAt ℝ
      (fun w => (b.map (MvPolynomial.eval (Φ.symm w))).coeff k) 0 := fun k => by
    simp only [Polynomial.coeff_map]
    exact (AnalyticOnNhd.eval_mvPolynomial (b.coeff k) (Φ.symm 0) (Set.mem_univ _)).comp hΦsymm_an0
  have hmem_cof : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin (n - s) → ℝ)),
      Polynomial.C (Pfull w) = (a.map (MvPolynomial.eval (Φ.symm w))) * gfull w
        + (b.map (MvPolynomial.eval (Φ.symm w))) * Polynomial.derivative (gfull w) := by
    filter_upwards with w
    have hgw : gfull w = Polynomial.map (MvPolynomial.eval (Φ.symm w)) f := rfl
    have h1 : a.map (MvPolynomial.eval (Φ.symm w)) * gfull w
        + b.map (MvPolynomial.eval (Φ.symm w)) * Polynomial.derivative (gfull w)
        = (a * f + b * Polynomial.derivative f).map (MvPolynomial.eval (Φ.symm w)) := by
      rw [hgw, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          ← Polynomial.derivative_map]
    rw [h1, hab, Polynomial.map_C]
  obtain ⟨V, hV_open, hV_zero, k, η, mult, hη_an, hη_ord, hη_roots, hmult_pos, hmult_const,
      hsec_oi⟩ :=
    analytic_pseudopoly_delineable' f.natDegree gfull (fun _ => Polynomial.natDegree_map_le)
      hgfull_coeff_an hgfull_pos hgfull_deg Pfull hPfull_an hPfull_ne
      a.natDegree b.natDegree (fun w => a.map (MvPolynomial.eval (Φ.symm w)))
      (fun w => b.map (MvPolynomial.eval (Φ.symm w)))
      (fun _ => Polynomial.natDegree_map_le) (fun _ => Polynomial.natDegree_map_le)
      hA_cof hB_cof hmem_cof hPfull_oi
  -- Step 10: Shrink `V` to a connected neighborhood of `0` on which (i) the chart inverse `Φ.symm`
  -- is analytic and (ii) every branch's section order is constant (the threaded order-invariance
  -- `hsec_oi`), then take the connected component of `0` for preconnectedness.
  obtain ⟨W_symm, hW_symm_sub, hW_symm_open, hW_symm_mem⟩ :=
    eventually_nhds_iff.mp hΦsymm_an0.eventually_analyticAt
  have hoi_all : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ i : Fin k,
      order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2) ((y, 0), η i y)
        = order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2)
            ((0, 0), η i 0) :=
    Filter.eventually_all.mpr hsec_oi
  obtain ⟨W_oi, hW_oi_sub, hW_oi_open, hW_oi_mem⟩ := eventually_nhds_iff.mp hoi_all
  let Vt : Set (Fin s → ℝ) :=
    V ∩ {y | (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target}
      ∩ {y | (y, (0 : Fin (n - s) → ℝ)) ∈ W_symm} ∩ W_oi
  have hVt_open : IsOpen Vt :=
    ((hV_open.inter (Φ.open_target.preimage (continuous_id.prodMk continuous_const))).inter
      (hW_symm_open.preimage (continuous_id.prodMk continuous_const))).inter hW_oi_open
  have hVt_zero : (0 : Fin s → ℝ) ∈ Vt :=
    ⟨⟨⟨hV_zero, hΦ_target_zero⟩, hW_symm_mem⟩, hW_oi_mem⟩
  let V' : Set (Fin s → ℝ) := connectedComponentIn Vt 0
  have hV'_sub_Vt : V' ⊆ Vt := connectedComponentIn_subset Vt 0
  have hV'_sub_V : V' ⊆ V := fun y hy => (hV'_sub_Vt hy).1.1.1
  have hV'_target : ∀ y ∈ V', (y, (0 : Fin (n - s) → ℝ)) ∈ Φ.target :=
    fun y hy => (hV'_sub_Vt hy).1.1.2
  have hV'_symm : ∀ y ∈ V', (y, (0 : Fin (n - s) → ℝ)) ∈ W_symm :=
    fun y hy => (hV'_sub_Vt hy).1.2
  have hV'_oi : ∀ y ∈ V', ∀ i : Fin k,
      order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2) ((y, 0), η i y)
        = order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2)
            ((0, 0), η i 0) :=
    fun y hy => hW_oi_sub y (hV'_sub_Vt hy).2
  have hV'_open : IsOpen V' := hVt_open.connectedComponentIn
  have hV'_zero : (0 : Fin s → ℝ) ∈ V' := mem_connectedComponentIn hVt_zero
  have hV'_preconn : IsPreconnected V' := isPreconnected_connectedComponentIn
  -- Step 11: Define U = {x ∈ Φ.source | (Φ x).1 ∈ V'}
  let U : Set (Fin n → ℝ) := Φ.source ∩ (Prod.fst ∘ Φ) ⁻¹' V'
  have hU_open : IsOpen U :=
    Φ.continuousOn.fst.isOpen_inter_preimage Φ.open_source hV'_open
  have hU_p : p ∈ U := by
    refine ⟨hΦ_source, ?_⟩
    show (Φ p).1 ∈ V'
    have : (Φ p).1 = 0 := by
      have := congr_arg Prod.fst (show Φ p = (0, 0) from hΦ_val ▸ rfl)
      simp at this; exact this
    rw [this]; exact hV'_zero
  have hV'_in_V : ∀ a ∈ S ∩ U, (Φ a).1 ∈ V :=
    fun a ha => hV'_sub_V ha.2.2
  -- S ∩ U is preconnected: it equals Ψ '' V', continuous image of preconnected set
  have hSU_preconn : IsPreconnected (S ∩ U) := by
    have hΨ_image : Ψ '' V' ⊆ S ∩ U := by
      intro x ⟨y, hy, hxy⟩; subst hxy
      exact ⟨hΨ_S y (hV'_target y hy), hΨ_source y (hV'_target y hy), by
        show (Φ (Ψ y)).1 ∈ V'
        rw [show Φ (Ψ y) = (y, (0 : Fin (n - s) → ℝ)) from Φ.right_inv (hV'_target y hy)]
        exact hy⟩
    have hSU_sub_image : S ∩ U ⊆ Ψ '' V' := by
      intro a ⟨haS, ha_source, ha_V'⟩
      exact ⟨(Φ a).1, ha_V', hΨ_roundtrip a haS ha_source⟩
    rw [(hΨ_image.antisymm hSU_sub_image).symm]
    apply hV'_preconn.image Ψ
    intro y hy
    exact (Φ.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => hV'_target z hz)).continuousWithinAt (mem_of_mem_of_subset hy (subset_refl _))
  -- Extract delineability so both goals can use it
  have hdel : AnalyticDelineable f (S ∩ U) := by
    let θ' : Fin k → (Fin n → ℝ) → ℝ := fun i x => η i ((Φ x).1)
    refine ⟨k, θ', mult, ?_, ?_, ?_, hmult_pos, ?_⟩
    · intro i a ha
      have h_phi_fst : AnalyticAt ℝ (Prod.fst ∘ Φ) a :=
        analyticAt_fst.comp (hΦ_an_all a ha.2.1)
      have h_eta : AnalyticAt ℝ (η i) ((Prod.fst ∘ ↑Φ) a) :=
        (hη_an i).analyticAt (hV_open.mem_nhds (hV'_in_V a ha))
      exact (h_eta.comp h_phi_fst).analyticWithinAt
    · intro a ha i j hij
      exact hη_ord ((Φ a).1) (hV'_in_V a ha) i j hij
    · intro a ha y
      rw [hg_spec a ha.1 ha.2.1]
      exact hη_roots ((Φ a).1) (hV'_in_V a ha) y
    · intro a ha i
      rw [hg_spec a ha.1 ha.2.1]
      exact hmult_const ((Φ a).1) (hV'_in_V a ha) i
  refine ⟨U, hU_open, hU_p, hdel, ?_⟩
  -- Goal 2: Order-invariance on section graphs. An arbitrary continuous root function `θ` tracks ONE
  -- delineation branch `η i₀` across the (preconnected) `S ∩ U` (a clopen/connectivity argument), and
  -- that branch's section order is constant on `V'` (the threaded `hsec_oi`); the straightening-chart
  -- bridge `orderFull_eq_order_section_chart` then transports this to `orderFull f a (θ a)`.
  intro θ hθ_cont hθ_root
  classical
  have hp_SU : p ∈ S ∩ U := ⟨hp, hU_p⟩
  -- branch values are strictly separated, hence the branch index is injective
  have hη_inj : ∀ y ∈ V, Function.Injective (fun l : Fin k => η l y) := by
    intro y hy l₁ l₂ hl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hl (ne_of_lt (hη_ord y hy l₁ l₂ h))
    · exact absurd hl.symm (ne_of_lt (hη_ord y hy l₂ l₁ h))
  -- each value `θ a` is some branch (it is a root of the section family `gfull (·, 0)`)
  have hθ_branch : ∀ a ∈ S ∩ U, ∃ i : Fin k, θ a = η i ((Φ a).1) := by
    intro a ha
    have hroot : (g ((Φ a).1)).IsRoot (θ a) := by
      rw [← hg_spec a ha.1 ha.2.1]; exact hθ_root a ha
    exact (hη_roots ((Φ a).1) (hV'_in_V a ha) (θ a)).mp hroot
  obtain ⟨i₀, hi₀⟩ := hθ_branch p hp_SU
  -- the branch-index function, well-defined on `S ∩ U`
  let idxf : (Fin n → ℝ) → Fin k := fun a =>
    if h : ∃ i : Fin k, θ a = η i ((Φ a).1) then Classical.choose h else i₀
  have hidxf_spec : ∀ a ∈ S ∩ U, θ a = η (idxf a) ((Φ a).1) := by
    intro a ha
    have h := hθ_branch a ha
    simp only [idxf, dif_pos h]
    exact Classical.choose_spec h
  -- `idxf` is locally constant on `S ∩ U` (continuity of `θ`, `η` + branch separation)
  have hidxf_loc : ∀ a₀ ∈ S ∩ U, ∀ᶠ a in 𝓝[S ∩ U] a₀, idxf a = idxf a₀ := by
    intro a₀ ha₀
    set j := idxf a₀ with hj
    have hsub_source : S ∩ U ⊆ Φ.source := fun x hx => hx.2.1
    have hθ_cwa : ContinuousWithinAt θ (S ∩ U) a₀ := hθ_cont a₀ ha₀
    have hηc_cwa : ∀ l : Fin k, ContinuousWithinAt (fun a => η l ((Φ a).1)) (S ∩ U) a₀ := by
      intro l
      have hfst_on : ContinuousWithinAt (fun a => (Φ a).1) (S ∩ U) a₀ :=
        ((Φ.continuousOn.mono hsub_source).continuousWithinAt ha₀).fst
      have hη_on : ContinuousWithinAt (η l) V ((Φ a₀).1) :=
        ((hη_an l).continuousOn).continuousWithinAt (hV'_in_V a₀ ha₀)
      exact ContinuousWithinAt.comp (g := η l) (f := fun a => (Φ a).1) hη_on hfst_on
        (fun a ha => hV'_in_V a ha)
    have hne_ev : ∀ᶠ a in 𝓝[S ∩ U] a₀, ∀ l : Fin k, l ≠ j → θ a ≠ η l ((Φ a).1) := by
      rw [eventually_all]
      intro l
      by_cases hlj : l = j
      · exact Filter.Eventually.of_forall (fun a hcon => absurd hlj hcon)
      · have hd0 : θ a₀ ≠ η l ((Φ a₀).1) := by
          rw [hidxf_spec a₀ ha₀]
          intro h
          exact hlj (hη_inj ((Φ a₀).1) (hV'_in_V a₀ ha₀) h).symm
        have htend : Filter.Tendsto (fun a => θ a - η l ((Φ a).1)) (𝓝[S ∩ U] a₀)
            (𝓝 (θ a₀ - η l ((Φ a₀).1))) := hθ_cwa.sub (hηc_cwa l)
        have hev : ∀ᶠ a in 𝓝[S ∩ U] a₀, θ a - η l ((Φ a).1) ≠ 0 :=
          htend.eventually (isOpen_ne.mem_nhds (sub_ne_zero.mpr hd0))
        filter_upwards [hev] with a ha _
        exact sub_ne_zero.mp ha
    filter_upwards [hne_ev, self_mem_nhdsWithin] with a ha_ne ha_SU
    by_contra hcon
    exact ha_ne (idxf a) hcon (hidxf_spec a ha_SU)
  -- locally constant + preconnected ⟹ constant
  have hcont_idx : ContinuousOn (fun a => (idxf a : ℕ)) (S ∩ U) := by
    intro a₀ ha₀
    rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
    filter_upwards [hidxf_loc a₀ ha₀] with a ha
    show (idxf a : ℕ) = (idxf a₀ : ℕ)
    rw [ha]
  have hidxf_const : ∀ a ∈ S ∩ U, idxf a = idxf p := fun a ha =>
    Fin.val_injective (hSU_preconn.constant hcont_idx ha hp_SU)
  have hidxf_p : idxf p = i₀ :=
    hη_inj ((Φ p).1) (hV'_in_V p hp_SU) ((hidxf_spec p hp_SU).symm.trans hi₀)
  have hsingle : ∀ a ∈ S ∩ U, θ a = η i₀ ((Φ a).1) := by
    intro a ha
    rw [hidxf_spec a ha, hidxf_const a ha, hidxf_p]
  -- transport to `orderFull` through the chart bridge; branch `i₀`'s section order is constant on `V'`
  have hconst : ∀ a ∈ S ∩ U, orderFull f a (θ a)
      = order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2)
          ((0, 0), η i₀ 0) := by
    intro a ha
    have hya : (Φ a).1 ∈ V' := ha.2.2
    have ha_eq : Φ.symm ((Φ a).1, 0) = a := hΨ_roundtrip a ha.1 ha.2.1
    calc orderFull f a (θ a)
        = orderFull f (Φ.symm ((Φ a).1, 0)) (θ a) := by rw [ha_eq]
      _ = order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2)
            (((Φ a).1, 0), θ a) :=
          orderFull_eq_order_section_chart f Φ ((Φ a).1, 0) (θ a) (hV'_target _ hya)
            hΦ_an_all (hW_symm_sub _ (hV'_symm _ hya))
      _ = order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2)
            (((Φ a).1, 0), η i₀ ((Φ a).1)) := by rw [hsingle a ha]
      _ = order ℝ (fun q : ((Fin s → ℝ) × (Fin (n - s) → ℝ)) × ℝ => (gfull q.1).eval q.2)
            ((0, 0), η i₀ 0) := hV'_oi ((Φ a).1) hya i₀
  intro pt hpt qt hqt
  obtain ⟨hpt1, hpt2⟩ := hpt
  obtain ⟨hqt1, hqt2⟩ := hqt
  show orderFull f pt.1 pt.2 = orderFull f qt.1 qt.2
  rw [hpt2, hqt2]
  exact (hconst pt.1 hpt1).trans (hconst qt.1 hqt1).symm

/-! ### Globalization: local delineation on connected set → global -/

/-- Globalization of analytic delineability on a connected set (not necessarily open).
This generalizes `locally_delineable_to_global` from open sets to arbitrary connected sets.
The proof is a connectivity argument: root count and multiplicities are locally constant
in the subspace topology of `S`, hence constant on connected `S`. -/
theorem locally_delineable_to_global'
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_conn : IsConnected S)
    (hlocal : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)),
      IsOpen U ∧ a ∈ U ∧ AnalyticDelineable f (S ∩ U)) :
    AnalyticDelineable f S := by
  -- Step 1: Pick base point a₀ and get its local delineation
  obtain ⟨a₀, ha₀⟩ := hS_conn.nonempty
  obtain ⟨U₀, hU₀_open, ha₀U₀, k, θ₀, m₀, hθ₀_an, hθ₀_ord, hθ₀_roots, hm₀_pos, hm₀_const⟩ :=
    hlocal a₀ ha₀
  -- Step 2: Extract delineation data at each point
  have hlocal' : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)) (k' : ℕ)
      (θ' : Fin k' → (Fin n → ℝ) → ℝ) (m' : Fin k' → ℕ),
      IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOn ℝ (θ' i) (S ∩ U)) ∧
      (∀ b ∈ S ∩ U, ∀ i j : Fin k', i < j → θ' i b < θ' j b) ∧
      (∀ b ∈ S ∩ U, ∀ y, (specialize f b).IsRoot y ↔ ∃ i, y = θ' i b) ∧
      (∀ i, 0 < m' i) ∧
      (∀ b ∈ S ∩ U, ∀ i, (specialize f b).rootMultiplicity (θ' i b) = m' i) := by
    intro a ha
    obtain ⟨U, hU, haU, k', θ', m', h1, h2, h3, h4, h5⟩ := hlocal a ha
    exact ⟨U, k', θ', m', hU, haU, h1, h2, h3, h4, h5⟩
  choose Uc kc θc mc hUc_open hUc_mem hθc_an hθc_ord hθc_roots _hmc_pos hmc_const using hlocal'
  -- Step 3: Root count is locally constant on S → constant by connectivity
  have hkc_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ Uc a ha → kc a ha = kc b hb :=
    fun a b ha hb hab => strictMono_fin_card_eq _ _
      (hθc_ord a ha b hab) (hθc_ord b hb b ⟨hb, hUc_mem b hb⟩)
      (delineable_root_range_eq (S ∩ Uc a ha) (S ∩ Uc b hb) f
        (θc a ha) (θc b hb) (hθc_roots a ha) (hθc_roots b hb) b hab ⟨hb, hUc_mem b hb⟩)
  let rootCount : (Fin n → ℝ) → ℕ := fun a => if ha : a ∈ S then kc a ha else 0
  have hrc_cont : ContinuousOn rootCount S := by
    intro a ha
    rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
    exact Filter.mem_of_superset
      (inter_mem_nhdsWithin S ((hUc_open a ha).mem_nhds (hUc_mem a ha)))
      fun b ⟨hbS, hbU⟩ => show rootCount b = rootCount a by
        simp only [rootCount, dif_pos hbS, dif_pos ha]
        exact (hkc_agree a b ha hbS ⟨hbS, hbU⟩).symm
  have hkc_eq : ∀ a (ha : a ∈ S), kc a ha = k := by
    intro a ha
    have h1 := hS_conn.isPreconnected.constant hrc_cont ha ha₀
    simp only [rootCount, dif_pos ha, dif_pos ha₀] at h1
    have h2 : kc a₀ ha₀ = k := strictMono_fin_card_eq _ _
      (hθc_ord a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩)
      (hθ₀_ord a₀ ⟨ha₀, ha₀U₀⟩)
      (delineable_root_range_eq (S ∩ Uc a₀ ha₀) (S ∩ U₀) f
        (θc a₀ ha₀) θ₀ (hθc_roots a₀ ha₀) hθ₀_roots
        a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ ⟨ha₀, ha₀U₀⟩)
    omega
  -- Step 4: Multiplicities are locally constant → constant
  have hmc_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ Uc a ha → ∀ i : Fin k,
      mc a ha (Fin.cast (hkc_eq a ha).symm i) = mc b hb (Fin.cast (hkc_eq b hb).symm i) := by
    intro a b ha hb hab i
    have hval_eq : θc a ha (Fin.cast (hkc_eq a ha).symm i) b =
        θc b hb (Fin.cast (hkc_eq b hb).symm i) b := by
      have hrange : Set.range (fun j : Fin k => θc a ha (Fin.cast (hkc_eq a ha).symm j) b) =
          Set.range (fun j : Fin k => θc b hb (Fin.cast (hkc_eq b hb).symm j) b) := by
        ext y; simp only [Set.mem_range]; constructor
        · rintro ⟨j, rfl⟩
          obtain ⟨j', hj'⟩ := (hθc_roots b hb b ⟨hb, hUc_mem b hb⟩ _).mp
            ((hθc_roots a ha b hab _).mpr ⟨_, rfl⟩)
          exact ⟨Fin.cast (hkc_eq b hb) j', hj'.symm⟩
        · rintro ⟨j, rfl⟩
          obtain ⟨j', hj'⟩ := (hθc_roots a ha b hab _).mp
            ((hθc_roots b hb b ⟨hb, hUc_mem b hb⟩ _).mpr ⟨_, rfl⟩)
          exact ⟨Fin.cast (hkc_eq a ha) j', hj'.symm⟩
      exact congrFun (strictMono_fin_eq_of_range_eq _ _
        (fun p q hpq => hθc_ord a ha b hab _ _ (by exact_mod_cast hpq))
        (fun p q hpq => hθc_ord b hb b ⟨hb, hUc_mem b hb⟩ _ _ (by exact_mod_cast hpq))
        hrange) i
    have hm1 := hmc_const a ha b hab (Fin.cast (hkc_eq a ha).symm i)
    rw [hval_eq] at hm1
    exact hm1.symm.trans (hmc_const b hb b ⟨hb, hUc_mem b hb⟩ _)
  have hmc_eq : ∀ (a : Fin n → ℝ) (ha : a ∈ S) (i : Fin k),
      mc a ha (Fin.cast (hkc_eq a ha).symm i) = m₀ i := by
    intro a ha i
    let multFunc : (Fin n → ℝ) → ℕ := fun b =>
      if hb : b ∈ S then mc b hb (Fin.cast (hkc_eq b hb).symm i) else 0
    have hmc_cont : ContinuousOn multFunc S := by
      intro a' ha'
      rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
      exact Filter.mem_of_superset
        (inter_mem_nhdsWithin S ((hUc_open a' ha').mem_nhds (hUc_mem a' ha')))
        fun b ⟨hbS, hbU⟩ => show multFunc b = multFunc a' by
          simp only [multFunc, dif_pos hbS, dif_pos ha']
          exact (hmc_agree a' b ha' hbS ⟨hbS, hbU⟩ i).symm
    have h1 := hS_conn.isPreconnected.constant hmc_cont ha ha₀
    simp only [multFunc, dif_pos ha, dif_pos ha₀] at h1
    have hval₀ : θc a₀ ha₀ (Fin.cast (hkc_eq a₀ ha₀).symm i) a₀ = θ₀ i a₀ := by
      have hrange₀ : Set.range (fun j : Fin k => θc a₀ ha₀ (Fin.cast (hkc_eq a₀ ha₀).symm j) a₀) =
          Set.range (fun j => θ₀ j a₀) := by
        ext y; simp only [Set.mem_range]; constructor
        · rintro ⟨j, rfl⟩
          exact ((hθ₀_roots a₀ ⟨ha₀, ha₀U₀⟩ _).mp
            ((hθc_roots a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _).mpr ⟨_, rfl⟩)).imp
            fun _ h => h.symm
        · rintro ⟨j, rfl⟩
          obtain ⟨j', hj'⟩ := (hθc_roots a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _).mp
            ((hθ₀_roots a₀ ⟨ha₀, ha₀U₀⟩ _).mpr ⟨j, rfl⟩)
          exact ⟨Fin.cast (hkc_eq a₀ ha₀) j', hj'.symm⟩
      exact congrFun (strictMono_fin_eq_of_range_eq _ _
        (fun p q hpq => hθc_ord a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ _ _ (by exact_mod_cast hpq))
        (fun p q hpq => hθ₀_ord a₀ ⟨ha₀, ha₀U₀⟩ p q hpq)
        hrange₀) i
    have hm₀ := hmc_const a₀ ha₀ a₀ ⟨ha₀, hUc_mem a₀ ha₀⟩ (Fin.cast (hkc_eq a₀ ha₀).symm i)
    rw [hval₀] at hm₀
    have hm₀' := hm₀_const a₀ ⟨ha₀, ha₀U₀⟩ i
    omega
  -- Step 5: Construct k-indexed delineation at each point
  have hk_loc : ∀ a ∈ S, ∃ (U : Set (Fin n → ℝ)) (θ : Fin k → (Fin n → ℝ) → ℝ),
      IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOn ℝ (θ i) (S ∩ U)) ∧
      (∀ b ∈ S ∩ U, ∀ i j : Fin k, i < j → θ i b < θ j b) ∧
      (∀ b ∈ S ∩ U, ∀ y, (specialize f b).IsRoot y ↔ ∃ i, y = θ i b) ∧
      (∀ b ∈ S ∩ U, ∀ i, (specialize f b).rootMultiplicity (θ i b) = m₀ i) := by
    intro a ha
    refine ⟨Uc a ha, fun i => θc a ha (Fin.cast (hkc_eq a ha).symm i),
      hUc_open a ha, hUc_mem a ha, ?_, ?_, ?_, ?_⟩
    · exact fun i => hθc_an a ha _
    · intro b hb i j hij
      exact hθc_ord a ha b hb _ _ (by exact_mod_cast hij)
    · intro b hb y
      rw [hθc_roots a ha b hb y]
      exact ⟨fun ⟨i, hi⟩ => ⟨Fin.cast (hkc_eq a ha) i, hi⟩,
             fun ⟨i, hi⟩ => ⟨Fin.cast (hkc_eq a ha).symm i, by simpa using hi⟩⟩
    · intro b hb i
      exact (hmc_const a ha b hb (Fin.cast (hkc_eq a ha).symm i)).trans (hmc_eq a ha i)
  -- Step 6: Define global root functions and verify properties
  choose U_loc θ_loc h_all using hk_loc
  have hθ_agree : ∀ (a b : Fin n → ℝ) (ha : a ∈ S) (hb : b ∈ S),
      b ∈ S ∩ U_loc a ha →
      (fun j => θ_loc a ha j b) = (fun j => θ_loc b hb j b) := by
    intro a b ha hb hab
    exact strictMono_fin_eq_of_range_eq _ _
      ((h_all a ha).2.2.2.1 b hab) ((h_all b hb).2.2.2.1 b ⟨hb, (h_all b hb).2.1⟩)
      (delineable_root_range_eq (S ∩ U_loc a ha) (S ∩ U_loc b hb) f
        (θ_loc a ha) (θ_loc b hb) (h_all a ha).2.2.2.2.1 (h_all b hb).2.2.2.2.1
        b hab ⟨hb, (h_all b hb).2.1⟩)
  refine ⟨k, fun i a => if ha : a ∈ S then θ_loc a ha i a else 0, m₀,
    ?_, ?_, ?_, hm₀_pos, ?_⟩
  · intro i
    apply analyticOn_of_locally_analyticOn
    intro a ha
    refine ⟨U_loc a ha, (h_all a ha).1, (h_all a ha).2.1, ?_⟩
    apply ((h_all a ha).2.2.1 i).congr
    intro b hb
    dsimp only
    rw [dif_pos hb.1]
    exact (congrFun (hθ_agree a b ha hb.1 hb) i).symm
  · intro a ha i j hij
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.1 a ⟨ha, (h_all a ha).2.1⟩ i j hij
  · intro a ha y
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.2.1 a ⟨ha, (h_all a ha).2.1⟩ y
  · intro a ha i
    simp only [dif_pos ha]
    exact (h_all a ha).2.2.2.2.2 a ⟨ha, (h_all a ha).2.1⟩ i

/-- Globalization of order invariance on section graphs.
If `orderFull f · (θ ·)` is locally constant on a connected set `S`, it is globally
constant. -/
theorem order_invariant_of_locally_invariant
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (θ : (Fin n → ℝ) → ℝ)
    (hS_conn : IsConnected S)
    (_hθ_cont : ContinuousOn θ S)
    (_hθ_root : IsRootFunction f θ S)
    (hlocal : ∀ p ∈ S, ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ p ∈ U ∧
      OrderInvariantFull f (SectionGraph θ (S ∩ U))) :
    OrderInvariantFull f (SectionGraph θ S) := by
  -- Extract local constancy of ordFun
  let ordFun := fun x => orderFull f x (θ x)
  have hlc : ∀ p ∈ S, ∃ U, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ S ∩ U, ordFun q = ordFun p := by
    intro p hp
    obtain ⟨U, hU, hpU, hOI⟩ := hlocal p hp
    exact ⟨U, hU, hpU, fun q ⟨hqS, hqU⟩ =>
      hOI ⟨q, θ q⟩ ⟨⟨hqS, hqU⟩, rfl⟩ ⟨p, θ p⟩ ⟨⟨hp, hpU⟩, rfl⟩⟩
  -- Unfold goal to ordFun a = ordFun b for a, b ∈ S
  intro ⟨a, _⟩ ha ⟨b, _⟩ hb
  simp only [SectionGraph, mem_setOf_eq] at ha hb
  obtain ⟨haS, rfl⟩ := ha; obtain ⟨hbS, rfl⟩ := hb
  show ordFun a = ordFun b
  -- Connectivity argument: ordFun is locally constant on S, hence constant
  choose Uloc hUloc_open hUloc_mem hUloc_const using hlc
  set c := ordFun a
  -- A covers {x ∈ S | ordFun x = c}, B covers the complement in S
  set A := ⋃ (x : {x // x ∈ S ∧ ordFun x = c}), Uloc x.1 x.2.1
  set B := ⋃ (x : {x // x ∈ S ∧ ordFun x ≠ c}), Uloc x.1 x.2.1
  have hA_open : IsOpen A := isOpen_iUnion fun x => hUloc_open x.1 x.2.1
  have hB_open : IsOpen B := isOpen_iUnion fun x => hUloc_open x.1 x.2.1
  have hS_sub : S ⊆ A ∪ B := by
    intro x hxS
    by_cases hxc : ordFun x = c
    · exact Or.inl (mem_iUnion.mpr ⟨⟨x, hxS, hxc⟩, hUloc_mem x hxS⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨x, hxS, hxc⟩, hUloc_mem x hxS⟩)
  have hSA : (S ∩ A).Nonempty :=
    ⟨a, haS, mem_iUnion.mpr ⟨⟨a, haS, rfl⟩, hUloc_mem a haS⟩⟩
  have hSAB_empty : ¬(S ∩ (A ∩ B)).Nonempty := by
    rintro ⟨x, hxS, hxA, hxB⟩
    obtain ⟨⟨y, hyS, hyc⟩, hxUy⟩ := mem_iUnion.mp hxA
    obtain ⟨⟨z, hzS, hzc⟩, hxUz⟩ := mem_iUnion.mp hxB
    have h1 : ordFun x = ordFun y := hUloc_const y hyS x ⟨hxS, hxUy⟩
    have h2 : ordFun x = ordFun z := hUloc_const z hzS x ⟨hxS, hxUz⟩
    exact hzc ((h2.symm.trans h1).trans hyc)
  -- By IsPreconnected, S ∩ B must be empty
  by_contra hne
  exact hSAB_empty (hS_conn.isPreconnected A B hA_open hB_open hS_sub hSA
    ⟨b, hbS, mem_iUnion.mpr ⟨⟨b, hbS, fun h => hne h.symm⟩, hUloc_mem b hbS⟩⟩)

/-! ### Case 1 ≤ s ≤ r - 2: S has positive codimension -/

/-- Case 1 ≤ s ≤ r - 2 of the generalized lifting theorem.
Proved from `lifting_generalized_codim_local` (local Weierstrass–Zariski axiom)
and globalization lemmas. -/
theorem lifting_generalized_codim_case
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (_hS_not_open : ¬ IsOpen S)
    (hdeg : DegreeInvariant f S)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  -- Step 1: Local delineation at each point (from the Weierstrass–Zariski axiom)
  have hlocal : ∀ p ∈ S, ∃ (U : Set (Fin n → ℝ)), IsOpen U ∧ p ∈ U ∧
      AnalyticDelineable f (S ∩ U) ∧
      (∀ θ, ContinuousOn θ (S ∩ U) → IsRootFunction f θ (S ∩ U) →
        OrderInvariantFull f (SectionGraph θ (S ∩ U))) :=
    fun p hp => lifting_generalized_codim_local S f hS_submfld p hp
      hdeg hspec_ne P hP_ne hP_mem hP_oi
  -- Step 2: Globalize analytic delineability
  refine ⟨locally_delineable_to_global' S f hS_conn
    (fun a ha => ?_), fun θ hθ_cont hθ_root => ?_⟩
  · obtain ⟨U, hU_open, haU, hU_del, _⟩ := hlocal a ha
    exact ⟨U, hU_open, haU, hU_del⟩
  -- Step 3: Globalize order invariance on section graphs
  · apply order_invariant_of_locally_invariant S f θ hS_conn hθ_cont hθ_root
    intro p hp
    obtain ⟨U, hU_open, hpU, _, hU_oi⟩ := hlocal p hp
    exact ⟨U, hU_open, hpU, hU_oi θ (hθ_cont.mono inter_subset_left)
      (fun a ha => hθ_root a ha.1)⟩

end
