import Cad.Multivariate.ProjectionTheorem.Generalized.F3
import Cad.Multivariate.ProjectionTheorem.Generalized.ShiftCluster
import Cad.Multivariate.ProjectionTheorem.Generalized.SimpleRoots

/-!
# Multi-cluster assembly — step 1: translation

`single_cluster_real_delineation_at` lifts `single_cluster_real_delineation` (stated at the root
`t = 0`) to a general real root `t_j` of `g(0,0)`, by Taylor-shifting the family
`g ↦ taylor t_j g` (and the cofactors), applying the `t=0` result, and shifting the conclusion back.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **Order is invariant under translation.** `order (fun y => f (y + c)) x = order f (x + c)`
(unconditional: `iteratedFDeriv` of a translation-composite is the shifted `iteratedFDeriv`). Used to
transport order-invariance through the Taylor shift `t ↦ t - t_j` of the cluster localization. -/
theorem order_comp_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (c x : E) :
    order ℝ (fun y => f (y + c)) x = order ℝ f (x + c) := by
  have hne : ∀ n, iteratedFDeriv ℝ n (fun y => f (y + c)) x ≠ 0
      ↔ iteratedFDeriv ℝ n f (x + c) ≠ 0 := fun n => by rw [iteratedFDeriv_comp_add_right]
  classical
  unfold order
  split_ifs with h1 h2 h2
  · exact congrArg _ (le_antisymm
      (Nat.find_le ((hne _).mpr (Nat.find_spec h2)))
      (Nat.find_le ((hne _).mp (Nat.find_spec h1))))
  · exact absurd (h1.imp fun n hn => (hne n).mp hn) h2
  · exact absurd (h2.imp fun n hn => (hne n).mpr hn) h1
  · rfl

/-- **Single cluster at a general root `t_j`.** -/
theorem single_cluster_real_delineation_at (m : ℕ) (hm_pos : 0 < m) (t_j : ℝ)
    (Ng : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (hg_deg : ∀ w, (g w).natDegree ≤ Ng)
    (hg_coeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hP_an : AnalyticAt ℝ P 0) (hP_ne : order ℝ P 0 ≠ ⊤)
    (NA NB : ℕ) (A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hA_deg : ∀ w, (A w).natDegree ≤ NA) (hB_deg : ∀ w, (B w).natDegree ≤ NB)
    (hA_coeff : ∀ i, AnalyticAt ℝ (fun w => (A w).coeff i) 0)
    (hB_coeff : ∀ i, AnalyticAt ℝ (fun w => (B w).coeff i) 0)
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w))
    (hP_oi_real : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0)
    (hm_root : (g 0).rootMultiplicity t_j = m)
    (hg_deg_const : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree) :
    ∃ (V : Set (Fin s → ℝ)) (δ : ℝ), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧ 0 < δ ∧
      ∃ (η : (Fin s → ℝ) → ℝ),
        AnalyticOn ℝ η V ∧ η 0 = t_j ∧
        (∀ y ∈ V, |η y - t_j| < δ) ∧
        (∀ y ∈ V, ∀ α : ℝ, (|α - t_j| < δ ∧ (g (y, 0)).IsRoot α) ↔ α = η y) ∧
        (∀ y ∈ V, (g (y, 0)).rootMultiplicity (η y) = m) ∧
        (∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
          order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2) ((y, 0), η y)
            = order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
                ((0, 0), η 0)) := by
  -- shifted family and cofactors
  set gj : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ := fun w => taylor t_j (g w) with hgj
  set Aj : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ := fun w => taylor t_j (A w) with hAj
  set Bj : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ := fun w => taylor t_j (B w) with hBj
  -- hypotheses for the `t=0` result applied to `gj`
  have hgj_deg : ∀ w, (gj w).natDegree ≤ Ng := fun w => by rw [hgj, natDegree_taylor]; exact hg_deg w
  have hgj_coeff : ∀ i, AnalyticAt ℝ (fun w => (gj w).coeff i) 0 :=
    fun i => analyticAt_taylor_coeff Ng g 0 hg_deg hg_coeff t_j i
  have hAj_deg : ∀ w, (Aj w).natDegree ≤ NA := fun w => by rw [hAj, natDegree_taylor]; exact hA_deg w
  have hBj_deg : ∀ w, (Bj w).natDegree ≤ NB := fun w => by rw [hBj, natDegree_taylor]; exact hB_deg w
  have hAj_coeff : ∀ i, AnalyticAt ℝ (fun w => (Aj w).coeff i) 0 :=
    fun i => analyticAt_taylor_coeff NA A 0 hA_deg hA_coeff t_j i
  have hBj_coeff : ∀ i, AnalyticAt ℝ (fun w => (Bj w).coeff i) 0 :=
    fun i => analyticAt_taylor_coeff NB B 0 hB_deg hB_coeff t_j i
  have hmem_j : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = Aj w * gj w + Bj w * derivative (gj w) := by
    filter_upwards [hmem] with w hw
    have h2 := congrArg (fun p : Polynomial ℝ => p.comp (X + C t_j)) hw
    simp only [add_comp, mul_comp, C_comp] at h2
    simp only [hgj, hAj, hBj, taylor_apply]
    rw [show derivative ((g w).comp (X + C t_j)) = (derivative (g w)).comp (X + C t_j) from by
      rw [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul]]
    exact h2
  have hm_root_j : (gj 0).rootMultiplicity 0 = m := by
    rw [hgj, rootMultiplicity_taylor, zero_add]; exact hm_root
  have hgj_deg_const : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (gj (y, 0)).natDegree = (gj 0).natDegree := by
    filter_upwards [hg_deg_const] with y hy
    rw [hgj, natDegree_taylor, natDegree_taylor]; exact hy
  -- apply the `t=0` single-cluster result to `gj`
  obtain ⟨V, δ, hVopen, hV0, hδ, η', hη'_an, hη'0, hη'_ball, hη'_cover, hη'_mult, hη'_oi⟩ :=
    single_cluster_real_delineation m hm_pos Ng gj hgj_deg hgj_coeff P hP_an hP_ne NA NB Aj Bj
      hAj_deg hBj_deg hAj_coeff hBj_coeff hmem_j hP_oi_real hm_root_j hgj_deg_const
  -- shift the conclusion back by `t_j`
  refine ⟨V, δ, hVopen, hV0, hδ, fun y => η' y + t_j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hη'_an.add analyticOn_const
  · show η' 0 + t_j = t_j; rw [hη'0, zero_add]
  · intro y hy; rw [add_sub_cancel_right]; exact hη'_ball y hy
  · intro y hy α
    have hroot_iff : (g (y, 0)).IsRoot α ↔ (gj (y, 0)).IsRoot (α - t_j) := by
      rw [hgj, Polynomial.IsRoot, Polynomial.IsRoot, eval_taylor, sub_add_cancel]
    rw [hroot_iff, show α = η' y + t_j ↔ α - t_j = η' y from ⟨fun h => by rw [h]; ring,
      fun h => by linarith⟩]
    exact hη'_cover y hy (α - t_j)
  · intro y hy
    have hmm := hη'_mult y hy
    simp only [hgj] at hmm
    rw [rootMultiplicity_taylor] at hmm
    exact hmm
  · -- order-invariance, transported from `gj` via the `t`-translation by `t_j`
    have hc : (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (gj q.1).eval q.2)
        = fun q => (fun q' : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q'.1).eval q'.2)
            (q + ((0 : (Fin s → ℝ) × (Fin e → ℝ)), t_j)) := by
      funext q
      simp only [hgj, Prod.fst_add, Prod.snd_add, add_zero]
      rw [eval_taylor]
    have htr : ∀ p : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ,
        order ℝ (fun q => (gj q.1).eval q.2) p
          = order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
              (p + ((0 : (Fin s → ℝ) × (Fin e → ℝ)), t_j)) := by
      intro p; rw [hc]
      exact order_comp_add_right
        (fun q' : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q'.1).eval q'.2)
        ((0 : (Fin s → ℝ) × (Fin e → ℝ)), t_j) p
    filter_upwards [hη'_oi] with y hy
    have e1 : (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η' y + t_j)
        = (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η' y) + ((0 : (Fin s → ℝ) × (Fin e → ℝ)), t_j) := by
      rw [Prod.mk_add_mk, add_zero]
    have e2 : (((0, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η' 0 + t_j)
        = (((0, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η' 0) + ((0 : (Fin s → ℝ) × (Fin e → ℝ)), t_j) := by
      rw [Prod.mk_add_mk, add_zero]
    show order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
        (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η' y + t_j) = _
    rw [e1, e2, ← htr ((y, 0), η' y), ← htr ((0, 0), η' 0)]
    exact hy

/-- **Multi-cluster real delineation (steps 2–3).** The real roots of the section family `g(·,0)`
near `0` form finitely many ordered real-analytic functions (one per distinct real root of `g(0,0)`)
with constant multiplicities. Axiom-clean on `{C, E, A2}`. -/
theorem multi_cluster_real_delineation
    (Ng : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (hg_deg : ∀ w, (g w).natDegree ≤ Ng)
    (hg_coeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    (hg_pos : 0 < (g 0).natDegree)
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hP_an : AnalyticAt ℝ P 0) (hP_ne : order ℝ P 0 ≠ ⊤)
    (NA NB : ℕ) (A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hA_deg : ∀ w, (A w).natDegree ≤ NA) (hB_deg : ∀ w, (B w).natDegree ≤ NB)
    (hA_coeff : ∀ i, AnalyticAt ℝ (fun w => (A w).coeff i) 0)
    (hB_coeff : ∀ i, AnalyticAt ℝ (fun w => (B w).coeff i) 0)
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w))
    (hP_oi_real : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0)
    (hg_deg_const : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree) :
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
  set fam : (Fin s → ℝ) → Polynomial ℝ := fun y => g (y, 0) with hfam
  set d := (g 0).natDegree with hd
  set p := g 0 with hp
  have hp_ne : p ≠ 0 := by
    intro h
    have hdp : (0 : ℕ) < p.natDegree := hg_pos
    rw [h, Polynomial.natDegree_zero] at hdp
    exact absurd hdp (lt_irrefl 0)
  have hfam0 : fam 0 = p := rfl
  have hfam_coeff : ∀ i, AnalyticAt ℝ (fun y => (fam y).coeff i) 0 := fun i =>
    (hg_coeff i).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hdeg_le : ∀ᶠ y in nhds (0 : Fin s → ℝ), (fam y).natDegree ≤ d :=
    hg_deg_const.mono fun y h => h.le
  -- enumerate the distinct real roots of `p = g 0`
  set k := p.roots.toFinset.card with hk_def
  let yiso := p.roots.toFinset.orderIsoOfFin rfl
  let yr : Fin k → ℝ := fun i => ↑(yiso i)
  have hyr_root : ∀ i, p.IsRoot (yr i) := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (yiso i).2)
  have hyr_sorted : StrictMono yr := fun _ _ h => yiso.strictMono h
  have hyr_complete : ∀ z, p.IsRoot z → ∃ i : Fin k, z = yr i := by
    intro z hz
    obtain ⟨i, hi⟩ := yiso.surjective
      ⟨z, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp_ne).mpr hz)⟩
    exact ⟨i, (congr_arg Subtype.val hi).symm⟩
  let mlt : Fin k → ℕ := fun i => p.rootMultiplicity (yr i)
  have hmlt_pos : ∀ i, 0 < mlt i := fun i => (Polynomial.rootMultiplicity_pos hp_ne).mpr (hyr_root i)
  -- per-cluster delineation at each root
  have hcl : ∀ i, ∃ (U : Set (Fin s → ℝ)) (δ : ℝ), IsOpen U ∧ (0 : Fin s → ℝ) ∈ U ∧ 0 < δ ∧
      ∃ (φ : (Fin s → ℝ) → ℝ), AnalyticOn ℝ φ U ∧ φ 0 = yr i ∧
      (∀ y ∈ U, |φ y - yr i| < δ) ∧
      (∀ y ∈ U, ∀ α : ℝ, (|α - yr i| < δ ∧ (g (y, 0)).IsRoot α) ↔ α = φ y) ∧
      (∀ y ∈ U, (g (y, 0)).rootMultiplicity (φ y) = mlt i) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
        order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2) ((y, 0), φ y)
          = order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
              ((0, 0), φ 0)) := fun i =>
    single_cluster_real_delineation_at (mlt i) (hmlt_pos i) (yr i) Ng g hg_deg hg_coeff P hP_an
      hP_ne NA NB A B hA_deg hB_deg hA_coeff hB_coeff hmem hP_oi_real rfl hg_deg_const
  choose Ui δ hUi_open ha₀_Ui hδ_pos φ hφ_an hφ_val hφ_ball hφ_cover hφ_mult hφ_oi using hcl
  -- root / uniqueness in each ball
  have hφ_root : ∀ i, ∀ y ∈ Ui i, (fam y).IsRoot (φ i y) := fun i y hy =>
    ((hφ_cover i y hy (φ i y)).mpr rfl).2
  have hφ_unique : ∀ i, ∀ y ∈ Ui i, ∀ z, (fam y).IsRoot z → |z - yr i| < δ i → z = φ i y :=
    fun i y hy z hroot hball => (hφ_cover i y hy z).mp ⟨hball, hroot⟩
  have hφ_cont : ∀ i, ContinuousAt (φ i) 0 := fun i =>
    (hφ_an i).continuousOn.continuousAt ((hUi_open i).mem_nhds (ha₀_Ui i))
  -- (a) all sections defined
  have h_ift : ∀ᶠ a in nhds (0 : Fin s → ℝ), a ∈ ⋂ i, Ui i :=
    (isOpen_iInter_of_finite fun i => hUi_open i).mem_nhds (Set.mem_iInter.mpr ha₀_Ui)
  -- (b) ordering preserved
  have h_ord : ∀ᶠ a in nhds (0 : Fin s → ℝ), ∀ i j : Fin k, i < j → φ i a < φ j a := by
    simp only [Filter.eventually_all]
    intro i j hij
    exact (((hφ_cont j).sub (hφ_cont i)).eventually
      (Ioi_mem_nhds (sub_pos.mpr (by
        show φ i 0 < φ j 0; rw [hφ_val i, hφ_val j]; exact hyr_sorted hij)))).mono
      fun _ h => sub_pos.mp h
  -- (c) no extra roots: every root lies in some ball
  have h_roots : ∀ᶠ a in nhds (0 : Fin s → ℝ),
      ∀ z, (fam a).IsRoot z → ∃ i : Fin k, z = φ i a := by
    obtain ⟨W, hW_open, hW_mem, hW_cont⟩ := fam_eval_continuousOn fam 0 d hdeg_le hfam_coeff
    let iftBall (i : Fin k) := Set.Ioo (yr i - δ i) (yr i + δ i)
    have hyr_in_ball : ∀ i, yr i ∈ iftBall i := fun i =>
      Set.mem_Ioo.mpr ⟨by linarith [hδ_pos i], by linarith [hδ_pos i]⟩
    let coeffSum := ∑ i ∈ Finset.range d, |p.coeff i|
    let lcAbs := |p.leadingCoeff|
    set R := max (coeffSum / lcAbs + 2)
        (if h : k = 0 then 1 else (Finset.univ.sup'
          ⟨⟨0, Nat.pos_of_ne_zero h⟩, Finset.mem_univ _⟩
          (fun i : Fin k => |yr i| + δ i)) + 1) with hR_def
    have hR_pos : (0 : ℝ) < R := lt_max_of_lt_left (by positivity)
    have hyr_in_R : ∀ i, |yr i| < R := by
      intro i
      have hk_ne : k ≠ 0 := by have := i.isLt; omega
      apply lt_of_lt_of_le _ (le_max_right _ _)
      rw [dif_neg hk_ne]
      have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
        ⟨⟨0, Nat.pos_of_ne_zero hk_ne⟩, Finset.mem_univ _⟩
      calc |yr i| < |yr i| + δ i := by linarith [hδ_pos i]
        _ ≤ Finset.univ.sup' hne (fun j : Fin k => |yr j| + δ j) :=
            Finset.le_sup' (fun j : Fin k => |yr j| + δ j) (Finset.mem_univ i)
        _ < _ + 1 := by linarith
    set Kset := Set.Icc (-R) R \ ⋃ i, iftBall i with hKset
    have hK_compact : IsCompact Kset :=
      (isCompact_Icc).diff (isOpen_iUnion fun i => isOpen_Ioo)
    have hK_no_root : ∀ y ∈ Kset, ¬ p.IsRoot y := by
      intro y ⟨_, hy_not⟩ hroot
      obtain ⟨i, rfl⟩ := hyr_complete y hroot
      exact hy_not (Set.mem_iUnion.mpr ⟨i, hyr_in_ball i⟩)
    have hopen_ne : IsOpen ((W ×ˢ Set.univ) ∩
        (fun pp : (Fin s → ℝ) × ℝ => (fam pp.1).eval pp.2) ⁻¹' {x | x ≠ 0}) :=
      hW_cont.isOpen_inter_preimage (hW_open.prod isOpen_univ) isOpen_ne
    have hprod_sub : {(0 : Fin s → ℝ)} ×ˢ Kset ⊆ (W ×ˢ Set.univ) ∩
        (fun pp : (Fin s → ℝ) × ℝ => (fam pp.1).eval pp.2) ⁻¹' {x | x ≠ 0} := by
      intro ⟨a, y⟩ ⟨ha, hy⟩
      simp only [Set.mem_singleton_iff] at ha; subst ha
      refine ⟨⟨hW_mem, Set.mem_univ _⟩, ?_⟩
      show (fam 0).eval y ≠ 0
      rw [hfam0]; exact hK_no_root y hy
    have h_tube : ∀ᶠ a in nhds (0 : Fin s → ℝ), ∀ y ∈ Kset, (fam a).eval y ≠ 0 := by
      rcases Set.eq_empty_or_nonempty Kset with hKe | hKne
      · exact Filter.Eventually.of_forall fun a y hy =>
          absurd hy (hKe ▸ (Set.mem_empty_iff_false y).mp)
      · obtain ⟨u, v, hu_open, _, ha₀u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton
            hK_compact hopen_ne hprod_sub
        exact Filter.Eventually.mono (hu_open.mem_nhds (Set.singleton_subset_iff.mp ha₀u))
          fun a ha y hy => (huv (Set.mk_mem_prod ha (hKv hy))).2
    have h_bound : ∀ᶠ a in nhds (0 : Fin s → ℝ),
        ∀ z, (fam a).IsRoot z → z ∈ Set.Ioo (-R) R := by
      have hlc_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
      have hlc_eq : (fam 0).coeff d = p.leadingCoeff := by rw [hfam0]; rfl
      let gbnd : (Fin s → ℝ) → ℝ := fun a =>
        (∑ i ∈ Finset.range d, |(fam a).coeff i|) / |(fam a).coeff d| + 1
      have hg_cont : ContinuousAt gbnd 0 := by
        apply ContinuousAt.add _ continuousAt_const
        apply ContinuousAt.div
        · exact tendsto_finset_sum _ fun i _ => (hfam_coeff i).continuousAt.abs
        · exact (hfam_coeff d).continuousAt.abs
        · rw [hlc_eq]; exact abs_ne_zero.mpr hlc_ne
      have hg_val : gbnd 0 = coeffSum / lcAbs + 1 := by
        show (∑ i ∈ Finset.range d, |(fam 0).coeff i|) / |(fam 0).coeff d| + 1 = _
        rw [hlc_eq, hfam0]
      have hg_lt_R : coeffSum / lcAbs + 1 < R := by
        have : coeffSum / lcAbs + 2 ≤ R := le_max_left _ _
        linarith
      have hg_ev : ∀ᶠ a in nhds (0 : Fin s → ℝ), gbnd a < R :=
        hg_cont.eventually (gt_mem_nhds (hg_val ▸ hg_lt_R))
      have hlc_ne' : (fam 0).coeff d ≠ 0 := by rw [hlc_eq]; exact hlc_ne
      have h_lc_ev : ∀ᶠ a in nhds (0 : Fin s → ℝ), (fam a).coeff d ≠ 0 :=
        (hfam_coeff d).continuousAt.eventually (isOpen_ne.mem_nhds hlc_ne')
      filter_upwards [hg_ev, h_lc_ev, hdeg_le] with a hga ha_lc ha_deg z hroot
      have hfa_ne : fam a ≠ 0 := fun h => ha_lc (by rw [h]; simp)
      have hcb := hroot.norm_lt_cauchyBound hfa_ne
      have hd_eq : (fam a).natDegree = d := le_antisymm ha_deg (by
        by_contra hlt; push_neg at hlt
        exact ha_lc (Polynomial.coeff_eq_zero_of_natDegree_lt hlt))
      have hcb_le : (Polynomial.cauchyBound (fam a) : ℝ) ≤ gbnd a := by
        have hcb_nn : Polynomial.cauchyBound (fam a) ≤
            (∑ i ∈ Finset.range d, ‖(fam a).coeff i‖₊) / ‖(fam a).leadingCoeff‖₊ + 1 := by
          simp only [Polynomial.cauchyBound, hd_eq]
          gcongr
          exact Finset.sup_le fun i hi =>
            Finset.single_le_sum (f := fun i => ‖(fam a).coeff i‖₊) (fun _ _ => zero_le _) hi
        calc (↑(Polynomial.cauchyBound (fam a)) : ℝ)
            ≤ ↑((∑ i ∈ Finset.range d, ‖(fam a).coeff i‖₊) /
                ‖(fam a).leadingCoeff‖₊ + 1) := by exact_mod_cast hcb_nn
          _ = gbnd a := by
              simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
              have hlc : (↑‖(fam a).leadingCoeff‖₊ : ℝ) = |(fam a).coeff d| := by
                have hlc' : (fam a).leadingCoeff = (fam a).coeff d := by
                  show (fam a).coeff (fam a).natDegree = (fam a).coeff d; rw [hd_eq]
                rw [hlc', coe_nnnorm, Real.norm_eq_abs]
              have hnum : (∑ i ∈ Finset.range d, (↑‖(fam a).coeff i‖₊ : ℝ)) =
                  ∑ i ∈ Finset.range d, |(fam a).coeff i| :=
                Finset.sum_congr rfl fun i _ => by rw [coe_nnnorm, Real.norm_eq_abs]
              show (∑ i ∈ Finset.range d, (↑‖(fam a).coeff i‖₊ : ℝ)) /
                  ↑‖(fam a).leadingCoeff‖₊ + 1
                = (∑ i ∈ Finset.range d, |(fam a).coeff i|) / |(fam a).coeff d| + 1
              rw [hnum, hlc]
      have hz_lt : |z| < R := calc
        |z| = ↑‖z‖₊ := by simp [coe_nnnorm, Real.norm_eq_abs]
        _ < ↑(Polynomial.cauchyBound (fam a)) := by exact_mod_cast hcb
        _ ≤ gbnd a := hcb_le
        _ < R := hga
      exact Set.mem_Ioo.mpr (abs_lt.mp hz_lt)
    exact (h_ift.and (h_tube.and h_bound)).mono fun a ⟨ha_ift, ha_tube, ha_bound⟩ z hroot => by
      have hz_R := ha_bound z hroot
      have hz_Icc : z ∈ Set.Icc (-R) R := Set.Ioo_subset_Icc_self hz_R
      have hz_not_K : z ∉ Kset := fun hzK => ha_tube z hzK hroot
      have hz_ball : ∃ i, z ∈ iftBall i := by
        by_contra h; push_neg at h
        exact hz_not_K ⟨hz_Icc, fun hmem => let ⟨i, hi⟩ := Set.mem_iUnion.mp hmem; h i hi⟩
      obtain ⟨i, hi⟩ := hz_ball
      refine ⟨i, hφ_unique i a (Set.mem_iInter.mp ha_ift i) z hroot ?_⟩
      simp only [iftBall, Set.mem_Ioo] at hi
      rw [abs_sub_lt_iff]; constructor <;> linarith [hi.1, hi.2]
  -- assemble
  obtain ⟨V, hV_sub, hV_open, ha₀_V⟩ :=
    mem_nhds_iff.mp (h_ift.and (h_ord.and h_roots))
  refine ⟨V, hV_open, ha₀_V, k, φ, mlt, ?_, ?_, ?_, hmlt_pos, ?_, fun i => hφ_oi i⟩
  · intro i; exact (hφ_an i).mono fun a ha => Set.mem_iInter.mp (hV_sub ha).1 i
  · intro a haV i j hij; exact (hV_sub haV).2.1 i j hij
  · intro a haV z
    exact ⟨(hV_sub haV).2.2 z, fun ⟨i, hi⟩ => hi ▸ hφ_root i a (Set.mem_iInter.mp (hV_sub haV).1 i)⟩
  · intro a haV i
    exact hφ_mult i a (Set.mem_iInter.mp (hV_sub haV).1 i)

end
