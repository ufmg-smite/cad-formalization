import Cad.Multivariate.ProjectionTheorem.Generalized.ClusterFromReal
import Cad.Multivariate.ProjectionTheorem.Generalized.A2Recovery

/-!
# F3 — single-cluster real delineation (the `{C, E}` milestone)

`single_cluster_real_delineation` wires the full per-cluster chain on `{C, E}`: it runs
`cluster_from_real` (Weierstrass + Zariski 4.1.1), which produces the **single** holomorphic branch
`ξ` of the cluster (the unique root, nonsplitting) together with the real-slice covering and
multiplicity, and then finishes with the **proved** recovery core
`real_delineation_of_single_branch` (`A2Recovery.lean`, 0 custom axioms) to obtain the **real** root
delineation of the section family `g(·,0)` near `0`. No separate real-analysis axiom is needed: the
no-splitting is part of Zariski's Theorem 4.1.1, and the real recovery is proved.

The remaining work for the full theorem is the multi-cluster assembly (enumerate `g(0,0)`'s real
roots, translate each to `0`, apply this, and glue).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **Single cluster, real (on `{C, E, A2}`).** From the real product family `g` localized at a
multiplicity-`m` cluster root of `g(0,0)` at `t = 0` (with witness `P`, cofactors `A,B`, and section
degree constancy), the real roots of the section family `g(·,0)` near `0` form finitely many ordered
real-analytic functions with constant multiplicities. -/
theorem single_cluster_real_delineation (m : ℕ) (hm_pos : 0 < m)
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
    (hm_root : (g 0).rootMultiplicity 0 = m)
    (hg_deg_const : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree) :
    ∃ (V : Set (Fin s → ℝ)) (δ : ℝ), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧ 0 < δ ∧
      ∃ (η : (Fin s → ℝ) → ℝ),
        AnalyticOn ℝ η V ∧ η 0 = 0 ∧
        (∀ y ∈ V, |η y| < δ) ∧
        (∀ y ∈ V, ∀ α : ℝ, (|α| < δ ∧ (g (y, 0)).IsRoot α) ↔ α = η y) ∧
        (∀ y ∈ V, (g (y, 0)).rootMultiplicity (η y) = m) ∧
        (∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
          order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2) ((y, 0), η y)
            = order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2)
                ((0, 0), η 0)) := by
  -- `cluster_from_real` (C + Zariski 4.1.1) gives the single holomorphic branch `ξ` of the cluster,
  -- real-valued on the slice; the proved recovery core turns it into the real-analytic delineation.
  obtain ⟨ξ, δ₀, hξ_an, hξ0, hδ₀, hξ_cover, hξ_mult, F_ℂ, hFℂ_an0, hagree_F, hcoi⟩ :=
    cluster_from_real m hm_pos Ng g hg_deg hg_coeff P hP_an hP_ne NA NB A B hA_deg hB_deg
      hA_coeff hB_coeff hmem hP_oi_real hm_root hg_deg_const
  obtain ⟨V, δ, hVopen, hV0, hδ, η, hη_an, hη0, hη_ball, hη_cover, hη_mult, hη_real⟩ :=
    real_delineation_of_single_branch (fun y => g (y, 0)) m ξ hξ_an hξ0 δ₀ hδ₀
      hξ_cover hξ_mult
  refine ⟨V, δ, hVopen, hV0, hδ, η, hη_an, hη0, hη_ball, hη_cover, hη_mult, ?_⟩
  -- order-invariance via `section_orderinv_of_complex`, using `cluster_from_real`'s complexification
  set G : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ → ℝ := fun q => (g q.1).eval q.2 with hG
  have hη_cont : ContinuousAt η 0 := (hη_an.analyticAt (hVopen.mem_nhds hV0)).continuousAt
  -- `G` analytic at `0` (polynomial family with analytic coefficients, degree `≤ Ng`)
  have hG_an0 : AnalyticAt ℝ G 0 := by
    have hsum : AnalyticAt ℝ
        (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ =>
          ∑ i ∈ Finset.range (Ng + 1), (g q.1).coeff i * q.2 ^ i) 0 := by
      apply Finset.analyticAt_fun_sum; intro i _
      exact ((hg_coeff i).comp_of_eq analyticAt_fst rfl).mul (analyticAt_snd.pow i)
    refine hsum.congr (Filter.Eventually.of_forall fun q => ?_)
    exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hg_deg q.1)) q.2).symm
  -- branch-point maps tending to `0`
  have hofReal_cont : Continuous (fun y : Fin s → ℝ => (Complex.ofReal ∘ y : Fin s → ℂ)) :=
    continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))
  have hbp : Filter.Tendsto (fun y : Fin s → ℝ => (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η y))
      (𝓝 0) (𝓝 0) := by
    have h0 : (((0, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η 0) = 0 := by simp [hη0]
    have hc : ContinuousAt (fun y : Fin s → ℝ => (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η y)) 0 :=
      ((by fun_prop : ContinuousAt
        (fun y : Fin s → ℝ => ((y, 0) : (Fin s → ℝ) × (Fin e → ℝ))) 0)).prodMk hη_cont
    have := hc.tendsto; rwa [h0] at this
  have hbpℂ : Filter.Tendsto
      (fun y : Fin s → ℝ => ((Complex.ofReal ∘ y, (0 : Fin e → ℂ)), (↑(η y) : ℂ)))
      (𝓝 0) (𝓝 0) := by
    have h0 : ((Complex.ofReal ∘ (0 : Fin s → ℝ), (0 : Fin e → ℂ)), (↑(η 0) : ℂ)) = 0 := by
      simp [hη0, ofReal_comp_zero]
    have hc : ContinuousAt
        (fun y : Fin s → ℝ => ((Complex.ofReal ∘ y, (0 : Fin e → ℂ)), (↑(η y) : ℂ))) 0 :=
      ((hofReal_cont.continuousAt).prodMk continuousAt_const).prodMk
        (Complex.continuous_ofReal.continuousAt.comp hη_cont)
    have := hc.tendsto; rwa [h0] at this
  -- the three hypotheses of `section_orderinv_of_complex`
  have hreal : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (↑(η y) : ℂ) = ξ (Complex.ofReal ∘ y) := by
    filter_upwards [hVopen.mem_nhds hV0] with y hy
    rw [hη_real y hy, realEmbedding_apply]
  have hG_an : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), AnalyticAt ℝ G ((y, 0), η y) :=
    hbp.eventually hG_an0.eventually_analyticAt
  have hFℂ_an : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      AnalyticAt ℂ F_ℂ ((Complex.ofReal ∘ y, (0 : Fin e → ℂ)), (↑(η y) : ℂ)) :=
    hbpℂ.eventually hFℂ_an0.eventually_analyticAt
  have hagree : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      ∀ᶠ x in 𝓝 (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η y),
        F_ℂ ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2), (x.2 : ℂ)) = ↑(G x) := by
    obtain ⟨U, hUsub, hUopen, hU0⟩ := eventually_nhds_iff.mp hagree_F
    filter_upwards [hbp.eventually (hUopen.mem_nhds hU0)] with y hyU
    filter_upwards [hUopen.mem_nhds hyU] with x hx
    exact hUsub x hx
  exact section_orderinv_of_complex G F_ℂ ξ hξ0 η hη0 hcoi hreal hG_an hFℂ_an hagree

end
