import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassCount
import Cad.Multivariate.ProjectionTheorem.Generalized.ShiftCluster
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# M2 — Rouché cluster separation (thesis Theorem 4.2.2, step 4)

This file is the **complex** analogue of `multi_cluster_real_delineation`
(`Mccalum/Generalized/MultiCluster.lean`): the bivariate root-continuity input to the
homotopy-deformation contradiction. Fix the section coordinates and let the transverse coordinate
`w` vary; the family of monic polynomials `P : ℂ → ℂ[X]` has the section polynomial `P 0` with
distinct roots `α₁,…,α_l` (multiplicities `m₁,…,m_l`). The thesis chooses disjoint discs `Dⱼ` about
the `αⱼ` and a transverse disc `D'` about `0` such that, for every transverse value `w ∈ D'`, exactly
`mⱼ` roots of `P w` lie in `Dⱼ`. We prove the two facts the monodromy contradiction (`M4`,
`monodromy_exchange_contradiction`) actually consumes:

* **confinement** — for `w` near `0`, *every* root of `P w` lies in `⋃ⱼ Dⱼ` (the deformed loop's lift
  stays in the disjoint union of discs);
* **non-emptiness** — for `w` near `0`, *each* `Dⱼ` still contains a root of `P w` (so the exchanged
  roots `α ∈ D₁`, `β ∈ D₂` exist at the off-section base point).

Confinement is the soft tube-lemma + `cauchyBound` argument ported from `multi_cluster`. Non-emptiness
is the genuine degree-theoretic content: it uses the argument principle — the contour root count
`(2πi)⁻¹∮_{∂Dⱼ} P'/P` is analytic in `w` (the project's keystone, via `powerSum_analyticAt`) and
integer-valued (`slice_powerSum_eq_rootSum`), hence locally constant, and equals `mⱼ ≥ 1` at `w = 0`.
-/

noncomputable section

open Polynomial Filter Complex Metric
open scoped Topology Real

namespace RoucheSeparation

/-- **Joint continuity of evaluation** for a complex analytic family (the `ℂ`-analogue of
`fam_eval_continuousOn`). -/
lemma fam_eval_continuousOn_C (P : ℂ → Polynomial ℂ) (w₀ : ℂ) (d : ℕ)
    (hdeg : ∀ᶠ w in 𝓝 w₀, (P w).natDegree ≤ d)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun w => (P w).coeff i) w₀) :
    ∃ W : Set ℂ, IsOpen W ∧ w₀ ∈ W ∧
      ContinuousOn (fun p : ℂ × ℂ => (P p.1).eval p.2) (W ×ˢ Set.univ) := by
  have hcoeff_nbhd : ∀ i, ∃ W : Set ℂ, IsOpen W ∧ w₀ ∈ W ∧
      ContinuousOn (fun w => (P w).coeff i) W := fun i => by
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ :=
      _root_.eventually_nhds_iff.mp (hcoeff i).eventually_analyticAt
    exact ⟨W, hW_open, hW_mem, fun w hw => (hW_sub w hw).continuousAt.continuousWithinAt⟩
  choose Wc hWc_open hWc_mem hWc_cont using hcoeff_nbhd
  obtain ⟨Wd, hWd_sub, hWd_open, hWd_mem⟩ := _root_.eventually_nhds_iff.mp hdeg
  refine ⟨Wd ∩ ⋂ i ∈ Finset.range (d + 1), Wc i,
    hWd_open.inter (isOpen_biInter_finset fun i _ => hWc_open i),
    ⟨hWd_mem, Set.mem_iInter₂.mpr fun i _ => hWc_mem i⟩, ?_⟩
  have hsum_cont : ContinuousOn
      (fun p : ℂ × ℂ => ∑ i ∈ Finset.range (d + 1), (P p.1).coeff i * p.2 ^ i)
      ((Wd ∩ ⋂ i ∈ Finset.range (d + 1), Wc i) ×ˢ Set.univ) := by
    apply continuousOn_finset_sum
    intro i hi
    apply ContinuousOn.mul _ (continuous_snd.continuousOn.pow i)
    exact (hWc_cont i).comp continuous_fst.continuousOn
      (fun p hp => (Set.mem_iInter₂.mp hp.1.2) i hi)
  exact hsum_cont.congr fun p hp =>
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hWd_sub p.1 hp.1.1)) p.2

/-- **The analytic order of a polynomial slice is the root multiplicity.** For `p ≠ 0`,
`analyticOrderAt (p.eval ·) a = p.rootMultiplicity a`. -/
lemma analyticOrderAt_eval_eq_rootMultiplicity (p : Polynomial ℂ) (hp : p ≠ 0) (a : ℂ) :
    analyticOrderAt (fun z => p.eval z) a = (p.rootMultiplicity a : ℕ∞) := by
  obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  set k := p.rootMultiplicity a with hk
  have hqa : q.eval a ≠ 0 := by
    have h := Polynomial.dvd_iff_isRoot.not.mp hq_ndvd
    rwa [Polynomial.IsRoot.def] at h
  have han : AnalyticAt ℂ (fun z => p.eval z) a := (p.differentiable (𝕜 := ℂ)).analyticAt a
  rw [han.analyticOrderAt_eq_natCast]
  refine ⟨fun z => q.eval z, (q.differentiable (𝕜 := ℂ)).analyticAt a, hqa, ?_⟩
  filter_upwards with z
  have : p.eval z = (z - a) ^ k * q.eval z := by
    conv_lhs => rw [hq_eq]
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [this, smul_eq_mul]

/-- **Confinement (soft half of M2).** For a monic complex family with analytic coefficients, every
root of `P w` lies, for `w` near `0`, within `ρ` of some distinct root of the section polynomial
`P 0`. Ported from the real `multi_cluster_real_delineation` (tube lemma + `cauchyBound`). -/
lemma roots_confined (P : ℂ → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ w, (P w).Monic) (hdeg : ∀ w, (P w).natDegree = m)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun w => (P w).coeff i) 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ w in 𝓝 (0 : ℂ), ∀ t, (P w).IsRoot t → ∃ α ∈ (P 0).roots.toFinset, t ∈ ball α ρ := by
  classical
  set p := P 0 with hp
  have hp_ne : p ≠ 0 := (hmonic 0).ne_zero
  set S := p.roots.toFinset with hS
  have hcoeff_m_one : ∀ w, (P w).coeff m = 1 := fun w => by
    have := (hmonic w).coeff_natDegree; rwa [hdeg w] at this
  have hdeg_le : ∀ᶠ w in 𝓝 (0 : ℂ), (P w).natDegree ≤ m :=
    Filter.Eventually.of_forall fun w => (hdeg w).le
  -- joint continuity of evaluation near `0`
  obtain ⟨W, hW_open, hW_mem, hW_cont⟩ := fam_eval_continuousOn_C P 0 m hdeg_le hcoeff
  -- the union of discs around the distinct roots
  set U := ⋃ α ∈ S, ball α ρ with hU
  have hU_open : IsOpen U := isOpen_biUnion fun α _ => isOpen_ball
  -- a radius `R` bounding all roots near `0`
  set coeffSum : ℝ := ∑ i ∈ Finset.range m, ‖p.coeff i‖ with hcoeffSum
  set R : ℝ := coeffSum + 2 with hR_def
  have hR_pos : (0 : ℝ) < R := by positivity
  set Kset := closedBall (0 : ℂ) R \ U with hKset
  have hK_compact : IsCompact Kset := (isCompact_closedBall _ _).diff hU_open
  have hK_no_root : ∀ y ∈ Kset, ¬ p.IsRoot y := by
    intro y ⟨_, hy_not⟩ hroot
    exact hy_not (Set.mem_biUnion (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp_ne).mpr hroot))
      (mem_ball_self hρ))
  -- (tube) no root of `P w` on `Kset`, for `w` near `0`
  have hopen_ne : IsOpen ((W ×ˢ Set.univ) ∩
      (fun pp : ℂ × ℂ => (P pp.1).eval pp.2) ⁻¹' {x | x ≠ 0}) :=
    hW_cont.isOpen_inter_preimage (hW_open.prod isOpen_univ) isOpen_ne
  have hprod_sub : {(0 : ℂ)} ×ˢ Kset ⊆ (W ×ˢ Set.univ) ∩
      (fun pp : ℂ × ℂ => (P pp.1).eval pp.2) ⁻¹' {x | x ≠ 0} := by
    intro ⟨a, y⟩ ⟨ha, hy⟩
    simp only [Set.mem_singleton_iff] at ha; subst ha
    refine ⟨⟨hW_mem, Set.mem_univ _⟩, ?_⟩
    show (P 0).eval y ≠ 0
    exact hK_no_root y hy
  have h_tube : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ y ∈ Kset, (P w).eval y ≠ 0 := by
    rcases Set.eq_empty_or_nonempty Kset with hKe | hKne
    · exact Filter.Eventually.of_forall fun a y hy =>
        absurd hy (hKe ▸ (Set.mem_empty_iff_false y).mp)
    · obtain ⟨u, v, hu_open, _, ha₀u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton
          hK_compact hopen_ne hprod_sub
      exact Filter.Eventually.mono (hu_open.mem_nhds (Set.singleton_subset_iff.mp ha₀u))
        fun a ha y hy => (huv (Set.mk_mem_prod ha (hKv hy))).2
  -- (bound) roots of `P w` lie in `ball 0 R`, for `w` near `0`
  have h_bound : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ t, (P w).IsRoot t → ‖t‖ < R := by
    set gbnd : ℂ → ℝ := fun w => (∑ i ∈ Finset.range m, ‖(P w).coeff i‖) + 1 with hgbnd
    have hg_cont : ContinuousAt gbnd 0 :=
      (tendsto_finset_sum _ fun i _ => (hcoeff i).continuousAt.norm).add continuousAt_const
    have hg_val : gbnd 0 = coeffSum + 1 := rfl
    have hg_lt_R : coeffSum + 1 < R := by rw [hR_def]; linarith
    have hg_ev : ∀ᶠ w in 𝓝 (0 : ℂ), gbnd w < R :=
      hg_cont.eventually (gt_mem_nhds (hg_val ▸ hg_lt_R))
    filter_upwards [hg_ev] with w hgw t hroot
    have hfw_ne : P w ≠ 0 := (hmonic w).ne_zero
    have hcb := hroot.norm_lt_cauchyBound hfw_ne
    -- `cauchyBound (P w) ≤ gbnd w`
    have hcb_le : (Polynomial.cauchyBound (P w) : ℝ) ≤ gbnd w := by
      have hlc : ‖(P w).leadingCoeff‖₊ = 1 := by
        rw [Polynomial.leadingCoeff, hdeg w, hcoeff_m_one w]; simp
      have hsup_le : Finset.sup (Finset.range m) (‖(P w).coeff ·‖₊)
          ≤ ∑ i ∈ Finset.range m, ‖(P w).coeff i‖₊ :=
        Finset.sup_le fun i hi => Finset.single_le_sum (f := fun i => ‖(P w).coeff i‖₊)
          (fun _ _ => zero_le _) hi
      calc (Polynomial.cauchyBound (P w) : ℝ)
          = ↑(Finset.sup (Finset.range m) (‖(P w).coeff ·‖₊)) + 1 := by
            rw [Polynomial.cauchyBound, hdeg w, hlc]; push_cast; ring
        _ ≤ ↑(∑ i ∈ Finset.range m, ‖(P w).coeff i‖₊) + 1 := by
            have := NNReal.coe_le_coe.mpr hsup_le; linarith
        _ = gbnd w := by rw [hgbnd]; simp only [NNReal.coe_sum, coe_nnnorm]
    have : (‖t‖₊ : ℝ) < gbnd w := lt_of_lt_of_le (by exact_mod_cast hcb) hcb_le
    calc ‖t‖ = (‖t‖₊ : ℝ) := rfl
      _ < gbnd w := this
      _ < R := hgw
  -- assemble
  filter_upwards [h_tube, h_bound] with w hw_tube hw_bound t hroot
  have ht_R : ‖t‖ < R := hw_bound t hroot
  have ht_cb : t ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]; exact ht_R.le
  have ht_not_K : t ∉ Kset := fun htK => hw_tube t htK hroot
  have ht_U : t ∈ U := by
    by_contra htU
    exact ht_not_K ⟨ht_cb, htU⟩
  obtain ⟨α, hαS, htα⟩ := Set.mem_iUnion₂.mp ht_U
  exact ⟨α, hαS, htα⟩

/-- **Continuous + integer-valued ⟹ locally constant** (restated from `CWeierstrassCount`, where it is
`private`). -/
private lemma eventually_nat_eq_of_continuousAt {X : Type*} [TopologicalSpace X] {x₀ : X}
    {f : X → ℂ} {N : X → ℕ} (hf : ContinuousAt f x₀)
    (heq : ∀ᶠ x in 𝓝 x₀, f x = (N x : ℂ)) : ∀ᶠ x in 𝓝 x₀, N x = N x₀ := by
  have hfx₀ : f x₀ = (N x₀ : ℂ) := heq.self_of_nhds
  have hclose : ∀ᶠ x in 𝓝 x₀, dist (f x) (f x₀) < 1 :=
    Metric.tendsto_nhds.mp hf.tendsto 1 one_pos
  filter_upwards [heq, hclose] with x hx hd
  rw [dist_eq_norm, hx, hfx₀] at hd
  have hreal : |((N x : ℤ) - (N x₀ : ℤ) : ℝ)| < 1 := by
    have e : ((N x : ℂ) - (N x₀ : ℂ)) = (((N x : ℤ) - (N x₀ : ℤ) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hd; exact hd
  have hint : |((N x : ℤ) - (N x₀ : ℤ))| < 1 := by exact_mod_cast hreal
  rcases abs_lt.mp hint with ⟨h1, h2⟩
  omega

/-- The transverse parameter as the single coordinate of `CParam 0 1` (`(Fin 0 → ℂ) × (Fin 1 → ℂ)`),
packaged as a continuous linear map so the `Layer-C` threading lemmas (stated over `CParam`) apply. -/
private def transL : CParam 0 1 →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ (Fin 0 → ℂ) (Fin 1 → ℂ))

private def transι (w : ℂ) : CParam 0 1 := ((0 : Fin 0 → ℂ), fun _ => w)

@[simp] private lemma transL_ι (w : ℂ) : transL (transι w) = w := by
  simp [transL, transι, ContinuousLinearMap.proj]

@[simp] private lemma transL_zero : transL (0 : CParam 0 1) = 0 := map_zero _

private lemma continuous_transι : Continuous transι := by
  unfold transι; fun_prop

/-- **Non-emptiness (degree-theoretic half of M2).** If `α` is a root of the section polynomial `P 0`,
the circle `∂(ball α ρ)` carries no root of `P 0`, `α` is the *only* root of `P 0` in `closedBall α R₁`,
and (for `w` near `0`) the roots of `P w` in `closedBall α R₁` stay inside `ball α ρ`, then for `w` near
`0` the disc `ball α ρ` still contains a root of `P w`. The argument principle: the contour root count
`(2πi)⁻¹∮_{|t|=ρ} ∂ₜG/G` is analytic in `w` (`powerSum_analyticAt`) and integer-valued
(`slice_powerSum_eq_rootSum`), hence locally constant, and equals `(P 0).rootMultiplicity α ≥ 1` at
`w = 0`. -/
lemma disc_roots_nonempty (P : ℂ → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ w, (P w).Monic) (hdeg : ∀ w, (P w).natDegree = m)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun w => (P w).coeff i) 0)
    (α : ℂ) (hαroot : (P 0).IsRoot α)
    {ρ R₁ : ℝ} (hρ : 0 < ρ) (hρR₁ : ρ < R₁)
    (hsphere0 : ∀ ζ ∈ sphere α ρ, ¬ (P 0).IsRoot ζ)
    (hsupp_ev : ∀ᶠ w in 𝓝 (0 : ℂ),
      ∀ t, (P w).IsRoot t → t ∈ closedBall α R₁ → t ∈ ball α ρ) :
    ∀ᶠ w in 𝓝 (0 : ℂ), ∃ t, (P w).IsRoot t ∧ t ∈ ball α ρ := by
  classical
  have hp_ne : P 0 ≠ 0 := (hmonic 0).ne_zero
  set mult : ℕ := (P 0).rootMultiplicity α with hmult
  have hmult_pos : 0 < mult := (Polynomial.rootMultiplicity_pos hp_ne).mpr hαroot
  -- the joint family over the transverse parameter, packaged for the threading lemmas
  set G : CParam 0 1 × ℂ → ℂ := fun zt => (P (transL zt.1)).eval (zt.2 + α) with hG_def
  -- `G` as a finite sum, for analyticity
  have hGeq : G = fun zt : CParam 0 1 × ℂ =>
      ∑ i ∈ Finset.range (m + 1), (P (transL zt.1)).coeff i * (zt.2 + α) ^ i := by
    rw [hG_def]; funext zt
    exact Polynomial.eval_eq_sum_range' (by rw [hdeg]; omega) _
  -- joint analyticity of `G` wherever the coefficients are analytic at `transL z`
  have hGan_at : ∀ (z : CParam 0 1) (t : ℂ),
      (∀ i ∈ Finset.range (m + 1), AnalyticAt ℂ (fun w => (P w).coeff i) (transL z)) →
      AnalyticAt ℂ G (z, t) := by
    intro z t hc
    rw [hGeq]
    apply Finset.analyticAt_fun_sum
    intro i hi
    have hinner : AnalyticAt ℂ (fun zt : CParam 0 1 × ℂ => transL zt.1) (z, t) :=
      (transL.analyticAt z).comp analyticAt_fst
    have h1 : AnalyticAt ℂ (fun zt : CParam 0 1 × ℂ => (P (transL zt.1)).coeff i) (z, t) :=
      AnalyticAt.comp (g := fun w => (P w).coeff i)
        (f := fun zt : CParam 0 1 × ℂ => transL zt.1) (hc i hi) hinner
    exact h1.mul ((analyticAt_snd.add analyticAt_const).pow i)
  -- the eventual set (over the transverse parameter) on which the coefficients are analytic
  have hcoeff_ev : ∀ᶠ z in 𝓝 (0 : CParam 0 1),
      ∀ i ∈ Finset.range (m + 1), AnalyticAt ℂ (fun w => (P w).coeff i) (transL z) := by
    refine Filter.eventually_all_finset _ |>.mpr fun i _ => ?_
    have hTlam : Filter.Tendsto transL (𝓝 (0 : CParam 0 1)) (𝓝 (0 : ℂ)) :=
      transL_zero ▸ transL.continuous.continuousAt
    exact hTlam.eventually (hcoeff i).eventually_analyticAt
  -- the slice family at `transL z = 0` is the Taylor shift of `P 0`
  have hslice0 : (fun t => G (0, t)) = fun t => (taylor α (P 0)).eval t := by
    funext t; simp only [hG_def, transL_zero, eval_taylor]
  -- analyticity of the parametrized root count (`R = ρ`, `k = 0`)
  have hG0_sph : ∀ ζ ∈ sphere (0 : ℂ) ρ, G (0, ζ) ≠ 0 := by
    intro ζ hζ
    show (P (transL 0)).eval (ζ + α) ≠ 0
    rw [transL_zero]
    intro h
    refine hsphere0 (ζ + α) ?_ h
    rw [mem_sphere_iff_norm, show ζ + α - α = ζ by ring, ← mem_sphere_zero_iff_norm]; exact hζ
  have hGan_sph : ∀ ζ ∈ sphere (0 : ℂ) ρ, AnalyticAt ℂ G (0, ζ) := fun ζ _ =>
    hGan_at 0 ζ (fun i _ => by rw [transL_zero]; exact hcoeff i)
  have hI_an : AnalyticAt ℂ
      (fun z : CParam 0 1 =>
        (2 * π * I)⁻¹ * ∮ ζ in C(0, ρ), ζ ^ (0 : ℕ) * fderiv ℂ G (z, ζ) (0, 1) / G (z, ζ)) 0 :=
    powerSum_analyticAt G hρ 0 hGan_sph hG0_sph
  -- the integer-valued count
  set N : CParam 0 1 → ℕ := fun z =>
    ∑ a ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset,
      (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) a).toNat with hN_def
  -- `G`-slice is entire (a polynomial), so analytic on the closed ball
  have hslice_an : ∀ z : CParam 0 1, AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall 0 R₁) := by
    intro z t _
    have he : (fun t => G (z, t)) = fun t : ℂ => (P (transL z)).eval (t + α) := by
      funext t; rw [hG_def]
    rw [he]
    exact (((P (transL z)).differentiable (𝕜 := ℂ)).comp
      (differentiable_id.add_const α)).analyticAt t
  -- monic ⟹ slices are nonzero polynomials, so attain a nonzero value on the ball
  have hslice_ne : ∀ z : CParam 0 1, ∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0 := by
    intro z
    have hball_inf : (closedBall (0 : ℂ) R₁).Infinite :=
      infinite_of_mem_nhds (0 : ℂ) (closedBall_mem_nhds 0 (lt_trans hρ hρR₁))
    by_contra h
    push_neg at h
    have hcomp0 : (P (transL z)).comp (X + C α) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply hball_inf.mono
      intro t ht
      show ((P (transL z)).comp (X + C α)).IsRoot t
      rw [Polynomial.IsRoot.def, eval_comp, eval_add, eval_X, eval_C]
      simpa only [hG_def] using h t ht
    have hmoniccomp : ((P (transL z)).comp (X + C α)).Monic := by
      rw [show (X + C α : Polynomial ℂ) = X - C (-α) by rw [map_neg, sub_neg_eq_add]]
      exact (hmonic (transL z)).comp_X_sub_C (-α)
    exact hmoniccomp.ne_zero hcomp0
  -- roots stay confined to `ball α ρ` near the central transverse parameter
  have hconf_z : ∀ᶠ z in 𝓝 (0 : CParam 0 1),
      ∀ t, (P (transL z)).IsRoot t → t ∈ closedBall α R₁ → t ∈ ball α ρ := by
    have hTlam : Filter.Tendsto transL (𝓝 (0 : CParam 0 1)) (𝓝 (0 : ℂ)) :=
      transL_zero ▸ transL.continuous.continuousAt
    exact hTlam.eventually hsupp_ev
  -- the contour count equals the integer `N z` near `0`
  have heq : ∀ᶠ z in 𝓝 (0 : CParam 0 1),
      (2 * π * I)⁻¹ * ∮ ζ in C(0, ρ), ζ ^ (0 : ℕ) * fderiv ℂ G (z, ζ) (0, 1) / G (z, ζ)
        = (N z : ℂ) := by
    filter_upwards [hcoeff_ev, hconf_z] with z hcz hconfz
    have hGdiff : ∀ t ∈ closedBall (0 : ℂ) R₁, DifferentiableAt ℂ G (z, t) :=
      fun t _ => (hGan_at z t hcz).differentiableAt
    have hsupp : ∀ a ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support,
        a ∈ ball (0 : ℂ) ρ := by
      intro a ha
      have hamem : a ∈ closedBall (0 : ℂ) R₁ :=
        (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).supportWithinDomain ha
      have hGa : G (z, a) = 0 := by
        by_contra hGa; exact ha (divisor_eq_zero_of_ne (hslice_an z) hamem hGa)
      have hroot : (P (transL z)).IsRoot (a + α) := by
        rw [Polynomial.IsRoot.def]; simpa only [hG_def] using hGa
      have hmemα : (a + α) ∈ closedBall α R₁ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        rw [mem_closedBall, dist_zero_right] at hamem; exact hamem
      have hball := hconfz (a + α) hroot hmemα
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at hball
      rw [mem_ball, dist_zero_right]; exact hball
    rw [slice_powerSum_eq_rootSum hρ hρR₁ (hslice_an z) hGdiff (hslice_ne z) hsupp 0, hN_def]
    push_cast
    exact Finset.sum_congr rfl fun a _ => by rw [pow_zero, mul_one]
  -- continuity + integer values ⟹ `N` locally constant
  have hNconst : ∀ᶠ z in 𝓝 (0 : CParam 0 1), N z = N 0 :=
    eventually_nat_eq_of_continuousAt hI_an.continuousAt heq
  -- `N 0 = (P 0).rootMultiplicity α ≥ 1`
  have hN0_pos : 1 ≤ N 0 := by
    have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R₁ := by
      rw [mem_closedBall, dist_self]; exact (lt_trans hρ hρR₁).le
    have htaylor_ne : taylor α (P 0) ≠ 0 := by
      rw [taylor_apply, show (X + C α : Polynomial ℂ) = X - C (-α) by rw [map_neg, sub_neg_eq_add]]
      exact ((hmonic 0).comp_X_sub_C (-α)).ne_zero
    have hord : analyticOrderAt (fun t => G (0, t)) 0 = (mult : ℕ∞) := by
      rw [hslice0, analyticOrderAt_eval_eq_rootMultiplicity (taylor α (P 0)) htaylor_ne 0,
        rootMultiplicity_taylor, zero_add]
    have hdiv0 : (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁)) 0 = (mult : ℤ) :=
      divisor_eq_of_analyticOrder h0mem (hslice_an 0) hord
    have h0supp : (0 : ℂ) ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (0, t))).toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, hdiv0]; exact_mod_cast hmult_pos.ne'
    calc 1 ≤ (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁) 0).toNat := by
          rw [hdiv0, Int.toNat_natCast]; exact hmult_pos
      _ ≤ N 0 := Finset.single_le_sum
          (f := fun a => (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁) a).toNat)
          (fun _ _ => Nat.zero_le _) h0supp
  -- non-emptiness over the transverse parameter
  have hQ : ∀ᶠ z in 𝓝 (0 : CParam 0 1), ∃ t, (P (transL z)).IsRoot t ∧ t ∈ ball α ρ := by
    filter_upwards [hNconst, hconf_z] with z hNz hconfz
    have hNz_pos : 1 ≤ N z := hNz ▸ hN0_pos
    have hfs_ne : (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hN0 : N z = 0 := by simp only [hN_def, hcon, Finset.sum_empty]
      omega
    obtain ⟨a, ha⟩ := hfs_ne
    have ha_supp : a ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support :=
      (Set.Finite.mem_toFinset _).mp ha
    have hamem : a ∈ closedBall (0 : ℂ) R₁ :=
      (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).supportWithinDomain ha_supp
    have hGa : G (z, a) = 0 := by
      by_contra hGa; exact ha_supp (divisor_eq_zero_of_ne (hslice_an z) hamem hGa)
    have hroot : (P (transL z)).IsRoot (a + α) := by
      rw [Polynomial.IsRoot.def]; simpa only [hG_def] using hGa
    have hmemα : (a + α) ∈ closedBall α R₁ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
      rw [mem_closedBall, dist_zero_right] at hamem; exact hamem
    exact ⟨a + α, hroot, hconfz (a + α) hroot hmemα⟩
  -- pull back along `transι` (`transL ∘ transι = id`)
  have hιT : Filter.Tendsto transι (𝓝 (0 : ℂ)) (𝓝 (0 : CParam 0 1)) :=
    (show transι 0 = (0 : CParam 0 1) from rfl) ▸ continuous_transι.continuousAt
  filter_upwards [hιT.eventually hQ] with w hw
  simpa only [transL_ι] using hw

/-- A separation radius for a finite set of points: `0 < ρ` with `3ρ < dist α β` for all distinct
`α, β ∈ S`. -/
lemma exists_sep_radius (S : Finset ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ α ∈ S, ∀ β ∈ S, α ≠ β → 3 * ρ < dist α β := by
  rcases S.offDiag.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun α hα β hβ hαβ => ?_⟩
    have : (α, β) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hα, hβ, hαβ⟩
    rw [he] at this; exact absurd this (Finset.notMem_empty _)
  · set d := S.offDiag.inf' hne (fun p => dist p.1 p.2) with hd
    have hd_pos : 0 < d := by
      rw [hd, Finset.lt_inf'_iff]
      intro p hp
      exact dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2
    refine ⟨d / 4, by linarith, fun α hα β hβ hαβ => ?_⟩
    have hmem : (α, β) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hα, hβ, hαβ⟩
    have hle : d ≤ dist α β := by
      rw [hd]; exact Finset.inf'_le (fun p : ℂ × ℂ => dist p.1 p.2) hmem
    linarith

/-- **M2 — Rouché cluster separation (thesis Theorem 4.2.2, step 4).** For a monic complex family
`P : ℂ → ℂ[X]` of constant degree with analytic coefficients, there is a radius `ρ > 0` whose discs
about the distinct roots of the section polynomial `P 0` are pairwise disjoint, and such that for all
transverse values `w` near `0`:

* every root of `P w` lies in one of those discs (**confinement**);
* each disc still contains a root of `P w` (**non-emptiness**).

This packages `roots_confined` (the tube-lemma half) and `disc_roots_nonempty` (the
argument-principle half) into the bivariate root-continuity statement the monodromy contradiction
consumes. -/
theorem cluster_separation (P : ℂ → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ w, (P w).Monic) (hdeg : ∀ w, (P w).natDegree = m)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun w => (P w).coeff i) 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ α ∈ (P 0).roots.toFinset, ∀ β ∈ (P 0).roots.toFinset, α ≠ β →
        Disjoint (ball α ρ) (ball β ρ)) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ),
        (∀ t, (P w).IsRoot t → ∃ α ∈ (P 0).roots.toFinset, t ∈ ball α ρ) ∧
        (∀ α ∈ (P 0).roots.toFinset, ∃ t, (P w).IsRoot t ∧ t ∈ ball α ρ) := by
  classical
  have hp_ne : P 0 ≠ 0 := (hmonic 0).ne_zero
  set S := (P 0).roots.toFinset with hS
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep_radius S
  have hroot_mem : ∀ {t}, (P 0).IsRoot t → t ∈ S :=
    fun ht => Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp_ne).mpr ht)
  refine ⟨ρ, hρ, ?_, ?_⟩
  · -- disjointness of the discs
    intro α hα β hβ hαβ
    exact ball_disjoint_ball (by have := hsep α hα β hβ hαβ; linarith)
  · -- confinement, then per-disc non-emptiness, combined
    have hconf := roots_confined P m hmonic hdeg hcoeff hρ
    have hnon : ∀ α ∈ S, ∀ᶠ w in 𝓝 (0 : ℂ), ∃ t, (P w).IsRoot t ∧ t ∈ ball α ρ := by
      intro α hα
      have hαroot : (P 0).IsRoot α := (Polynomial.mem_roots hp_ne).mp (Multiset.mem_toFinset.mp hα)
      have hsphere0 : ∀ ζ ∈ sphere α ρ, ¬ (P 0).IsRoot ζ := by
        intro ζ hζ hroot
        have hdζ : dist ζ α = ρ := mem_sphere.mp hζ
        rcases eq_or_ne ζ α with h | h
        · rw [h, dist_self] at hdζ; exact absurd hdζ.symm hρ.ne'
        · linarith [hsep ζ (hroot_mem hroot) α hα h, hdζ]
      have hsupp_ev : ∀ᶠ w in 𝓝 (0 : ℂ),
          ∀ t, (P w).IsRoot t → t ∈ closedBall α (2 * ρ) → t ∈ ball α ρ := by
        filter_upwards [hconf] with w hw t hroot ht_cb
        obtain ⟨β, hβS, htβ⟩ := hw t hroot
        rcases eq_or_ne α β with h | h
        · rw [h]; exact htβ
        · exfalso
          have h1 : dist t α ≤ 2 * ρ := mem_closedBall.mp ht_cb
          have h2 : dist t β < ρ := mem_ball.mp htβ
          have h3 : dist α β < 3 * ρ := by
            have htri := dist_triangle α t β
            rw [dist_comm α t] at htri
            linarith
          exact absurd (hsep α hα β hβS h) (by linarith)
      exact disc_roots_nonempty P m hmonic hdeg hcoeff α hαroot hρ (by linarith : ρ < 2 * ρ)
        hsphere0 hsupp_ev
    filter_upwards [hconf, (Filter.eventually_all_finset S).mpr hnon] with w hwconf hwnon
    exact ⟨hwconf, hwnon⟩

end RoucheSeparation
