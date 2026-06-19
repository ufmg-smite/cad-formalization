import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassPrepC

/-!
# Layer C, piece 2: parametric threading of the slice hypotheses

`slice_powerSum_eq_rootSum` and `powerSum_analyticAt` (in `CWeierstrassPrepC`) compute the power
sums of the roots of the `t`-slice `G(z,·)`, **assuming** that for the fixed parameter `z` the slice
is analytic on a closed disc `closedBall 0 R₁`, is not identically zero, and has all its zeros inside
the smaller circle `|t| < R`. This file discharges those hypotheses **uniformly for all `z` near
`0`**, from the single qualitative input that `G` is analytic at `0` and `t`-regular of order `m`
(`analyticOrderAt (G(0,·)) 0 = m`, `m > 0`).

The geometry is the classical Weierstrass setup:

* `G` analytic at `0` ⟹ analytic on a product ball `ball 0 ρ` (`AnalyticAt.exists_ball_analyticOnNhd`);
  for `‖z‖ < ρ` every slice `G(z,·)` is then analytic on `closedBall 0 R₁` whenever `R₁ < ρ`.
* The order-`m` (`m > 0`) zero of `G(0,·)` at `t = 0` is **isolated**: there is a punctured disc
  `0 < |t| < δ` on which `G(0,·)` never vanishes. Choosing `R < R₁ < min ρ δ`, the closed annulus
  `R ≤ |t| ≤ R₁` is a compact set on which `G(0,·) ≠ 0`.
* `eventually_ne_zero_on_compact` then propagates non-vanishing on that annulus to all `z` near `0`:
  so for `z` near `0` the slice `G(z,·)` has no zeros in the annulus, hence all its zeros lie in
  `|t| < R` (and it is not identically zero — it is non-zero on the whole annulus).

The output `slice_hyps_eventually` packages exactly the four hypotheses consumed downstream.
-/

noncomputable section

open Complex Metric Filter
open scoped Real Topology

variable {s e : ℕ}

/-- For an analytic function with a zero of *finite* order at `a` (here `≠ 0` would be order `0`),
`f a ≠ 0` forces the divisor to vanish at `a`. Contrapositive of "divisor-support points are
zeros", used to confine the zeros of the slice to `|t| < R`. -/
lemma divisor_eq_zero_of_ne {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {a : ℂ}
    (ha : a ∈ U) (hne : f a ≠ 0) : (MeromorphicOn.divisor f U) a = 0 := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn ha]
  have hfa : AnalyticAt ℂ f a := hf a ha
  rw [hfa.meromorphicOrderAt_eq, hfa.analyticOrderAt_eq_zero.mpr hne]
  rfl

/-- **Isolated zero of the regular slice.** If `G(0,·)` has order exactly `m > 0` at `t = 0`, there
is a punctured radius `δ > 0` on which it never vanishes: `0 < |t| < δ ⟹ G(0,t) ≠ 0`. -/
private lemma exists_punctured_radius (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ δ > 0, ∀ t : ℂ, t ≠ 0 → ‖t‖ < δ → G (0, t) ≠ 0 := by
  have hG0 : AnalyticAt ℂ (fun t : ℂ => G (0, t)) 0 :=
    hG.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  rcases hG0.eventually_eq_zero_or_eventually_ne_zero with hz | hne
  · -- order would be ⊤, contradicting `= m`
    exfalso
    have : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = ⊤ := analyticOrderAt_eq_top.mpr hz
    rw [hreg] at this
    exact (ENat.coe_ne_top m) this
  · obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp hne
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
    exact ⟨δ, hδ, fun t ht htδ =>
      hUsub t (hball ⟨by simpa [dist_zero_right] using htδ, by simpa using ht⟩)⟩

/-- **Parametric threading (Layer C, piece 2).** From `G` analytic at `0` and `t`-regular of order
`m > 0`, produce radii `0 < R < R₁` such that for every parameter `z` in a neighbourhood of `0`, the
slice `G(z,·)`:
* is analytic on `closedBall 0 R₁`,
* is jointly differentiable there (`DifferentiableAt ℂ G (z,t)` for `t ∈ closedBall 0 R₁`),
* is not identically zero, and
* has all of its zeros (divisor support) inside `ball 0 R`.

These are exactly the hypotheses of `slice_powerSum_eq_rootSum` / `powerSum_analyticAt`, now verified
simultaneously for a whole neighbourhood of `0` in the parameter. -/
theorem slice_hyps_eventually (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ R R₁ : ℝ, 0 < R ∧ R < R₁ ∧
      (∀ ζ ∈ sphere (0 : ℂ) R, AnalyticAt ℂ G (0, ζ)) ∧
      (∀ ζ ∈ sphere (0 : ℂ) R, G (0, ζ) ≠ 0) ∧
      (∀ t ∈ closedBall (0 : ℂ) R₁, t ≠ 0 → G (0, t) ≠ 0) ∧
      ∀ᶠ z in 𝓝 (0 : CParam s e),
        AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall 0 R₁) ∧
        (∀ t ∈ closedBall (0 : ℂ) R₁, DifferentiableAt ℂ G (z, t)) ∧
        (∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0) ∧
        (∀ a ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support,
          a ∈ ball (0 : ℂ) R) := by
  -- 1. analyticity ball for `G`
  obtain ⟨ρ, hρ, hGball⟩ := hG.exists_ball_analyticOnNhd
  -- 2. punctured radius for the isolated zero of the regular slice
  obtain ⟨δ, hδ, hpunct⟩ := exists_punctured_radius G hG m hreg
  -- 3. choose radii  R = q/4 < R₁ = q/2 < q = min ρ δ
  set q : ℝ := min ρ δ with hq_def
  have hq : 0 < q := lt_min hρ hδ
  have hqρ : q ≤ ρ := min_le_left _ _
  have hqδ : q ≤ δ := min_le_right _ _
  refine ⟨q / 4, q / 2, by positivity, by linarith, ?_, ?_, ?_, ?_⟩
  · -- (0,ζ) ∈ ball 0 ρ  since ‖ζ‖ = q/2 < ρ
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    refine hGball (0, ζ) ?_
    rw [mem_ball, dist_zero_right, show ‖((0 : CParam s e), ζ)‖ = ‖ζ‖ by simp [Prod.norm_def], hζ]
    linarith
  · -- non-vanishing on the circle |ζ| = q/2  (punctured: 0 < q/2 < δ)
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    refine hpunct ζ ?_ (by rw [hζ]; linarith)
    rw [← norm_pos_iff, hζ]; positivity
  · -- isolated zero at 0: the only zero of `G(0,·)` in `closedBall 0 (q/2)` is `t = 0`
    intro t ht htne
    rw [mem_closedBall, dist_zero_right] at ht
    exact hpunct t htne (by linarith)
  -- 4. the eventually-statement
  -- the closed annulus  q/4 ≤ |t| ≤ q/2
  set K : Set ℂ := closedBall 0 (q / 2) \ ball 0 (q / 4) with hK_def
  have hK_compact : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  -- G(0,·) ≠ 0 on K
  have hG0K : ∀ t ∈ K, G (0, t) ≠ 0 := by
    rintro t ⟨htR₁, htR⟩
    rw [mem_closedBall, dist_zero_right] at htR₁
    rw [mem_ball, dist_zero_right, not_lt] at htR
    refine hpunct t ?_ (by linarith)
    rw [← norm_pos_iff]; linarith
  -- annulus is inside the slice-at-0 fiber of the product ball
  have hKsub : ({(0 : CParam s e)} ×ˢ K) ⊆ ball (0 : CParam s e × ℂ) ρ := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rw [Set.mem_singleton_iff] at hz; subst hz
    have htR₁ : ‖t‖ ≤ q / 2 := by
      have := ht.1; rw [mem_closedBall, dist_zero_right] at this; exact this
    rw [mem_ball, dist_zero_right, Prod.norm_def]
    simp only [norm_zero, max_eq_right (norm_nonneg t)]
    linarith
  -- propagate non-vanishing on K to z near 0
  have hannulus : ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ t ∈ K, G (z, t) ≠ 0 :=
    eventually_ne_zero_on_compact isOpen_ball hGball.continuousOn hK_compact hKsub hG0K
  -- slices analytic on closedBall (q/2) for z in ball 0 ρ
  have hball_z : ball (0 : CParam s e) ρ ∈ 𝓝 (0 : CParam s e) := Metric.ball_mem_nhds 0 hρ
  filter_upwards [hannulus, hball_z] with z hz_annulus hz_ball
  rw [mem_ball, dist_zero_right] at hz_ball
  -- the slice is analytic at each t in closedBall (q/2): (z,t) ∈ ball 0 ρ
  have hslice_at : ∀ t ∈ closedBall (0 : ℂ) (q / 2), AnalyticAt ℂ (fun t => G (z, t)) t := by
    intro t ht
    rw [mem_closedBall, dist_zero_right] at ht
    have hmem : (z, t) ∈ ball (0 : CParam s e × ℂ) ρ := by
      rw [mem_ball, dist_zero_right, Prod.norm_def]
      apply max_lt hz_ball; linarith
    exact (hGball (z, t) hmem).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hslice_an : AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall 0 (q / 2)) :=
    fun t ht => hslice_at t ht
  refine ⟨hslice_an, ?_, ?_, ?_⟩
  · -- joint differentiability
    intro t ht
    rw [mem_closedBall, dist_zero_right] at ht
    have hmem : (z, t) ∈ ball (0 : CParam s e × ℂ) ρ := by
      rw [mem_ball, dist_zero_right, Prod.norm_def]
      apply max_lt hz_ball; linarith
    exact (hGball (z, t) hmem).differentiableAt
  · -- not identically zero: nonzero at t = (q/2 : ℂ), which lies on the annulus
    have hnorm : ‖((q / 2 : ℝ) : ℂ)‖ = q / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine ⟨((q / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, hnorm]
    · refine hz_annulus ((q / 2 : ℝ) : ℂ) ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, hnorm]
      · rw [mem_ball, dist_zero_right, hnorm, not_lt]; linarith
  · -- zeros confined to ball 0 (q/4)
    intro a ha
    by_contra ha_out
    rw [mem_ball, dist_zero_right, not_lt] at ha_out
    have ha_mem : a ∈ closedBall (0 : ℂ) (q / 2) :=
      (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall 0 (q / 2))).supportWithinDomain ha
    have haK : a ∈ K := by
      refine ⟨ha_mem, ?_⟩
      rw [mem_ball, dist_zero_right, not_lt]; exact ha_out
    have hGa : G (z, a) ≠ 0 := hz_annulus a haK
    exact ha (divisor_eq_zero_of_ne hslice_an ha_mem hGa)

end
