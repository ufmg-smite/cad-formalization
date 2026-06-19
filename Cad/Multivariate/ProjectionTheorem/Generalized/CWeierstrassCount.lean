import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassThreading

/-!
# Layer C, piece 3: the zero count is `m`

For Weierstrass preparation `G = u·W` the polynomial `W` must be **monic of degree exactly `m`**
(the `t`-regularity order). Its degree is the number of zeros (with multiplicity) of the slice
`G(z,·)` inside `|t| < R`, i.e. the `k = 0` power sum
`N(z) = ∑_{a} mult_a = (2πi)⁻¹ ∮ G'/G`. Two facts pin it down:

* `N(z)` is the value of an **analytic** function of `z` (`powerSum_analyticAt` at `k = 0`,
  identified with `N(z)` by `slice_powerSum_eq_rootSum` since `a⁰ = 1`), hence continuous;
* `N(z)` is a **natural number** for every `z`.

A continuous, integer-valued function is locally constant, so `N(z) = N(0)` near `0`; and at `z = 0`
the slice `G(0,·)` has a single zero (`t = 0`) of multiplicity `m`, giving `N(0) = m`. The output
`zero_count_eventually` threads this count alongside the four slice hypotheses, ready for the
Newton-identity construction of `W`.
-/

noncomputable section

open Complex Metric Filter
open scoped Real Topology

variable {s e : ℕ}

/-- **Continuous + integer-valued ⟹ locally constant.** If `f` is continuous at `x₀` and equals a
`ℕ`-valued function `N` near `x₀`, then `N` is eventually equal to `N x₀`. (The image lands in the
discrete set `ℤ`, so a change would force a jump of size `≥ 1`, contradicting continuity.) -/
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

/-- The divisor of an analytic slice at a point of known order `m` equals `m` (as an integer). -/
lemma divisor_eq_of_analyticOrder {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ} (hU : a ∈ U)
    (hf : AnalyticOnNhd ℂ f U) {m : ℕ} (hord : analyticOrderAt f a = (m : ℕ∞)) :
    (MeromorphicOn.divisor f U) a = (m : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hU, (hf a hU).meromorphicOrderAt_eq, hord]
  rfl

/-- **Zero count is `m` (Layer C, piece 3).** Strengthens `slice_hyps_eventually`: for `z` near `0`
the slice `G(z,·)` satisfies the four hypotheses of `slice_powerSum_eq_rootSum` *and* its total zero
count (sum of multiplicities of the divisor support) is exactly `m`. -/
theorem zero_count_eventually (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hm_pos : 0 < m) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ R R₁ : ℝ, 0 < R ∧ R < R₁ ∧
      (∀ ζ ∈ sphere (0 : ℂ) R, AnalyticAt ℂ G (0, ζ)) ∧
      (∀ ζ ∈ sphere (0 : ℂ) R, G (0, ζ) ≠ 0) ∧
      (∀ t ∈ closedBall (0 : ℂ) R₁, t ≠ 0 → G (0, t) ≠ 0) ∧
      ∀ᶠ z in 𝓝 (0 : CParam s e),
        AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall 0 R₁) ∧
        (∀ t ∈ closedBall (0 : ℂ) R₁, DifferentiableAt ℂ G (z, t)) ∧
        (∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0) ∧
        (∀ a ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support,
          a ∈ ball (0 : ℂ) R) ∧
        (∑ a ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset,
          (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) a).toNat) = m := by
  classical
  obtain ⟨R, R₁, hR, hRR₁, hGan_sph, hG0_sph, hiso0, hev⟩ :=
    slice_hyps_eventually G hG m hreg
  refine ⟨R, R₁, hR, hRR₁, hGan_sph, hG0_sph, hiso0, ?_⟩
  -- the `k = 0` power sum is analytic, hence continuous
  have hp0_an : AnalyticAt ℂ
      (fun z : CParam s e => (2 * π * I)⁻¹ *
        ∮ ζ in C(0, R), ζ ^ (0 : ℕ) * fderiv ℂ G (z, ζ) (0, 1) / G (z, ζ)) 0 :=
    powerSum_analyticAt G hR 0 hGan_sph hG0_sph
  -- the total zero count as a `ℕ`-valued function
  set N : CParam s e → ℕ := fun z =>
    ∑ a ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset,
      (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) a).toNat with hN_def
  -- the power sum equals `N z` for `z` where the slice hypotheses hold
  have heq : ∀ᶠ z in 𝓝 (0 : CParam s e),
      (2 * π * I)⁻¹ * ∮ ζ in C(0, R), ζ ^ (0 : ℕ) * fderiv ℂ G (z, ζ) (0, 1) / G (z, ζ)
        = (N z : ℂ) := by
    filter_upwards [hev] with z hz
    obtain ⟨hAn, hDiff, hNe, hSupp⟩ := hz
    rw [slice_powerSum_eq_rootSum hR hRR₁ hAn hDiff hNe hSupp 0, hN_def]
    push_cast
    exact Finset.sum_congr rfl fun a _ => by rw [pow_zero, mul_one]
  -- continuity + integer values ⟹ `N` is locally constant
  have hNconst : ∀ᶠ z in 𝓝 (0 : CParam s e), N z = N 0 :=
    eventually_nat_eq_of_continuousAt hp0_an.continuousAt heq
  -- compute `N 0 = m`
  have hN0 : N 0 = m := by
    obtain ⟨hAn0, _, _, _⟩ := hev.self_of_nhds
    have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R₁ := by
      rw [mem_closedBall, dist_self]; linarith
    -- divisor at 0 equals m
    have hdiv0 : (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁)) 0 = (m : ℤ) :=
      divisor_eq_of_analyticOrder h0mem hAn0 hreg
    -- the divisor support reduces to {0}
    have hsupp_eq : (divisor_support_finite (R₁ := R₁) (fun t => G (0, t))).toFinset = {0} := by
      ext a
      rw [Set.Finite.mem_toFinset, Finset.mem_singleton, Function.mem_support]
      constructor
      · intro ha
        by_contra hane
        have hamem : a ∈ closedBall (0 : ℂ) R₁ :=
          (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁)).supportWithinDomain ha
        have hGa : G (0, a) ≠ 0 := hiso0 a hamem hane
        exact ha (divisor_eq_zero_of_ne hAn0 hamem hGa)
      · intro ha; rw [ha, hdiv0]; exact_mod_cast hm_pos.ne'
    rw [hN_def]
    simp only [hsupp_eq, Finset.sum_singleton, hdiv0, Int.toNat_natCast]
  -- assemble
  filter_upwards [hev, hNconst] with z hz hNz
  obtain ⟨hAn, hDiff, hNe, hSupp⟩ := hz
  refine ⟨hAn, hDiff, hNe, hSupp, ?_⟩
  show N z = m
  rw [hNz, hN0]

end
