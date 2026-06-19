import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# C argument-principle, base case (WIP)

Toward the `z = 0` base case of the argument principle needed for `weierstrass_division`:
for `G(ζ) = ζᵐ·v(ζ)` with `v` analytic and non-vanishing on the closed disc,
`(2πi)⁻¹ ∮_{|ζ|=R} G'(ζ)/G(ζ) dζ = m`. The logarithmic derivative splits as
`G'/G = m/ζ + v'/v`, and `∮ m/ζ = 2πi·m` (residue, **proved below, sorry-free**),
`∮ v'/v = 0` (Cauchy–Goursat, `v ≠ 0` on the disc).

This isolates the genuinely-Mathlib-supported half of the argument-principle gap (the residue), and
documents the remaining obligation (the log-derivative split + Cauchy–Goursat for `v'/v`).
-/

noncomputable section

open Complex Metric Topology Filter
open scoped Real Topology

/-- **Weighted single-point residue (argument-principle brick).** For `a` inside the circle,
`(2πi)⁻¹ ∮_{|t|=R} tᵏ/(t−a) dt = aᵏ` — the residue of `tᵏ/(t−a)` at the simple pole `a`. This is the
per-root contribution in the (generalized) argument principle `(2πi)⁻¹∮ tᵏ G'/G = ∑ mult·aᵏ`: applied
to each zero `a` of `G(z,·)` after factoring out the non-vanishing unit (`MeromorphicOn.extract_zeros_poles`),
it gives the `k`-th power sum of the roots. Direct from the Cauchy integral formula (`f(t) = tᵏ`). -/
theorem circleIntegral_pow_div_sub {R : ℝ} (k : ℕ) {a : ℂ} (ha : a ∈ ball 0 R) :
    (2 * π * I)⁻¹ * ∮ t in C(0, R), t ^ k / (t - a) = a ^ k := by
  have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (E := ℂ) (s := ∅) Set.countable_empty ha
    ((continuous_pow k).continuousOn) (fun z _ => (differentiable_pow k).differentiableAt)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- `logDeriv` of a shifted power: `logDeriv (·−a)^n = n/(·−a)`. -/
theorem logDeriv_sub_const_pow (a : ℂ) (n : ℕ) (t : ℂ) :
    logDeriv (fun u => (u - a) ^ n) t = (n : ℂ) / (t - a) := by
  have hg : DifferentiableAt ℂ (fun u : ℂ => u - a) t := by fun_prop
  have h := logDeriv_comp (f := fun u : ℂ => u ^ n) (g := fun u : ℂ => u - a)
    (differentiableAt_pow n) hg
  rw [logDeriv_pow] at h
  rw [show (fun u : ℂ => (u - a) ^ n) = (fun u => u ^ n) ∘ (fun u => u - a) from rfl, h]
  simp

/-- **The argument principle for a factored function (Layer C assembly).** For
`f(t) = (∏_{a∈s} (t−a)^{d a}) · g(t)` with the roots `a ∈ s` inside the circle and `g` analytic and
non-vanishing on the closed disc, the weighted log-derivative integral computes the `k`-th power sum of
the roots: `(2πi)⁻¹ ∮ tᵏ · f'/f dt = ∑_{a∈s} (d a)·aᵏ`. Sum of the per-root residues
(`circleIntegral_pow_div_sub`); the unit `g` contributes `0` (Cauchy–Goursat). -/
theorem argPrinciple_factored {R : ℝ} (hR : 0 < R) (k : ℕ)
    (s : Finset ℂ) (hs : ∀ a ∈ s, a ∈ ball (0 : ℂ) R) (d : ℂ → ℕ)
    (g : ℂ → ℂ) (hg_an : ∀ z ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ g z)
    (hg0 : ∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0) :
    (2 * π * I)⁻¹ * ∮ t in C(0, R), t ^ k *
        logDeriv (fun u => (∏ a ∈ s, (u - a) ^ d a) * g u) t
      = ∑ a ∈ s, (d a : ℂ) * a ^ k := by
  -- on the sphere `t ≠ a` for every root, and `g t ≠ 0`
  have hne : ∀ t ∈ sphere (0 : ℂ) R, ∀ a ∈ s, t - a ≠ 0 := by
    intro t ht a ha hta
    rw [sub_eq_zero] at hta
    rw [mem_sphere_zero_iff_norm, hta] at ht
    exact absurd ht (ne_of_lt (mem_ball_zero_iff.mp (hs a ha)))
  have hgcb : ∀ t ∈ sphere (0 : ℂ) R, g t ≠ 0 := fun t ht => hg0 t (sphere_subset_closedBall ht)
  have hlogDeriv_g_an : ∀ z ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ (logDeriv g) z :=
    fun z hz => ((hg_an z hz).deriv).div (hg_an z hz) (hg0 z hz)
  have hfac_diff : ∀ (a : ℂ) (t : ℂ), DifferentiableAt ℂ (fun u => (u - a) ^ d a) t :=
    fun a t => ((differentiableAt_id).sub_const a).pow (d a)
  have hprod_diff : ∀ t : ℂ, DifferentiableAt ℂ (fun u => ∏ a ∈ s, (u - a) ^ d a) t :=
    fun t => DifferentiableAt.fun_finset_prod fun a _ => hfac_diff a t
  -- integrand decomposition on the sphere
  have hdecomp : Set.EqOn
      (fun t => t ^ k * logDeriv (fun u => (∏ a ∈ s, (u - a) ^ d a) * g u) t)
      (fun t => (∑ a ∈ s, t ^ k * ((d a : ℂ) / (t - a))) + t ^ k * logDeriv g t)
      (sphere (0 : ℂ) R) := by
    intro t ht
    have hprod_ne : (∏ a ∈ s, (t - a) ^ d a) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun a ha => pow_ne_zero _ (hne t ht a ha)
    have hg_diff : DifferentiableAt ℂ g t := (hg_an t (sphere_subset_closedBall ht)).differentiableAt
    have hlogprod : logDeriv (fun u : ℂ => ∏ a ∈ s, (u - a) ^ d a) t
        = ∑ a ∈ s, (d a : ℂ) / (t - a) := by
      rw [logDeriv_prod (f := fun a => fun u : ℂ => (u - a) ^ d a)
        (fun a ha => pow_ne_zero (d a) (hne t ht a ha)) (fun a _ => hfac_diff a t)]
      exact Finset.sum_congr rfl fun a _ => logDeriv_sub_const_pow a (d a) t
    show t ^ k * logDeriv (fun u => (∏ a ∈ s, (u - a) ^ d a) * g u) t
      = (∑ a ∈ s, t ^ k * ((d a : ℂ) / (t - a))) + t ^ k * logDeriv g t
    rw [logDeriv_mul (f := fun u => ∏ a ∈ s, (u - a) ^ d a) (g := g) t hprod_ne (hgcb t ht)
      (hprod_diff t) hg_diff, hlogprod, mul_add, Finset.mul_sum]
  -- integrability of each piece on the sphere (continuity)
  have hint_each : ∀ a ∈ s, CircleIntegrable (fun t => t ^ k * ((d a : ℂ) / (t - a))) 0 R := by
    intro a ha
    refine ContinuousOn.circleIntegrable hR.le ((continuous_pow k).continuousOn.mul ?_)
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun t ht => hne t ht a ha)
  have hint_g : CircleIntegrable (fun t => t ^ k * logDeriv g t) 0 R :=
    ContinuousOn.circleIntegrable hR.le ((continuous_pow k).continuousOn.mul fun t ht =>
      ((hlogDeriv_g_an t (sphere_subset_closedBall ht)).continuousAt).continuousWithinAt)
  have hunit0 : ∮ t in C(0, R), t ^ k * logDeriv g t = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      ((continuous_pow k).continuousOn.mul fun t ht =>
        ((hlogDeriv_g_an t ht).continuousAt).continuousWithinAt) (fun t ht => ?_)
    exact (differentiableAt_pow k).mul (hlogDeriv_g_an t (ball_subset_closedBall ht.1)).differentiableAt
  have hint_sum : CircleIntegrable (fun t => ∑ a ∈ s, t ^ k * ((d a : ℂ) / (t - a))) 0 R :=
    ContinuousOn.circleIntegrable hR.le (continuousOn_finset_sum s fun a _ =>
      (continuous_pow k).continuousOn.mul (continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) fun t ht => hne t ht a ‹_›))
  rw [circleIntegral.integral_congr hR.le hdecomp,
    circleIntegral.integral_add hint_sum hint_g, hunit0, add_zero,
    circleIntegral.integral_fun_sum hint_each, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have heq : (fun t => t ^ k * ((d a : ℂ) / (t - a))) = fun t => (d a : ℂ) • (t ^ k / (t - a)) := by
    funext t; rw [smul_eq_mul]; ring
  rw [heq, circleIntegral.integral_smul, smul_eq_mul,
    show (2 * π * I)⁻¹ * ((d a : ℂ) * ∮ t in C(0, R), t ^ k / (t - a))
      = (d a : ℂ) * ((2 * π * I)⁻¹ * ∮ t in C(0, R), t ^ k / (t - a)) from by ring,
    circleIntegral_pow_div_sub (k := k) (hs a ha)]

/-- **The factorized-rational factor as a `Finset` product** (toward `argPrinciple_factored`'s shape):
for a finitely-supported non-negative divisor `d`, `∏ᶠ u, (x−u)^{d u} = ∏_{a∈supp} (x−a)^{(d a).toNat}`. -/
theorem finprod_sub_zpow_eq_finset_prod {d : ℂ → ℤ} (hfin : d.support.Finite)
    (hd : ∀ a, 0 ≤ d a) (x : ℂ) :
    ∏ᶠ u, (x - u) ^ d u = ∏ a ∈ hfin.toFinset, (x - a) ^ (d a).toNat := by
  have hsub : Function.mulSupport (fun u => (x - u) ^ d u) ⊆ ↑hfin.toFinset := by
    intro u hu
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hd0
    exact hu (by simp [hd0])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact Finset.prod_congr rfl fun a _ => by rw [← zpow_natCast, Int.toNat_of_nonneg (hd a)]

/-- **Finiteness of the divisor support on a closed ball** (the remaining `extract_zeros_poles`
hypothesis): the support of `divisor f (closedBall 0 R₁)` is finite, since the divisor has locally
finite support within its domain and the domain is compact. -/
theorem divisor_support_finite (f : ℂ → ℂ) {R₁ : ℝ} :
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) R₁)).support.Finite :=
  (MeromorphicOn.divisor f (closedBall 0 R₁)).finiteSupport (isCompact_closedBall 0 R₁)

/-- **Codiscrete equality upgrades to a neighborhood equality for analytic functions.** If `f = h`
off a codiscrete subset of an open set `U`, and both are analytic at `z₀ ∈ U`, then `f = h` on a whole
neighborhood of `z₀`. This is the key bridge that lets `extract_zeros_poles`'s `=ᶠ[codiscreteWithin]`
factorization be used for the (local) `logDeriv` / contour integral, where genuine neighborhood
equality is needed. Proof: codiscrete ⟹ `f = h` on a punctured neighborhood; `f − h` is analytic and
eventually zero off `z₀`, hence (no isolated points) frequently zero, hence eventually zero. -/
theorem eventuallyEq_nhds_of_codiscreteWithin {U : Set ℂ} {f h : ℂ → ℂ}
    (hfh : f =ᶠ[codiscreteWithin U] h) {z₀ : ℂ} (hmem : U ∈ 𝓝 z₀)
    (hf : AnalyticAt ℂ f z₀) (hh : AnalyticAt ℂ h z₀) :
    f =ᶠ[𝓝 z₀] h := by
  have hz₀ : z₀ ∈ U := mem_of_mem_nhds hmem
  have hUmem : U ∈ 𝓝[≠] z₀ := nhdsWithin_le_nhds hmem
  have hcd : {x | f x = h x} ∪ Uᶜ ∈ 𝓝[≠] z₀ :=
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfh z₀ hz₀
  have hpunc : f =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hcd, hUmem] with x hx hxU
    exact hx.resolve_right (not_not.mpr hxU)
  have hd : (f - h) =ᶠ[𝓝[≠] z₀] 0 := by filter_upwards [hpunc] with x hx; simp [hx]
  have hev : (f - h) =ᶠ[𝓝 z₀] 0 :=
    (hf.sub hh).frequently_zero_iff_eventually_zero.mp hd.frequently
  filter_upwards [hev] with x hx; simpa [sub_eq_zero] using hx

/-- **Order is finite everywhere** (toward `extract_zeros_poles`'s hypothesis): an analytic function
on a preconnected open set that is non-zero at one point has finite meromorphic order at every point
(it is not locally zero anywhere, by the identity theorem). -/
theorem meromorphicOrderAt_ne_top_of_analyticOnNhd {U : Set ℂ} (hU : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hfz₀ : f z₀ ≠ 0) :
    ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤ := by
  intro z hz
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf z hz).meromorphicAt]
  rcases (hf z hz).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exact absurd (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz hzero hz₀) hfz₀
  · exact hne

/-- **The argument principle (general analytic `f`).** For `f` analytic on `closedBall 0 R₁`
(`R < R₁`), not identically zero, with all its zeros inside the circle `|t| = R`, the weighted
log-derivative integral computes the `k`-th power sum of the zeros (with multiplicity):
`(2πi)⁻¹ ∮ tᵏ f'/f dt = ∑_{a : zero} (mult a)·aᵏ`. Proof: factor `f = (∏(·−a)^{mult})·g` via
`extract_zeros_poles` (hypotheses from the bricks above), upgrade the codiscrete equality to a
neighborhood equality on the circle, and finish with `argPrinciple_factored`. -/
theorem argPrinciple_general {R R₁ : ℝ} (hR : 0 < R) (hRR₁ : R < R₁) (k : ℕ)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R₁))
    (hfz₀ : ∃ z ∈ closedBall (0 : ℂ) R₁, f z ≠ 0)
    (hsupp : ∀ a ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) R₁)).support, a ∈ ball (0 : ℂ) R) :
    (2 * π * I)⁻¹ * ∮ t in C(0, R), t ^ k * logDeriv f t
      = ∑ a ∈ (divisor_support_finite (R₁ := R₁) f).toFinset,
          ((MeromorphicOn.divisor f (closedBall (0 : ℂ) R₁) a).toNat : ℂ) * a ^ k := by
  classical
  obtain ⟨z₀, hz₀mem, hz₀ne⟩ := hfz₀
  have hcbpre : IsPreconnected (closedBall (0 : ℂ) R₁) := (convex_closedBall 0 R₁).isPreconnected
  have horder : ∀ u : closedBall (0 : ℂ) R₁, meromorphicOrderAt f u ≠ ⊤ := fun u =>
    meromorphicOrderAt_ne_top_of_analyticOnNhd hcbpre hf hz₀mem hz₀ne u u.2
  obtain ⟨g, hg_an, hg_ne, hfact⟩ :=
    (AnalyticOnNhd.meromorphicOn hf).extract_zeros_poles horder (divisor_support_finite f)
  have hdivnn0 : (0 : _) ≤ MeromorphicOn.divisor f (closedBall (0 : ℂ) R₁) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hdivnn : ∀ a, 0 ≤ MeromorphicOn.divisor f (closedBall (0 : ℂ) R₁) a := fun a => hdivnn0 a
  set D := MeromorphicOn.divisor f (closedBall (0 : ℂ) R₁) with hD
  set s := (divisor_support_finite (R₁ := R₁) f).toFinset with hs
  have hcbsub : closedBall (0 : ℂ) R ⊆ closedBall (0 : ℂ) R₁ := closedBall_subset_closedBall hRR₁.le
  -- `g` analytic and non-vanishing on the smaller closed ball
  have hg_an_R : ∀ z ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ g z := fun z hz => hg_an z (hcbsub hz)
  have hg0_R : ∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0 := fun z hz => hg_ne ⟨z, hcbsub hz⟩
  -- the factored form `φ • g = (∏ a∈s, (·-a)^…) * g`
  have hfacteq : (∏ᶠ u, (· - u) ^ (D u)) • g
      = fun u => (∏ a ∈ s, (u - a) ^ (D a).toNat) * g u := by
    funext x
    rw [Pi.smul_apply', smul_eq_mul, Function.FactorizedRational.finprod_eq_fun (divisor_support_finite f)]
    exact congrArg (· * g x) (finprod_sub_zpow_eq_finset_prod (divisor_support_finite f) hdivnn x)
  -- on the sphere, `logDeriv f = logDeriv (factored)`
  have hlogeq : Set.EqOn (fun t => t ^ k * logDeriv f t)
      (fun t => t ^ k * logDeriv (fun u => (∏ a ∈ s, (u - a) ^ (D a).toNat) * g u) t)
      (sphere (0 : ℂ) R) := by
    intro t ht
    have htcb : t ∈ closedBall (0 : ℂ) R₁ := hcbsub (sphere_subset_closedBall ht)
    have hcbmem : closedBall (0 : ℂ) R₁ ∈ 𝓝 t :=
      mem_of_superset (isOpen_ball.mem_nhds (by
        rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp ht]; exact hRR₁)) ball_subset_closedBall
    have hft : AnalyticAt ℂ f t := hf t htcb
    have hffacan : AnalyticAt ℂ (fun u => (∏ a ∈ s, (u - a) ^ (D a).toNat) * g u) t :=
      (Finset.analyticAt_fun_prod s fun a _ =>
        (analyticAt_id.sub analyticAt_const).pow _).mul (hg_an_R t (sphere_subset_closedBall ht))
    have hφgan : AnalyticAt ℂ ((∏ᶠ u, (· - u) ^ (D u)) • g) t := by rw [hfacteq]; exact hffacan
    have hbridge := eventuallyEq_nhds_of_codiscreteWithin hfact hcbmem hft hφgan
    rw [hfacteq] at hbridge
    show t ^ k * logDeriv f t
      = t ^ k * logDeriv (fun u => (∏ a ∈ s, (u - a) ^ (D a).toNat) * g u) t
    rw [logDeriv_apply, logDeriv_apply, hbridge.deriv_eq, hbridge.eq_of_nhds]
  rw [circleIntegral.integral_congr hR.le hlogeq]
  exact argPrinciple_factored hR k s
    (fun a ha => hsupp a ((Set.Finite.mem_toFinset _).mp ha)) (fun a => (D a).toNat) g hg_an_R hg0_R

/-!
**Status of the argument principle** (`(2πi)⁻¹∮ tᵏ G'/G = ∑ mult·aᵏ`, hence root count `= m` constant
near `0` and the power sums `= ∑ roots^k`):
* ✅ base case `z = 0` — `circleIntegral_logDeriv_pow_mul`.
* ✅ per-root residue — `circleIntegral_pow_div_sub`.
* ✅ **factored case** — `argPrinciple_factored`: for `f = (∏ⱼ(·−aⱼ)^{dⱼ})·g` with `g` analytic
  non-vanishing, `(2πi)⁻¹∮ tᵏ f'/f = ∑ⱼ dⱼ·aⱼᵏ` (sum the residues; unit `g` contributes `0`).
* ✅ codiscrete bookkeeping bricks: `meromorphicOrderAt_ne_top_of_analyticOnNhd` (order `≠ ⊤`),
  `eventuallyEq_nhds_of_codiscreteWithin` (`=ᶠ[codiscreteWithin]` ⟹ `=ᶠ[𝓝]`),
  `finprod_sub_zpow_eq_finset_prod` (factor as `Finset` product), `divisor_support_finite`
  (finiteness on the compact closed ball, via `locallyFinsuppWithin.finiteSupport`).
* ✅ **`argPrinciple_general`** — the full argument principle for an arbitrary analytic `f` on
  `closedBall 0 R₁` whose zeros lie inside `|t| = R`: `(2πi)⁻¹∮ tᵏ f'/f = ∑_{a} (mult a)·aᵏ`. Assembled
  from `extract_zeros_poles` + the bricks + `argPrinciple_factored`.

**Remaining for Weierstrass preparation:** specialize `argPrinciple_general` to `f = G(z,·)` (the zeros
of `G(z,·)` cluster inside a small circle for `z` near `0`, giving the `hsupp` hypothesis), deducing
`pₖ(z) = ∑ roots^k` and root count `= m`; then Newton's identities → the Weierstrass polynomial `W`,
and the synthesis `G = u·W`.
-/

end
