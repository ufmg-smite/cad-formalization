import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVPackage
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs
import Cad.Multivariate.ProjectionTheorem.Generalized.CArgPrinciple

/-!
# Layer C, piece 1: analyticity of the power sums

Toward Weierstrass preparation (`G = u·W`) via the argument principle. The classical proof builds the
Weierstrass polynomial `W` from the **power sums of the roots** of the `t`-slice `G(z,·)`, which are
given by the contour integrals
`pₖ(z) = (2πi)⁻¹ ∮_{|ζ|=R} ζᵏ · ∂_t G(z,ζ) / G(z,ζ) dζ`
(`∂_t G = fderiv ℂ G (z,ζ) (0,1)`, the `t`-direction partial). This file proves the **first piece**:
each `pₖ` is `AnalyticAt ℂ` in the parameter `z` — an immediate consequence of the now-proven keystone
`circleIntegral_analyticAt_fiber`, since the integrand is analytic at `(0,ζ)` for every `ζ` on the
circle (`G` analytic and non-vanishing there, `∂_t G` analytic as `fderiv` of an analytic function).
-/

noncomputable section

open Complex Metric Filter
open scoped Real Topology

variable {s e : ℕ}

/-- **Non-vanishing propagates locally in the parameter.** If `G(z₀,·)` is non-zero on a compact set
`K` (of the `t`-variable), then `G(z,·)` is non-zero on all of `K` for every `z` in a neighborhood of
`z₀`. (Tube lemma applied to the open set `{G ≠ 0}` around the compact fiber `{z₀} × K`.) This supplies
the "zeros stay inside the circle" hypothesis (`hsupp`) when specializing the argument principle to a
`t`-regular family `G(z,·)` near `z = 0`. -/
theorem eventually_ne_zero_on_compact {H : Type*} [TopologicalSpace H] {W : Set (H × ℂ)}
    (hW : IsOpen W) {G : H × ℂ → ℂ} (hG : ContinuousOn G W) {K : Set ℂ} (hK : IsCompact K) {z₀ : H}
    (hsub : {z₀} ×ˢ K ⊆ W) (hz₀ : ∀ t ∈ K, G (z₀, t) ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ t ∈ K, G (z, t) ≠ 0 := by
  obtain ⟨u, v, hu, _, hz₀u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK
    (hG.isOpen_inter_preimage hW isOpen_compl_singleton)
    (by rintro ⟨z, t⟩ ⟨hz, ht⟩
        rw [Set.mem_singleton_iff] at hz; subst hz
        exact ⟨hsub (Set.mk_mem_prod rfl ht), hz₀ t ht⟩)
  filter_upwards [hu.mem_nhds (hz₀u rfl)] with z hz t ht
  exact (huv (Set.mk_mem_prod hz (hKv ht))).2

/-- **The `t`-partial as a slice derivative:** `∂ₜG(z,ζ) = deriv (G(z,·)) ζ`. This identifies the
power-sum integrand `ζᵏ·∂ₜG/G` with `argPrinciple_general`'s integrand `ζᵏ·logDeriv(G(z,·))`. -/
theorem deriv_slice_eq_fderiv {G : CParam s e × ℂ → ℂ} {z : CParam s e} {ζ : ℂ}
    (hG : DifferentiableAt ℂ G (z, ζ)) :
    deriv (fun t => G (z, t)) ζ = fderiv ℂ G (z, ζ) (0, 1) := by
  have hmap : HasDerivAt (fun t : ℂ => ((z, t) : CParam s e × ℂ)) ((0, 1) : CParam s e × ℂ) ζ :=
    (hasDerivAt_const ζ z).prodMk (hasDerivAt_id ζ)
  exact (hG.hasFDerivAt.comp_hasDerivAt ζ hmap).deriv

/-- **Power sums are analytic (Layer C, piece 1).** If `G` is analytic and non-vanishing at `(0,ζ)`
for every `ζ` on the circle `|ζ| = R`, then the `k`-th power-sum contour integral
`z ↦ (2πi)⁻¹ ∮ ζᵏ ∂_t G(z,ζ)/G(z,ζ) dζ` is `AnalyticAt ℂ` at the origin. The genuine content is the
keystone `circleIntegral_analyticAt_fiber`; the integrand's fiber-analyticity is routine. -/
theorem powerSum_analyticAt (G : CParam s e × ℂ → ℂ) {R : ℝ} (hR : 0 < R) (k : ℕ)
    (hGan : ∀ ζ ∈ sphere (0 : ℂ) R, AnalyticAt ℂ G (0, ζ))
    (hG0 : ∀ ζ ∈ sphere (0 : ℂ) R, G (0, ζ) ≠ 0) :
    AnalyticAt ℂ (fun z : CParam s e =>
      (2 * π * I)⁻¹ * ∮ ζ in C(0, R), ζ ^ k * fderiv ℂ G (z, ζ) (0, 1) / G (z, ζ)) 0 := by
  refine analyticAt_const.mul ?_
  refine circleIntegral_analyticAt_fiber
    (fun p : CParam s e × ℂ => p.2 ^ k * fderiv ℂ G p (0, 1) / G p) hR fun ζ hζ => ?_
  have hGζ : AnalyticAt ℂ G (0, ζ) := hGan ζ hζ
  have hpow : AnalyticAt ℂ (fun p : CParam s e × ℂ => p.2 ^ k) (0, ζ) := analyticAt_snd.pow k
  have hpartial : AnalyticAt ℂ (fun p : CParam s e × ℂ => fderiv ℂ G p (0, 1)) (0, ζ) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : CParam s e × ℂ)).analyticAt _).comp hGζ.fderiv
  exact (hpow.mul hpartial).div hGζ (hG0 ζ hζ)

/-- **The argument principle for a `t`-slice (Layer C specialization).** For a fixed parameter `z`,
if the slice `G(z,·)` is analytic on `closedBall 0 R₁` (`R < R₁`), is jointly differentiable, is not
identically zero, and all its zeros lie inside `|t| = R`, then the `k`-th power-sum integral computes
the `k`-th power sum of the roots of `G(z,·)`:
`(2πi)⁻¹ ∮ tᵏ·∂ₜG(z,t)/G(z,t) dt = ∑_{a : root} (mult a)·aᵏ`. Just `argPrinciple_general` with the
integrand `∂ₜG = deriv (G(z,·))` (via `deriv_slice_eq_fderiv`). -/
theorem slice_powerSum_eq_rootSum {G : CParam s e × ℂ → ℂ} {z : CParam s e} {R R₁ : ℝ}
    (hR : 0 < R) (hRR₁ : R < R₁)
    (hGan : AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall 0 R₁))
    (hGdiff : ∀ t ∈ closedBall (0 : ℂ) R₁, DifferentiableAt ℂ G (z, t))
    (hne : ∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0)
    (hsupp : ∀ a ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support,
      a ∈ ball (0 : ℂ) R)
    (k : ℕ) :
    (2 * π * I)⁻¹ * ∮ t in C(0, R), t ^ k * fderiv ℂ G (z, t) (0, 1) / G (z, t)
      = ∑ a ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset,
          ((MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) a).toNat : ℂ) * a ^ k := by
  rw [show (2 * π * I)⁻¹ * (∮ t in C(0, R), t ^ k * fderiv ℂ G (z, t) (0, 1) / G (z, t))
      = (2 * π * I)⁻¹ * ∮ t in C(0, R), t ^ k * logDeriv (fun t' => G (z, t')) t from ?_]
  · exact argPrinciple_general hR hRR₁ k hGan hne hsupp
  · congr 1
    refine circleIntegral.integral_congr hR.le fun t ht => ?_
    rw [logDeriv_apply, deriv_slice_eq_fderiv
      (hGdiff t (closedBall_subset_closedBall hRR₁.le (sphere_subset_closedBall ht)))]
    ring

end
