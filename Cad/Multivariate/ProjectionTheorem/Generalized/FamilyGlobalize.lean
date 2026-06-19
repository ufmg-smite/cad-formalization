import Cad.Multivariate.ProjectionTheorem.Generalized.DiscNormalForm

/-!
# M5 — globalizing a germ-analytic family by a radial cutoff

The covering pipeline (`section_card_le_one`, M4) needs a family whose coefficients are **globally
continuous** (for the properness/closedness of the root variety) and **analytic on a ball** (for the
local trivialisations). A Weierstrass family `q` coming from the Zariski axiom only has coefficients
analytic *at `0`* (`hc`), and `q` is otherwise an arbitrary total function. Global analyticity is
unattainable, but we don't need it: compose `q` with the radial retraction `g` onto a closed ball
`closedBall 0 r` (where the coefficients are analytic), giving `q̃ := q ∘ g` which

* is monic of constant degree `d` everywhere (inherited from `q`, which is monic everywhere);
* has globally **continuous** coefficients (`g` is continuous into the ball, where the coefficients are
  continuous);
* agrees with `q` on `ball 0 r` (there `g = id`), so it is analytic there and shares all germ data at
  `0` (roots, separability, irreducibility).

This is the bridge feeding the localized M4 chain from the germ-level Zariski hypotheses.
-/

noncomputable section

open Polynomial Filter Metric Set
open scoped Topology

namespace FamilyGlobalize

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Radial-cutoff globalization.** A family `q`, monic of constant degree `d` with coefficients
analytic at `0`, admits a globalization `q̃` (= `q` composed with a retraction onto a small closed ball)
that is monic of degree `d` everywhere, has globally continuous coefficients, and agrees with `q`
(hence is analytic) on `ball 0 r`. Works over any complex normed space `E`. -/
theorem exists_globalized_family {d : ℕ} (q : E → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hc : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (0 : E)) :
    ∃ (qt : E → Polynomial ℂ) (r : ℝ), 0 < r ∧
      (∀ y, (qt y).Monic) ∧ (∀ y, (qt y).natDegree = d) ∧
      (∀ i, Continuous (fun y => (qt y).coeff i)) ∧
      (∀ y ∈ ball (0 : E) r, qt y = q y) ∧
      (∀ i, ∀ y ∈ ball (0 : E) r,
        AnalyticAt ℂ (fun z => (qt z).coeff i) y) := by
  classical
  -- a uniform radius `ρ` on which all low coefficients are analytic
  have hev : ∀ᶠ y in 𝓝 (0 : E),
      ∀ i ∈ Finset.range d, AnalyticAt ℂ (fun z => (q z).coeff i) y :=
    (Finset.eventually_all (Finset.range d)).mpr (fun i _ => (hc i).eventually_analyticAt)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set r : ℝ := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hr]; linarith
  -- the retraction `g` onto `closedBall 0 r`
  set g : E → E := fun y => (r / max r ‖y‖) • y with hg
  have hmax_pos : ∀ y : E, 0 < max r ‖y‖ := fun y => lt_of_lt_of_le hr0 (le_max_left _ _)
  have hg_cont : Continuous g := by
    simp only [hg]
    exact (continuous_const.div (continuous_const.max continuous_norm)
      (fun y => (hmax_pos y).ne')).smul continuous_id
  have hg_id : ∀ y : E, ‖y‖ < r → g y = y := by
    intro y hy
    simp only [hg, max_eq_left hy.le, div_self hr0.ne', one_smul]
  have hg_norm : ∀ y : E, ‖g y‖ ≤ r := by
    intro y
    simp only [hg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr0.le (hmax_pos y).le), div_mul_eq_mul_div]
    rw [div_le_iff₀ (hmax_pos y)]
    exact mul_le_mul_of_nonneg_left (le_max_right r ‖y‖) hr0.le
  have hg_ball : ∀ y : E, dist (g y) 0 < ρ := fun y => by
    rw [dist_zero_right]; exact lt_of_le_of_lt (hg_norm y) hrρ
  -- coefficient facts of `q` (constant top / vanishing high coefficients)
  have hcoeff_top : ∀ y, (q y).coeff d = 1 := fun y => by
    have := (hmonic y).coeff_natDegree; rwa [hdeg y] at this
  have hcoeff_high : ∀ i, d < i → ∀ y, (q y).coeff i = 0 := fun i hi y =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg y]; exact hi)
  -- analyticity of the `q`-coefficients at any point of `ball 0 ρ`
  have hq_an : ∀ i, ∀ z : E, dist z 0 < ρ →
      AnalyticAt ℂ (fun w => (q w).coeff i) z := by
    intro i z hz
    rcases lt_trichotomy i d with hlt | heq | hgt
    · exact hball hz i (Finset.mem_range.mpr hlt)
    · subst heq
      exact (analyticAt_congr (Filter.Eventually.of_forall hcoeff_top)).mpr analyticAt_const
    · exact (analyticAt_congr (Filter.Eventually.of_forall (hcoeff_high i hgt))).mpr analyticAt_const
  refine ⟨fun y => q (g y), r, hr0, fun y => hmonic (g y), fun y => hdeg (g y), ?_, ?_, ?_⟩
  · -- global continuity of each coefficient `(q (g ·)).coeff i`
    intro i
    have hcont_on : ContinuousOn (fun w => (q w).coeff i) (closedBall (0 : E) r) :=
      fun z hz => ((hq_an i z (lt_of_le_of_lt (mem_closedBall.mp hz) hrρ)).continuousAt).continuousWithinAt
    exact hcont_on.comp_continuous hg_cont (fun y => mem_closedBall_zero_iff.mpr (hg_norm y))
  · intro y hy; show q (g y) = q y; rw [hg_id y (mem_ball_zero_iff.mp hy)]
  · intro i y hy
    have hyb : ‖y‖ < r := mem_ball_zero_iff.mp hy
    have heq : (fun z => (q (g z)).coeff i) =ᶠ[𝓝 y] (fun z => (q z).coeff i) := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      rw [hg_id z (mem_ball_zero_iff.mp hz)]
    exact (hq_an i y (by rw [dist_zero_right]; exact lt_trans hyb hrρ)).congr heq.symm

end FamilyGlobalize
