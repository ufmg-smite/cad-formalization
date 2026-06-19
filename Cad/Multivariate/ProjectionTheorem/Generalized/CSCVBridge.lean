import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Cad.Multivariate.ProjectionTheorem.Generalized.CParamIntegral

/-!
# Several-complex-variables bridge — Step 4 build (WIP)

This file builds the missing several-complex-variables infrastructure needed to discharge `osgood`
(equivalently, the bridge `jointly ℂ-differentiable ⇒ analytic` on `ℂⁿ`). Per `CBridge.lean`, the
polydisc–Cauchy route is proved through the iterated/torus Cauchy representation (`bridge_torus_repr`);
what remains ("Step 4") is to **expand the Cauchy kernel into a several-variable power series** and
package it as a `HasFPowerSeriesOnBall` on `ℂ²` (then `ℂⁿ`).

Foundation stone: the **Cauchy-kernel geometric expansion** `(ζ − z)⁻¹ = ∑_j (z−z₀)^j/(ζ−z₀)^{j+1}`
for `‖z − z₀‖ < ‖ζ − z₀‖`. This is the 1-variable analytic engine; the several-variable kernel is its
(two-fold) product, integrated term-by-term over the torus.
-/

noncomputable section

open Complex Metric
open scoped Real Topology




/-- **Step 3 (one variable): the Cauchy integral expands as a power series with explicit integral
coefficients.** For a slice `g = f(·, w)` holomorphic on the closed disc `|ζ − z₀| ≤ r`,
`2πi · f(z,w) = ∑_j ∮_ζ ((z−z₀)/(ζ−z₀))^j·(ζ−z₀)⁻¹·f(ζ,w)` for `‖z−z₀‖ < r`. This is Mathlib's
`hasSum_two_pi_I_cauchyPowerSeries_integral` (the 1-var integral–sum swap, done by dominated
convergence) combined with the Cauchy integral formula for the value. -/
theorem hasSum_z_expansion {f : ℂ × ℂ → ℂ} {z₀ : ℂ} {r : ℝ} {w : ℂ}
    (hcont : ContinuousOn (fun ζ => f (ζ, w)) (closedBall z₀ r))
    (hdiff : ∀ ζ ∈ ball z₀ r, DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ)
    {z : ℂ} (hz : ‖z - z₀‖ < r) :
    HasSum (fun j : ℕ => ∮ ζ in C(z₀, r), ((z - z₀) / (ζ - z₀)) ^ j • (ζ - z₀)⁻¹ • f (ζ, w))
      ((2 * π * I : ℂ) • f (z, w)) := by
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hz
  have hci : CircleIntegrable (fun ζ => f (ζ, w)) z₀ r :=
    (hcont.mono sphere_subset_closedBall).circleIntegrable hrpos.le
  have hzmem : z ∈ ball z₀ r := mem_ball_iff_norm.mpr hz
  have hsum := hasSum_two_pi_I_cauchyPowerSeries_integral
    (f := fun ζ => f (ζ, w)) (c := z₀) (R := r) (w := z - z₀) hci hz
  rw [show z₀ + (z - z₀) = z from by ring,
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable Set.countable_empty hzmem hcont
      (fun ζ hζ => hdiff ζ hζ.1)] at hsum
  exact hsum

/-! ## Step 4: packaging into a `FormalMultilinearSeries` on `ℂ²`

The double-indexed Cauchy coefficients `c j k` are packaged into a several-variable power series. The
`n`-th term is `∑_{j+k=n} c_{jk}·mⱼ`, where `mⱼ` is the (asymmetric) monomial multilinear map reading
the first `j` slots' coordinate `1` and the rest's coordinate `2`. Its diagonal value is
`mⱼ(y,…,y) = y.1^j·y.2^{n-j}` — **no binomial coefficient**, which is what makes this construction
work. -/

open ContinuousMultilinearMap in



/-- **Clean `z`-expansion** (coefficients pulled out of the integral): for a holomorphic `z`-slice,
`2πi·f(z,w) = ∑_j (z−z₀)^j · B_j(w)` with `B_j(w) = ∮_ζ (ζ−z₀)^{-(j+1)}·f(ζ,w)`. This is the form that
combines with the `w`-expansion of each coefficient `B_j` (analytic in `w`) toward the double series. -/
theorem hasSum_z_expansion' {f : ℂ × ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hcont : ContinuousOn (fun ζ => f (ζ, w)) (closedBall z₀ r))
    (hdiff : ∀ ζ ∈ ball z₀ r, DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ)
    {z : ℂ} (hz : ‖z - z₀‖ < r) :
    HasSum (fun j : ℕ => (z - z₀) ^ j • ∮ ζ in C(z₀, r), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
      ((2 * π * I : ℂ) • f (z, w)) := by
  have hbase := hasSum_z_expansion hcont hdiff hz
  have hfeq : (fun j : ℕ => (z - z₀) ^ j • ∮ ζ in C(z₀, r), ((ζ - z₀) ^ (j + 1))⁻¹ • f (ζ, w))
      = fun j : ℕ => ∮ ζ in C(z₀, r), ((z - z₀) / (ζ - z₀)) ^ j • (ζ - z₀)⁻¹ • f (ζ, w) := by
    funext j
    rw [← circleIntegral.integral_smul]
    refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
    have hζ0 : ζ - z₀ ≠ 0 := by
      rw [mem_sphere_iff_norm] at hζ
      intro h; rw [h, norm_zero] at hζ; exact (ne_of_lt hr) hζ
    simp only [smul_eq_mul]; rw [div_pow, pow_succ, mul_inv]; ring
  rw [hfeq]; exact hbase

open Finset in






/-- `‖2πI‖ = 2π`. -/
theorem norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [show (2 * π * I : ℂ) = ((2 * π : ℝ) : ℂ) * I by push_cast; ring, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]




/-- **One-variable Cauchy power-series expansion**, obtained from `hasSum_z_expansion'` by ignoring
the first coordinate (`f := fun p => g p.1`). -/
theorem hasSum_w_expansion {g : ℂ → ℂ} {w₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn g (closedBall w₀ r))
    (hdiff : ∀ η ∈ ball w₀ r, DifferentiableAt ℂ g η)
    {w : ℂ} (hw : ‖w - w₀‖ < r) :
    HasSum (fun k : ℕ => (w - w₀) ^ k • ∮ η in C(w₀, r), ((η - w₀) ^ (k + 1))⁻¹ • g η)
      ((2 * π * I : ℂ) • g w) :=
  hasSum_z_expansion' (f := fun p : ℂ × ℂ => g p.1) (w := w₀) hr hcont hdiff hw














end
