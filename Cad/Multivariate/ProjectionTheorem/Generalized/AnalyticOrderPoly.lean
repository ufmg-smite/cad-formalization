import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic

/-!
# Analytic order of a polynomial = root multiplicity

`analyticOrderAt_polynomial_eval`: for a nonzero complex polynomial `p`, the analytic vanishing order
of `z ↦ p.eval z` at `z₀` equals `p.rootMultiplicity z₀`. This is the static fact that lets a
cluster's localization datum (`analyticOrderAt … 0 = m`) be read off as a polynomial root
multiplicity — internalizing the last hypothesis of `cluster_from_real`.
-/

open Polynomial
open scoped Topology

/-- The analytic order of a nonzero polynomial's evaluation equals its root multiplicity. -/
lemma analyticOrderAt_polynomial_eval {p : Polynomial ℂ} (hp : p ≠ 0) (z₀ : ℂ) :
    analyticOrderAt (fun z => p.eval z) z₀ = (p.rootMultiplicity z₀ : ℕ∞) := by
  obtain ⟨g, hpg, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp z₀
  have hg0 : g.eval z₀ ≠ 0 := fun h => hndvd (dvd_iff_isRoot.mpr h)
  have han : AnalyticAt ℂ (fun z => p.eval z) z₀ :=
    (AnalyticOnNhd.eval_polynomial p) z₀ (Set.mem_univ z₀)
  rw [han.analyticOrderAt_eq_natCast]
  refine ⟨fun z => g.eval z, (AnalyticOnNhd.eval_polynomial g) z₀ (Set.mem_univ z₀), hg0, ?_⟩
  filter_upwards with z
  show p.eval z = (z - z₀) ^ p.rootMultiplicity z₀ • g.eval z
  conv_lhs => rw [hpg]
  rw [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]

/-- Real-polynomial form: the analytic order of `(p.map (algebraMap ℝ ℂ)).eval` at a real point
equals the real root multiplicity. -/
lemma analyticOrderAt_polynomial_eval_ofReal {p : Polynomial ℝ} (hp : p ≠ 0) (x₀ : ℝ) :
    analyticOrderAt (fun z => (p.map (algebraMap ℝ ℂ)).eval z) (algebraMap ℝ ℂ x₀)
      = (p.rootMultiplicity x₀ : ℕ∞) := by
  have hmap_ne : p.map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp
  rw [analyticOrderAt_polynomial_eval hmap_ne (algebraMap ℝ ℂ x₀),
    ← Polynomial.eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective x₀]

/-- A unit factor doesn't change the analytic order: if `f =ᶠ u * h` with `u α ≠ 0`, then `f` and `h`
have the same analytic order at `α`. -/
lemma analyticOrderAt_eq_of_unit_factor {f h u : ℂ → ℂ} {α : ℂ}
    (hu : AnalyticAt ℂ u α) (huα : u α ≠ 0) (hh : AnalyticAt ℂ h α)
    (hfac : f =ᶠ[𝓝 α] u * h) :
    analyticOrderAt f α = analyticOrderAt h α := by
  rw [analyticOrderAt_congr hfac, analyticOrderAt_mul hu hh,
    hu.analyticOrderAt_eq_zero.mpr huα, zero_add]
