import Cad.Multivariate.ProjectionTheorem.Generalized.PolyOfFamily
import Cad.Multivariate.ProjectionTheorem.Generalized.MembershipDescent
import Cad.Multivariate.ProjectionTheorem.Generalized.SectionOrder

/-!
# Complexification glue (A3)

Helpers connecting `complexify_pseudopoly_prod`'s output (a family `gℂ : CParam → ℂ[t]` with
coefficient-wise real-slice agreements) to the function-ring polynomial `polyOfFamily N gℂ` used by
the descent:
* `analyticCoeffs_polyOfFamily` — assembled polynomial has analytic coefficients;
* `map_agree_of_complexify` — the `Polynomial.map`-level real-slice agreement required by
  `complexify_membership`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- The assembled function-ring polynomial has analytic coefficients. -/
lemma analyticCoeffs_polyOfFamily (N : ℕ) (gℂ : CParam s e → Polynomial ℂ)
    (h : ∀ i, AnalyticAt ℂ (fun z => (gℂ z).coeff i) 0) :
    AnalyticCoeffs (polyOfFamily N gℂ) := by
  intro j
  rw [polyOfFamily_coeff]
  by_cases hj : j ≤ N
  · simp only [hj, if_true]; exact h j
  · simp only [hj, if_false]; exact analyticAt_const

/-- `Polynomial.map`-level real-slice agreement: evaluating `polyOfFamily N gℂ`'s coefficients at a
real point recovers the real family mapped through `ofReal`. -/
lemma map_agree_of_complexify (N : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (gℂ : CParam s e → Polynomial ℂ) (hdeg : ∀ w, (g w).natDegree ≤ N)
    (hagree : ∀ i, ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      (gℂ (prodEmbedCLM s e w)).coeff i = Complex.ofReal ((g w).coeff i)) :
    ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      (polyOfFamily N gℂ).map (Pi.evalRingHom (fun _ => ℂ) (prodEmbedCLM s e w))
        = (g w).map (algebraMap ℝ ℂ) := by
  have hall : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      ∀ i ∈ Finset.range (N + 1), (gℂ (prodEmbedCLM s e w)).coeff i = Complex.ofReal ((g w).coeff i) :=
    (eventually_all_finset _).mpr (fun i _ => hagree i)
  filter_upwards [hall] with w hw
  ext j
  rw [Polynomial.coeff_map, Polynomial.coeff_map, polyOfFamily_coeff]
  by_cases hj : j ≤ N
  · simp only [hj, if_true]
    show (gℂ (prodEmbedCLM s e w)).coeff j = algebraMap ℝ ℂ ((g w).coeff j)
    rw [hw j (Finset.mem_range.mpr (by omega)), Complex.coe_algebraMap]
  · simp only [hj, if_false]
    show (0 : ℂ) = algebraMap ℝ ℂ ((g w).coeff j)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg w) (by omega)), map_zero]

end
