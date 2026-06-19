import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDivision

/-!
# A3 plumbing: family-of-polynomials ↔ function-ring polynomial

The complexification machinery (`complexify_pseudopoly`) produces a *family* `gℂ : CParam → ℂ[t]`,
but the descent works with a *function-ring polynomial* `g : (CParam → ℂ)[X]`. `polyOfFamily`
assembles the former into the latter, and `polyToFun_polyOfFamily` shows the two evaluate compatibly
through the `polyToFun` bridge:

`polyToFun (polyOfFamily N gℂ) (z, t) = (gℂ z).eval t`.

This connects A3's complexified `gℂ`/cofactors to the `polyToFun`-based descent inputs.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- Assemble a degree-`≤ N` family of `ℂ`-polynomials into a polynomial over the function ring. -/
def polyOfFamily (N : ℕ) (gℂ : CParam s e → Polynomial ℂ) : (CParam s e → ℂ)[X] :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (fun z => (gℂ z).coeff i)

lemma polyOfFamily_coeff (N : ℕ) (gℂ : CParam s e → Polynomial ℂ) (j : ℕ) :
    (polyOfFamily N gℂ).coeff j = if j ≤ N then (fun z => (gℂ z).coeff j) else 0 := by
  rw [polyOfFamily, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (N + 1)) j (fun i => (fun z => (gℂ z).coeff i))]
  simp [Finset.mem_range]

end
