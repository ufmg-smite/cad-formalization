import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The `ℂⁿ` multi-index term — foundation of the `n`-variable SCV bridge

The polarization-free route to the `ℂⁿ` holomorphy⇒analyticity bridge generalizes the proven `ℂ²`
`scvTerm`/`scvCoeff` construction to `ℕⁿ` multi-indices with **scalar** coefficients (so the
coefficient bounds are clean iterated 1-variable Cauchy estimates — no operator-norm polarization).

This file builds the foundational block: `mtTerm c assign`, the asymmetric `N`-multilinear map on
`Fin n → ℂ` (= `ℂⁿ`) whose `i`-th slot reads coordinate `assign i`. Its diagonal at `y` is
`c · ∏ᵢ y (assign i)` (so for an `assign` realizing a multi-index `α`, the diagonal is `c · ∏ⱼ yⱼ^αⱼ`),
and its operator norm is `≤ ‖c‖`. This generalizes `CSCVCombination.mlTerm`/`CSCVBridge.scvTerm` from
2 coordinates (`fst`/`snd`) to `n` coordinates (Pi-projections).
-/

noncomputable section

open ContinuousMultilinearMap

/-- The `j`-th coordinate projection `ℂⁿ → ℂ` has operator norm `≤ 1`. -/
theorem norm_proj_pi_le {n : ℕ} (i : Fin n) :
    ‖(ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

/-- The asymmetric multi-index term: the `N`-multilinear map on `ℂⁿ` whose `i`-th argument is read in
coordinate `assign i`. Diagonal `c · ∏ᵢ y(assign i)`, norm `≤ ‖c‖`. -/
def mtTerm {N n : ℕ} (c : ℂ) (assign : Fin N → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N => Fin n → ℂ) ℂ :=
  c • (ContinuousMultilinearMap.mkPiAlgebraFin ℂ N ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (assign i))

/-- **Diagonal of `mtTerm`:** `mtTerm c assign (fun _ => y) = c · ∏ᵢ y (assign i)`. -/
theorem mtTerm_apply_diag {N n : ℕ} (c : ℂ) (assign : Fin N → Fin n) (y : Fin n → ℂ) :
    mtTerm c assign (fun _ => y) = c * ∏ i : Fin N, y (assign i) := by
  rw [mtTerm, ContinuousMultilinearMap.smul_apply, compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  simp [smul_eq_mul]

/-- **Operator-norm bound:** `‖mtTerm c assign‖ ≤ ‖c‖`. -/
theorem norm_mtTerm_le {N n : ℕ} (c : ℂ) (assign : Fin N → Fin n) : ‖mtTerm c assign‖ ≤ ‖c‖ := by
  rw [mtTerm, norm_smul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  refine (norm_compContinuousLinearMap_le _ _).trans ?_
  have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ N ℂ‖ ≤ 1 :=
    norm_mkPiAlgebraFin_le.trans (by rw [norm_one, max_self])
  exact mul_le_one₀ hmk (Finset.prod_nonneg fun i _ => norm_nonneg _)
    (Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_proj_pi_le _)

end
