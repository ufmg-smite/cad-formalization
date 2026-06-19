import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticOrderPoly
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassZariskiAxioms

/-!
# Convergent Weierstrass preparation, derived from Weierstrass division

`weierstrass_preparation_analytic` is **derived** here from the single Phase-C axiom
`weierstrass_division`, by the classical corollary: divide `tᵐ` by the `t`-regular germ `G`
(`tᵐ = q·G + r`), then show the quotient `q` is a unit and the remainder coefficients vanish at `0`
(the "unit argument"), so `G = q⁻¹ · (tᵐ − r)` with `tᵐ − r` a Weierstrass polynomial. This collapses
Phase C to the single axiom `weierstrass_division`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **Convergent Weierstrass preparation (Phase C).** Derived from `weierstrass_division`. -/
theorem weierstrass_preparation_analytic {s e : ℕ}
    (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hm : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ (u : CParam s e × ℂ → ℂ) (a : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      G =ᶠ[𝓝 0] fun wt => u wt * (weierstrassPoly m a wt.1).eval wt.2 := by
  classical
  -- 1. divide `tᵐ` by `G`
  have hF : AnalyticAt ℂ (fun wt : CParam s e × ℂ => wt.2 ^ m) 0 := analyticAt_snd.pow m
  obtain ⟨q, ρ, hq, hρ, hdiv⟩ := (weierstrass_division G hG m hm).1 _ hF
  set a : Fin m → (CParam s e → ℂ) := fun i w => -(ρ i w) with ha_def
  have ha_an : ∀ i, AnalyticAt ℂ (a i) 0 := fun i => (hρ i).neg
  have hwp_eval : ∀ (w : CParam s e) (t : ℂ),
      (weierstrassPoly m a w).eval t = t ^ m + ∑ i : Fin m, a i w * t ^ (i : ℕ) := by
    intro w t
    simp [weierstrassPoly, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]
  -- 2. restrict to the line `w = 0`
  have htend : Tendsto (fun t : ℂ => ((0 : CParam s e), t)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℂ => ((0 : CParam s e), t)) := by fun_prop
    simpa using hc.tendsto (0 : ℂ)
  have hline : (fun t : ℂ => t ^ m) =ᶠ[𝓝 0]
      fun t => q ((0 : CParam s e), t) * G ((0 : CParam s e), t)
        + ∑ i : Fin m, ρ i 0 * t ^ (i : ℕ) := by
    simpa using htend.eventually hdiv
  -- 3. the single-variable polynomial `Ep`
  set c : Fin m → ℂ := fun i => a i 0 with hc_def
  set Ep : Polynomial ℂ := X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ) with hEp_def
  have hEp_coeff : ∀ j : ℕ, Ep.coeff j
      = (if j = m then 1 else 0) + ∑ i : Fin m, c i * (if j = (i : ℕ) then 1 else 0) := by
    intro j
    rw [hEp_def, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hcoeff_m : Ep.coeff m = 1 := by
    rw [hEp_coeff, Finset.sum_eq_zero fun i _ => by rw [if_neg (ne_of_gt i.isLt), mul_zero]]
    simp
  have hcoeff_lt : ∀ i : Fin m, Ep.coeff (i : ℕ) = c i := by
    intro i
    rw [hEp_coeff, if_neg (ne_of_lt i.isLt), zero_add,
      Finset.sum_eq_single i (fun k _ hk => by rw [if_neg (fun h => hk (Fin.ext h.symm)), mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, mul_one]
  have hEp_ne : Ep ≠ 0 := fun h => by simp [h] at hcoeff_m
  have hndeg : Ep.natDegree = m := by
    refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_m]; exact one_ne_zero))
    rw [hEp_coeff, if_neg (ne_of_gt hj), zero_add]
    exact Finset.sum_eq_zero fun i _ => by
      rw [if_neg (ne_of_gt (lt_trans i.isLt hj)), mul_zero]
  have hEp_eval : ∀ t : ℂ, Ep.eval t = t ^ m + ∑ i : Fin m, c i * t ^ (i : ℕ) := by
    intro t
    simp [hEp_def, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]
  have hprod : (fun t : ℂ => Ep.eval t) =ᶠ[𝓝 0]
      fun t => q ((0 : CParam s e), t) * G ((0 : CParam s e), t) := by
    filter_upwards [hline] with t ht
    have hzs : ∑ i : Fin m, c i * t ^ (i : ℕ) + ∑ i : Fin m, ρ i 0 * t ^ (i : ℕ) = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [hc_def, ha_def]; ring
    rw [hEp_eval]; linear_combination ht + hzs
  -- 4. order argument
  have hGl : AnalyticAt ℂ (fun t : ℂ => G ((0 : CParam s e), t)) 0 :=
    hG.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hql : AnalyticAt ℂ (fun t : ℂ => q ((0 : CParam s e), t)) 0 :=
    hq.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hord_eq : (Ep.rootMultiplicity 0 : ℕ∞)
      = analyticOrderAt (fun t : ℂ => q ((0 : CParam s e), t)) 0 + (m : ℕ∞) := by
    have h2 : analyticOrderAt (fun t : ℂ => Ep.eval t) 0
        = analyticOrderAt (fun t : ℂ => q ((0 : CParam s e), t)) 0
          + analyticOrderAt (fun t : ℂ => G ((0 : CParam s e), t)) 0 := by
      rw [analyticOrderAt_congr hprod]; exact analyticOrderAt_mul hql hGl
    rw [← analyticOrderAt_polynomial_eval hEp_ne 0, h2, hm]
  have hrm_le : Ep.rootMultiplicity 0 ≤ m := by
    have h := Polynomial.natDegree_le_of_dvd (pow_rootMultiplicity_dvd Ep 0) hEp_ne
    rwa [Polynomial.natDegree_pow, show (X - C (0 : ℂ)) = X by simp, Polynomial.natDegree_X,
      mul_one, hndeg] at h
  have hmt : (m : ℕ∞) ≠ ⊤ := ENat.coe_ne_top m
  have hoq0 : analyticOrderAt (fun t : ℂ => q ((0 : CParam s e), t)) 0 = 0 := by
    have hle : analyticOrderAt (fun t : ℂ => q ((0 : CParam s e), t)) 0 + (m : ℕ∞)
        ≤ 0 + (m : ℕ∞) := by
      rw [zero_add, ← hord_eq]; exact_mod_cast hrm_le
    exact le_antisymm ((ENat.add_le_add_iff_right hmt).mp hle) (zero_le _)
  have hrm_eq : Ep.rootMultiplicity 0 = m := by
    have : (Ep.rootMultiplicity 0 : ℕ∞) = (m : ℕ∞) := by rw [hord_eq, hoq0, zero_add]
    exact_mod_cast this
  -- 5. unit + vanishing coefficients
  have hq0 : q 0 ≠ 0 := by
    have h := (hql.analyticOrderAt_eq_zero).mp hoq0
    exact h
  have hρ0 : ∀ i, ρ i 0 = 0 := by
    have hdvd : (X : Polynomial ℂ) ^ m ∣ Ep := by
      have h := pow_rootMultiplicity_dvd Ep 0
      rwa [hrm_eq, show (X - C (0 : ℂ)) = X by simp] at h
    intro i
    have hc0 : c i = 0 := by
      rw [← hcoeff_lt i]; exact Polynomial.X_pow_dvd_iff.mp hdvd (i : ℕ) i.isLt
    have : a i 0 = 0 := hc0
    rw [ha_def] at this; simpa using this
  -- 6. assemble
  refine ⟨fun wt => (q wt)⁻¹, a, hq.inv hq0, ?_, ha_an, ?_, ?_⟩
  · simpa using inv_ne_zero hq0
  · intro i; rw [ha_def]; show -(ρ i 0) = 0; rw [hρ0 i, neg_zero]
  · have hq_ne : ∀ᶠ wt in 𝓝 (0 : CParam s e × ℂ), q wt ≠ 0 := hq.continuousAt.eventually_ne hq0
    filter_upwards [hdiv, hq_ne] with wt hd hne
    rw [hwp_eval]
    have hzs2 : ∑ i : Fin m, a i wt.1 * wt.2 ^ (i : ℕ)
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ) = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [ha_def]; ring
    have hqG : q wt * G wt = wt.2 ^ m + ∑ i : Fin m, a i wt.1 * wt.2 ^ (i : ℕ) := by
      linear_combination -hd - hzs2
    rw [← hqG, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end
