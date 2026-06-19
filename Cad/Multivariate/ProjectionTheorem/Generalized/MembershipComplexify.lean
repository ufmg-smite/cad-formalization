import Cad.Multivariate.ProjectionTheorem.Generalized.MembershipDescent
import Cad.Multivariate.ProjectionTheorem.Generalized.SectionOrder

/-!
# Membership-complexification bridge (A3 item (b))

`complexify_membership` lifts the **real** analytic-cofactor elimination membership
`C (P w) = A w · g w + B w · g'(w)` (near `0`) to the **eventual `polyToFun`** form consumed by
`single_cluster_from_weierstrass`:

  `polyToFun (C Pℂ) =ᶠ polyToFun Aℂ · polyToFun g + polyToFun Bℂ · polyToFun g'`.

The exact function-ring polynomial identity is *not* achievable (complexification is local), so the
target is the eventual form. The proof works at the `Polynomial.map` level: the difference polynomial
`D` maps to `0` under coefficient-evaluation at every real point (real identity), so each coefficient
of `D` vanishes on the real slice, hence (CParam identity theorem) near `0`, hence `polyToFun D =ᶠ 0`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- If every coefficient of `D` vanishes near `0`, then `polyToFun D` vanishes near `0`. -/
lemma polyToFun_eventuallyEq_zero_of_coeffs (D : (CParam s e → ℂ)[X])
    (hD : ∀ k, (D.coeff k) =ᶠ[𝓝 (0 : CParam s e)] 0) :
    polyToFun s e D =ᶠ[𝓝 (0 : CParam s e × ℂ)] 0 := by
  have hev : ∀ᶠ z in 𝓝 (0 : CParam s e), ∀ k ∈ D.support, D.coeff k z = 0 :=
    (eventually_all_finset D.support).mpr (fun k _ => hD k)
  have hmap0 : ∀ᶠ z in 𝓝 (0 : CParam s e),
      D.map (Pi.evalRingHom (fun _ => ℂ) z) = 0 := by
    filter_upwards [hev] with z hz
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hk : k ∈ D.support
    · show D.coeff k z = 0; exact hz k hk
    · have : D.coeff k = 0 := by simpa [Polynomial.mem_support_iff] using hk
      rw [this]; rfl
  have hfst : Filter.Tendsto (Prod.fst : CParam s e × ℂ → CParam s e)
      (𝓝 0) (𝓝 0) := by simpa using continuous_fst.tendsto (0 : CParam s e × ℂ)
  filter_upwards [hfst.eventually hmap0] with zt hzt
  show polyToFun s e D zt = (0 : CParam s e × ℂ → ℂ) zt
  rw [polyToFun_apply, hzt, Polynomial.eval_zero]; rfl

/-- **Membership-complexification bridge.** From the real analytic-cofactor membership and the
`Polynomial.map`-level real-slice agreements of the complexified data, produce the eventual
`polyToFun` membership required by `single_cluster_from_weierstrass`. -/
theorem complexify_membership
    (g A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ)
    (g_poly Aℂ Bℂ : (CParam s e → ℂ)[X]) (Pℂ : CParam s e → ℂ)
    (hg_an : AnalyticCoeffs g_poly) (hA_an : AnalyticCoeffs Aℂ) (hB_an : AnalyticCoeffs Bℂ)
    (hP_an : AnalyticAt ℂ Pℂ 0)
    (hg_agree : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      g_poly.map (Pi.evalRingHom (fun _ => ℂ) (prodEmbedCLM s e w)) = (g w).map (algebraMap ℝ ℂ))
    (hA_agree : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Aℂ.map (Pi.evalRingHom (fun _ => ℂ) (prodEmbedCLM s e w)) = (A w).map (algebraMap ℝ ℂ))
    (hB_agree : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Bℂ.map (Pi.evalRingHom (fun _ => ℂ) (prodEmbedCLM s e w)) = (B w).map (algebraMap ℝ ℂ))
    (hP_agree : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Pℂ (prodEmbedCLM s e w) = algebraMap ℝ ℂ (P w))
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w)) :
    polyToFun s e (Polynomial.C Pℂ) =ᶠ[𝓝 0] fun zt =>
        polyToFun s e Aℂ zt * polyToFun s e g_poly zt
      + polyToFun s e Bℂ zt * polyToFun s e (derivative g_poly) zt := by
  set D : (CParam s e → ℂ)[X] :=
    Polynomial.C Pℂ - (Aℂ * g_poly + Bℂ * derivative g_poly) with hD
  -- `D` has analytic coefficients
  have hD_an : AnalyticCoeffs D :=
    analyticCoeffs_sub (analyticCoeffs_C hP_an)
      (analyticCoeffs_add (analyticCoeffs_mul hA_an hg_an)
        (analyticCoeffs_mul hB_an (analyticCoeffs_derivative hg_an)))
  -- each coefficient of `D` vanishes near `0`
  have hDcoeff : ∀ k, (D.coeff k) =ᶠ[𝓝 (0 : CParam s e)] 0 := by
    intro k
    refine eventuallyEq_zero_of_real_eq_zero_prod (D.coeff k) (hD_an k) ?_
    filter_upwards [hg_agree, hA_agree, hB_agree, hP_agree, hmem] with w hgw hAw hBw hPw hmemw
    set ev := Pi.evalRingHom (fun _ : CParam s e => ℂ) (prodEmbedCLM s e w) with hev
    have hDmap : D.map ev = 0 := by
      have key : (Polynomial.C (P w)).map (algebraMap ℝ ℂ)
          = (A w * g w + B w * derivative (g w)).map (algebraMap ℝ ℂ) := by rw [hmemw]
      rw [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        ← Polynomial.derivative_map] at key
      rw [hD, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_mul, ← Polynomial.derivative_map, hgw, hAw, hBw]
      rw [show ev Pℂ = Pℂ (prodEmbedCLM s e w) from rfl, hPw, sub_eq_zero]
      exact key
    show D.coeff k (prodEmbedCLM s e w) = 0
    have hcm : D.coeff k (prodEmbedCLM s e w) = (D.map ev).coeff k := by
      rw [Polynomial.coeff_map]; rfl
    rw [hcm, hDmap, Polynomial.coeff_zero]
  -- hence `polyToFun D =ᶠ 0`, which is the claim after expanding the ring hom
  have hpolyD : polyToFun s e D =ᶠ[𝓝 0] 0 := polyToFun_eventuallyEq_zero_of_coeffs D hDcoeff
  filter_upwards [hpolyD] with zt hzt
  have hexp : polyToFun s e D zt = polyToFun s e (Polynomial.C Pℂ) zt
      - (polyToFun s e Aℂ zt * polyToFun s e g_poly zt
        + polyToFun s e Bℂ zt * polyToFun s e (derivative g_poly) zt) := by
    rw [hD, map_sub, map_add, map_mul, map_mul]; rfl
  rw [hexp, Pi.zero_apply] at hzt
  exact sub_eq_zero.mp hzt

end
