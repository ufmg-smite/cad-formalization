import Cad.Multivariate.ProjectionTheorem.Generalized.MembershipDescent

/-!
# Analyticity of `weierstrassResFun` and `weierstrassDiscFn`

The resultant/discriminant functions of the Weierstrass family are analytic at `0` — they are ring
expressions (a Sylvester determinant) in the analytic coefficients `aᵢ`. Proved via the same
`toSubring` + `resultant_map_map` technique used for `coeff_divByMonic_analyticAt`: the resultant of
two `AnalyticAtSubring`-coefficient polynomials lands in `AnalyticAtSubring`.

These discharge the `hres_an`/`hdisc_an` analyticity hypotheses of
`DiscOrder.weierstrassDisc_order_const_along_section`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- A polynomial with analytic-at-`0` coefficients has its `coeffs` finset inside the analytic-at-`0`
subring. -/
lemma AnalyticCoeffs.coeffs_subset {p : (CParam s e → ℂ)[X]} (hp : AnalyticCoeffs p) :
    (↑p.coeffs : Set (CParam s e → ℂ)) ⊆ ↑(AnalyticAtSubring s e) := by
  intro x hx; obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx; exact hp n

/-- The resultant function of the Weierstrass family is analytic at `0`. -/
lemma weierstrassResFun_analyticAt {m : ℕ} (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (weierstrassResFun m a) 0 := by
  set S := AnalyticAtSubring s e
  have hwPF : AnalyticCoeffs (weierstrassPolyFun m a) := analyticCoeffs_weierstrassPolyFun a ha_an
  have hderiv : AnalyticCoeffs (derivative (weierstrassPolyFun m a)) := analyticCoeffs_derivative hwPF
  set wPF_S := (weierstrassPolyFun m a).toSubring S hwPF.coeffs_subset with hwPF_S
  set deriv_S := (derivative (weierstrassPolyFun m a)).toSubring S hderiv.coeffs_subset with hderiv_S
  have hmap1 : wPF_S.map S.subtype = weierstrassPolyFun m a := map_toSubring _ _ _
  have hmap2 : deriv_S.map S.subtype = derivative (weierstrassPolyFun m a) := map_toSubring _ _ _
  have h1 : weierstrassResFun m a = S.subtype (Polynomial.resultant wPF_S deriv_S m (m - 1)) := by
    have hr := Polynomial.resultant_map_map wPF_S deriv_S m (m - 1) S.subtype
    rw [hmap1, hmap2] at hr
    exact hr
  rw [h1]
  exact (Polynomial.resultant wPF_S deriv_S m (m - 1)).2

/-- The discriminant function of the Weierstrass family is analytic at `0` (it equals
`(-1)^k · weierstrassResFun`). -/
lemma weierstrassDiscFn_analyticAt {m : ℕ} (hm : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (weierstrassDiscFn m a) 0 := by
  have hfun : weierstrassDiscFn m a
      = fun w => (-1 : ℂ) ^ (m * (m - 1) / 2) * weierstrassResFun m a w := by
    funext w
    have := weierstrassResFun_eq_discFn m a hm w
    -- `weierstrassResFun w = (-1)^k * weierstrassDiscFn w` ⟹ `weierstrassDiscFn w = (-1)^k * resFun w`
    have hsq : ((-1 : ℂ) ^ (m * (m - 1) / 2)) * ((-1 : ℂ) ^ (m * (m - 1) / 2)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc weierstrassDiscFn m a w
        = 1 * weierstrassDiscFn m a w := (one_mul _).symm
      _ = ((-1 : ℂ) ^ (m * (m - 1) / 2) * (-1 : ℂ) ^ (m * (m - 1) / 2)) * weierstrassDiscFn m a w := by
            rw [hsq]
      _ = (-1 : ℂ) ^ (m * (m - 1) / 2) * weierstrassResFun m a w := by rw [mul_assoc, ← this]
  rw [hfun]
  exact analyticAt_const.mul (weierstrassResFun_analyticAt a ha_an)

end
