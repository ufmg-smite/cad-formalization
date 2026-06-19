import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDivision

/-!
# Phase D1 descent — the membership descent (Step 3a)

Assembles the proven pieces into the **membership descent**: from a *germ-level* membership
`polyToFun (C P) =ᶠ Γ·H + Δ·H'` (with `Γ,Δ` analytic — the `u`-transfer output, Step 2), produce
**polynomial cofactors** `A,B` (analytic coefficients) with `polyToFun (C P) =ᶠ polyToFun (A·h + B·h')`.

Method: Weierstrass-divide `Γ,Δ` by `h` (existence axiom) into analytic quotients `qΓ,qΔ` and
degree-`<m` polynomial remainders `rΓ,rΔ`; collect `k := qΓ·H + qΔ·H'`; the algebra gives
`k·H =ᶠ polyToFun P₀` with `P₀ := C P − rΓ·h − rΔ·h'`; the **core descent step**
(`analytic_mul_weierstrass_eq_poly_of_coeffs`) turns `k` into the polynomial `polyToFun (P₀/ₘh)`;
then `A := P₀/ₘh + rΓ`, `B := rΔ`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

@[simp] lemma polyToFun_C (c : CParam s e → ℂ) :
    polyToFun s e (Polynomial.C c) = fun zt => c zt.1 := by
  funext zt; rw [polyToFun_apply]; simp

@[simp] lemma polyToFun_X : polyToFun s e (X : (CParam s e → ℂ)[X]) = fun zt => zt.2 := by
  funext zt; rw [polyToFun_apply]; simp

/-- The degree-`<m` remainder polynomial `∑_{i<m} C(ρᵢ)·Xⁱ`. -/
def remPolyFun {m : ℕ} (ρ : Fin m → (CParam s e → ℂ)) : (CParam s e → ℂ)[X] :=
  ∑ i : Fin m, Polynomial.C (ρ i) * X ^ (i : ℕ)

lemma polyToFun_remPolyFun {m : ℕ} (ρ : Fin m → (CParam s e → ℂ)) :
    polyToFun s e (remPolyFun ρ) = fun zt => ∑ i : Fin m, ρ i zt.1 * zt.2 ^ (i : ℕ) := by
  rw [remPolyFun, map_sum]
  funext zt
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [map_mul, map_pow, polyToFun_C, polyToFun_X, Pi.mul_apply, Pi.pow_apply]


/-- The coefficients of the remainder polynomial are analytic at `0`. -/
lemma remPolyFun_coeff_analyticAt {m : ℕ} (ρ : Fin m → (CParam s e → ℂ))
    (hρ : ∀ i, AnalyticAt ℂ (ρ i) 0) (k : ℕ) :
    AnalyticAt ℂ ((remPolyFun ρ).coeff k) 0 := by
  set S := AnalyticAtSubring s e
  let pS : S[X] := ∑ i : Fin m, Polynomial.C (⟨ρ i, hρ i⟩ : S) * X ^ (i : ℕ)
  have hmap : pS.map S.subtype = remPolyFun ρ := by
    simp only [pS, remPolyFun, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    rfl
  have hc : (remPolyFun ρ).coeff k = ↑(pS.coeff k) := by rw [← hmap, Polynomial.coeff_map]; rfl
  rw [hc]; exact (pS.coeff k).2

/-- A polynomial over `CParam s e → ℂ` with analytic-at-`0` coefficients (the analytic-coeff
predicate is closed under the ring operations — see `analyticCoeffs_*` below). -/
def AnalyticCoeffs (p : (CParam s e → ℂ)[X]) : Prop := ∀ i, AnalyticAt ℂ (p.coeff i) 0

lemma analyticCoeffs_add {p q : (CParam s e → ℂ)[X]}
    (hp : AnalyticCoeffs p) (hq : AnalyticCoeffs q) : AnalyticCoeffs (p + q) :=
  fun i => by rw [Polynomial.coeff_add]; exact (hp i).add (hq i)

lemma analyticCoeffs_sub {p q : (CParam s e → ℂ)[X]}
    (hp : AnalyticCoeffs p) (hq : AnalyticCoeffs q) : AnalyticCoeffs (p - q) :=
  fun i => by rw [Polynomial.coeff_sub]; exact (hp i).sub (hq i)

lemma analyticCoeffs_mul {p q : (CParam s e → ℂ)[X]}
    (hp : AnalyticCoeffs p) (hq : AnalyticCoeffs q) : AnalyticCoeffs (p * q) := by
  intro i
  rw [Polynomial.coeff_mul]
  have : (∑ x ∈ Finset.antidiagonal i, p.coeff x.1 * q.coeff x.2)
      = fun w => ∑ x ∈ Finset.antidiagonal i, p.coeff x.1 w * q.coeff x.2 w := by
    funext w; rw [Finset.sum_apply]; rfl
  rw [this]
  exact Finset.analyticAt_fun_sum _ (fun x _ => (hp x.1).mul (hq x.2))

lemma analyticCoeffs_C {c : CParam s e → ℂ} (hc : AnalyticAt ℂ c 0) :
    AnalyticCoeffs (Polynomial.C c) := by
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · simpa using hc
  · rw [Polynomial.coeff_C, if_neg hi]; exact analyticAt_const

lemma analyticCoeffs_weierstrassPolyFun {m : ℕ} (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) : AnalyticCoeffs (weierstrassPolyFun m a) :=
  weierstrassPolyFun_coeff_analyticAt a ha_an

lemma analyticCoeffs_derivative {p : (CParam s e → ℂ)[X]} (hp : AnalyticCoeffs p) :
    AnalyticCoeffs (derivative p) := by
  intro i
  rw [Polynomial.coeff_derivative,
    show ((i : CParam s e → ℂ) + 1) = fun _ => ((i : ℂ) + 1) from by funext _; simp]
  exact (hp (i + 1)).mul analyticAt_const

lemma analyticCoeffs_remPolyFun {m : ℕ} (ρ : Fin m → (CParam s e → ℂ))
    (hρ : ∀ i, AnalyticAt ℂ (ρ i) 0) : AnalyticCoeffs (remPolyFun ρ) :=
  remPolyFun_coeff_analyticAt ρ hρ

lemma analyticCoeffs_divByMonic {p h : (CParam s e → ℂ)[X]}
    (hp : AnalyticCoeffs p) (hh : AnalyticCoeffs h) (hmonic : h.Monic) :
    AnalyticCoeffs (p /ₘ h) :=
  fun i => (coeff_divByMonic_analyticAt p h hp hh hmonic i).1

/-- **Membership descent (Step 3a).** From a germ-level membership `polyToFun (C P) =ᶠ Γ·H + Δ·H'`
(`Γ,Δ` analytic), produce polynomial cofactors `A,B` (analytic coefficients) with
`polyToFun (C P) =ᶠ polyToFun (A·h + B·h')`. -/
theorem membership_descent {m : ℕ} (hm : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (P : CParam s e → ℂ) (hP_an : AnalyticAt ℂ P 0)
    (Γ Δ : CParam s e × ℂ → ℂ) (hΓ : AnalyticAt ℂ Γ 0) (hΔ : AnalyticAt ℂ Δ 0)
    (hmem : polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0] fun zt =>
        Γ zt * polyToFun s e (weierstrassPolyFun m a) zt
      + Δ zt * polyToFun s e (derivative (weierstrassPolyFun m a)) zt) :
    ∃ (A B : (CParam s e → ℂ)[X]),
      AnalyticCoeffs A ∧ AnalyticCoeffs B ∧
      polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0]
        polyToFun s e (A * weierstrassPolyFun m a + B * derivative (weierstrassPolyFun m a)) := by
  have hmonic : (weierstrassPolyFun m a).Monic := weierstrassPolyFun_monic m a
  have hh_an : AnalyticCoeffs (weierstrassPolyFun m a) := analyticCoeffs_weierstrassPolyFun a ha_an
  have hh'_an : AnalyticCoeffs (derivative (weierstrassPolyFun m a)) := analyticCoeffs_derivative hh_an
  set H := polyToFun s e (weierstrassPolyFun m a) with hH
  set H' := polyToFun s e (derivative (weierstrassPolyFun m a)) with hH'
  have hHan : AnalyticAt ℂ H 0 := polyToFun_analyticAt _ hh_an
  have hH'an : AnalyticAt ℂ H' 0 := polyToFun_analyticAt _ hh'_an
  obtain ⟨qΓ, ρΓ, hqΓ, hρΓ, hdivΓ⟩ := weierstrass_division_analytic m a ha_an ha0 Γ hΓ
  obtain ⟨qΔ, ρΔ, hqΔ, hρΔ, hdivΔ⟩ := weierstrass_division_analytic m a ha_an ha0 Δ hΔ
  -- Divisions in `polyToFun` form: `Γ =ᶠ qΓ·H + polyToFun rΓ`, etc.
  have hΓ_eq : Γ =ᶠ[𝓝 0] fun zt => qΓ zt * H zt + polyToFun s e (remPolyFun ρΓ) zt := by
    filter_upwards [hdivΓ] with zt hzt
    rw [hzt, polyToFun_remPolyFun, hH, polyToFun_weierstrassPolyFun]
  have hΔ_eq : Δ =ᶠ[𝓝 0] fun zt => qΔ zt * H zt + polyToFun s e (remPolyFun ρΔ) zt := by
    filter_upwards [hdivΔ] with zt hzt
    rw [hzt, polyToFun_remPolyFun, hH, polyToFun_weierstrassPolyFun]
  -- collected quotient germ and the polynomial `P₀`
  set k : CParam s e × ℂ → ℂ := fun zt => qΓ zt * H zt + qΔ zt * H' zt with hk_def
  have hk_an : AnalyticAt ℂ k 0 := (hqΓ.mul hHan).add (hqΔ.mul hH'an)
  set P0 : (CParam s e → ℂ)[X] :=
    Polynomial.C P - remPolyFun ρΓ * weierstrassPolyFun m a - remPolyFun ρΔ * derivative (weierstrassPolyFun m a)
    with hP0
  have hP0_coeff : AnalyticCoeffs P0 := by
    rw [hP0]
    exact analyticCoeffs_sub (analyticCoeffs_sub (analyticCoeffs_C hP_an)
      (analyticCoeffs_mul (analyticCoeffs_remPolyFun ρΓ hρΓ) hh_an))
      (analyticCoeffs_mul (analyticCoeffs_remPolyFun ρΔ hρΔ) hh'_an)
  -- `polyToFun P₀ = polyToFun (C P) − polyToFun rΓ · H − polyToFun rΔ · H'`
  have hP0exp : polyToFun s e P0 = fun zt => polyToFun s e (Polynomial.C P) zt
      - polyToFun s e (remPolyFun ρΓ) zt * H zt - polyToFun s e (remPolyFun ρΔ) zt * H' zt := by
    rw [hP0, map_sub, map_sub, map_mul, map_mul]; rfl
  -- `k · H =ᶠ polyToFun P₀`
  have hkH : (fun zt => k zt * H zt) =ᶠ[𝓝 0] polyToFun s e P0 := by
    filter_upwards [hmem, hΓ_eq, hΔ_eq] with zt hmz hΓz hΔz
    rw [hP0exp]
    simp only [hk_def]
    have hmz' : polyToFun s e (Polynomial.C P) zt = Γ zt * H zt + Δ zt * H' zt := hmz
    rw [hmz', hΓz, hΔz]; ring
  -- core descent: `k =ᶠ polyToFun (P₀ /ₘ h)`
  have hcore : k =ᶠ[𝓝 0] polyToFun s e (P0 /ₘ weierstrassPolyFun m a) :=
    analytic_mul_weierstrass_eq_poly_of_coeffs hm a ha_an ha0 k hk_an P0 hP0_coeff hkH
  -- assemble `A := P₀/ₘh + rΓ`, `B := rΔ`
  refine ⟨P0 /ₘ weierstrassPolyFun m a + remPolyFun ρΓ, remPolyFun ρΔ,
    analyticCoeffs_add (analyticCoeffs_divByMonic hP0_coeff hh_an hmonic)
      (analyticCoeffs_remPolyFun ρΓ hρΓ), analyticCoeffs_remPolyFun ρΔ hρΔ, ?_⟩
  have hRHS : polyToFun s e ((P0 /ₘ weierstrassPolyFun m a + remPolyFun ρΓ) * weierstrassPolyFun m a
        + remPolyFun ρΔ * derivative (weierstrassPolyFun m a))
      = fun zt => polyToFun s e (P0 /ₘ weierstrassPolyFun m a) zt * H zt
        + polyToFun s e (remPolyFun ρΓ) zt * H zt + polyToFun s e (remPolyFun ρΔ) zt * H' zt := by
    rw [map_add, map_mul, map_add, map_mul]
    funext zt; simp only [Pi.add_apply, Pi.mul_apply]; ring
  rw [hRHS]
  filter_upwards [hcore, hkH] with zt hcz hkz
  have hkz' : k zt * H zt = polyToFun s e P0 zt := hkz
  have hP0z := congrFun hP0exp zt
  rw [← hcz, hkz', hP0z]; ring

/-- **`u`-transfer (Step 2).** From the analytic-cofactor membership `C P = A·g + B·g'` and the
**differentiated Weierstrass factorization** `polyToFun g =ᶠ u·H`,
`polyToFun g' =ᶠ uder·H + u·H'` (with `u, uder` analytic — the prep axiom + Leibniz in `t`), produce
the germ membership `polyToFun (C P) =ᶠ Γ·H + Δ·H'` feeding `membership_descent`:
`Γ := polyToFun A · u + polyToFun B · uder`, `Δ := polyToFun B · u`. -/
theorem u_transfer {m : ℕ} (a : Fin m → (CParam s e → ℂ))
    (P : CParam s e → ℂ) (g A B : (CParam s e → ℂ)[X])
    (hA : AnalyticCoeffs A) (hB : AnalyticCoeffs B)
    (hmem_g : polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0] fun zt =>
        polyToFun s e A zt * polyToFun s e g zt
      + polyToFun s e B zt * polyToFun s e (derivative g) zt)
    (u uder : CParam s e × ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (huder : AnalyticAt ℂ uder 0)
    (hfac : polyToFun s e g =ᶠ[𝓝 0]
        fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt)
    (hfac' : polyToFun s e (derivative g) =ᶠ[𝓝 0] fun zt =>
        uder zt * polyToFun s e (weierstrassPolyFun m a) zt
      + u zt * polyToFun s e (derivative (weierstrassPolyFun m a)) zt) :
    ∃ Γ Δ : CParam s e × ℂ → ℂ, AnalyticAt ℂ Γ 0 ∧ AnalyticAt ℂ Δ 0 ∧
      polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0] fun zt =>
        Γ zt * polyToFun s e (weierstrassPolyFun m a) zt
      + Δ zt * polyToFun s e (derivative (weierstrassPolyFun m a)) zt := by
  refine ⟨fun zt => polyToFun s e A zt * u zt + polyToFun s e B zt * uder zt,
          fun zt => polyToFun s e B zt * u zt,
          ((polyToFun_analyticAt A hA).mul hu).add ((polyToFun_analyticAt B hB).mul huder),
          (polyToFun_analyticAt B hB).mul hu, ?_⟩
  filter_upwards [hmem_g, hfac, hfac'] with zt hcpz hf hf'
  rw [hcpz, hf, hf']
  ring

/-- **Descent (Steps 2 + 3a combined).** From the analytic-cofactor membership of `g` and the
differentiated Weierstrass factorization, produce polynomial cofactors `A',B'` (analytic) with
`polyToFun (C P) =ᶠ polyToFun (A'·h + B'·h')` — the full germ-to-`𝒪ₙ[t]` descent (the `=ᶠ` form). -/
theorem descent_membership {m : ℕ} (hm : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (P : CParam s e → ℂ) (hP_an : AnalyticAt ℂ P 0)
    (g A B : (CParam s e → ℂ)[X]) (hA : AnalyticCoeffs A) (hB : AnalyticCoeffs B)
    (hmem_g : polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0] fun zt =>
        polyToFun s e A zt * polyToFun s e g zt
      + polyToFun s e B zt * polyToFun s e (derivative g) zt)
    (u uder : CParam s e × ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (huder : AnalyticAt ℂ uder 0)
    (hfac : polyToFun s e g =ᶠ[𝓝 0]
        fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt)
    (hfac' : polyToFun s e (derivative g) =ᶠ[𝓝 0] fun zt =>
        uder zt * polyToFun s e (weierstrassPolyFun m a) zt
      + u zt * polyToFun s e (derivative (weierstrassPolyFun m a)) zt) :
    ∃ (A' B' : (CParam s e → ℂ)[X]),
      AnalyticCoeffs A' ∧ AnalyticCoeffs B' ∧
      polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0]
        polyToFun s e (A' * weierstrassPolyFun m a + B' * derivative (weierstrassPolyFun m a)) := by
  obtain ⟨Γ, Δ, hΓ, hΔ, hmem⟩ :=
    u_transfer a P g A B hA hB hmem_g u uder hu huder hfac hfac'
  exact membership_descent hm a ha_an ha0 P hP_an Γ Δ hΓ hΔ hmem

end
