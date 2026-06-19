import Cad.Multivariate.ProjectionTheorem.Generalized.BlowupNormalForm
import Cad.Multivariate.ProjectionTheorem.Generalized.BlowupMap
import Cad.Multivariate.ProjectionTheorem.Generalized.CoordTranslate
import Cad.Multivariate.ProjectionTheorem.Generalized.DiscNormalForm
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic

/-!
# M5b (e ≥ 2) — the blow-up reduction to codimension one

The blow-up `Qcp : CParam (s + (k+1)) 1 → CParam s (k+2)` (the thesis Case II quadratic transformation,
re-grouped to match the codimension-one domain of `zariski_nonsplitting`) splits the `(s+k+1)`-section
coordinate `Y` into the original section `y` (first `s`) and the ratio coordinates `v` (last `k+1`),
and applies `BlowupMap.Q`. Through `Φ' := cparamEquiv (s+(k+1))` (which puts the distinguished
coordinate `u` at flat coordinate `0`), the `u`-slice of `Qcp` is a straight transverse line — the
geometric input to `BlowupNormalForm.iteratedDeriv_line_eq`.
-/

noncomputable section

open Filter BlowupNormalForm BlowupMap CoordTranslate DiscNormalForm
open scoped Topology

namespace ZariskiE2

variable {s k : ℕ}

/-- The codimension-one blow-up domain coordinate map: split `Y : Fin (s+(k+1)) → ℂ` into the section
`y` (first `s`) and ratios `v` (last `k+1`), then apply `Q`. -/
def Qcp (W : CParam (s + (k + 1)) 1) : CParam s (k + 2) :=
  Q (W.1 ∘ Fin.castAdd (k + 1), W.1 ∘ Fin.natAdd s, W.2 0)

/-- The flat blow-up `B = Qcp ∘ Φ'.symm` on `Fin (s+k+2) → ℂ` coordinates (`u` at coordinate `0`). -/
def B (Z : Fin (s + (k + 1) + 1) → ℂ) : CParam s (k + 2) :=
  Qcp ((cparamEquiv (s + (k + 1))).symm Z)

lemma Qcp_zero : Qcp (0 : CParam (s + (k + 1)) 1) = 0 := by
  rw [Qcp]
  convert Q_zero using 2

lemma B_zero : B (0 : Fin (s + (k + 1) + 1) → ℂ) = 0 := by
  rw [B, map_zero, Qcp_zero]

/-- **The flat blow-up line identity.** For `Z` with `Z 0 = 0`, the `u`-slice of `B` is the transverse
line `(yZ, 0) + t • ξZ`, where `yZ = (Fin.tail Z) ∘ Fin.castAdd (k+1)` and
`ξZ = (0, Fin.snoc ((Fin.tail Z) ∘ Fin.natAdd s) 1)`. -/
lemma B_line (Z : Fin (s + (k + 1) + 1) → ℂ) (hZ : Z 0 = 0) (t : ℂ) :
    B (Z + t • e0 (s + (k + 1))) =
      (((Fin.tail Z ∘ Fin.castAdd (k + 1), 0) : CParam s (k + 2))
        + t • ((0, (Fin.snoc (Fin.tail Z ∘ Fin.natAdd s) 1 : Fin (k + 2) → ℂ))
            : CParam s (k + 2))) := by
  have htail : Fin.tail (Z + t • e0 (s + (k + 1))) = Fin.tail Z := by
    funext i
    simp only [Fin.tail, Pi.add_apply, Pi.smul_apply, e0]
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero, add_zero]
  have hu : (Z + t • e0 (s + (k + 1))) 0 = t := by
    simp only [Pi.add_apply, Pi.smul_apply, e0, Pi.single_eq_same, smul_eq_mul, mul_one, hZ, zero_add]
  rw [B, cparamEquiv_symm_apply, Qcp]
  simp only [htail, hu]
  rw [show ((Fin.tail Z ∘ Fin.castAdd (k + 1), Fin.tail Z ∘ Fin.natAdd s, ((fun _ => t) : Fin 1 → ℂ) 0))
      = (Fin.tail Z ∘ Fin.castAdd (k + 1), Fin.tail Z ∘ Fin.natAdd s, t) from rfl]
  exact Q_line _ _ t

/-- The section coordinate extracted from a flat blow-up source point. -/
def yOf (Z : Fin (s + (k + 1) + 1) → ℂ) : Fin s → ℂ := Fin.tail Z ∘ Fin.castAdd (k + 1)

/-- The transverse line direction at a flat blow-up source point. -/
def ξOf (Z : Fin (s + (k + 1) + 1) → ℂ) : CParam s (k + 2) :=
  (0, (Fin.snoc (Fin.tail Z ∘ Fin.natAdd s) 1 : Fin (k + 2) → ℂ))

lemma yOf_continuous : Continuous (yOf (s := s) (k := k)) := by
  unfold yOf Fin.tail; fun_prop

lemma yOf_zero : yOf (0 : Fin (s + (k + 1) + 1) → ℂ) = 0 := by
  funext i; simp [yOf, Fin.tail]

lemma yOf_tendsto : Tendsto (yOf (s := s) (k := k)) (𝓝 0) (𝓝 0) := by
  have := yOf_continuous (s := s) (k := k) |>.tendsto 0
  rwa [yOf_zero] at this

/-- **The jet hypothesis for `div_coord0_pow`.** If `g` is analytic at `0` and at the section points
`(y, 0)` for `y` near `0`, and the order of `g` along the section is `≥ r` (so its `< r` jets vanish
there), then the `< r` coordinate-`0` jets of `g ∘ B` vanish on `{Z 0 = 0}` near `0`. -/
lemma jet_vanish (g : CParam s (k + 2) → ℂ) (r : ℕ)
    (hgB_an : AnalyticAt ℂ (fun Z => g (B Z)) (0 : Fin (s + (k + 1) + 1) → ℂ))
    (hg_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g ((y, 0) : CParam s (k + 2)))
    (hord : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j < r, iteratedFDeriv ℂ j g ((y, 0) : CParam s (k + 2)) = 0) :
    ∀ j, j < r → ∀ᶠ Z in 𝓝 (0 : Fin (s + (k + 1) + 1) → ℂ),
      Z 0 = 0 → (pderiv0)^[j] (fun Z => g (B Z)) Z = 0 := by
  intro j hj
  filter_upwards [pderiv0_iterate_eq_iteratedDeriv hgB_an j,
    yOf_tendsto.eventually hg_at, yOf_tendsto.eventually hord] with Z hbridge hgZ hordZ
  intro hZ0
  rw [hbridge]
  have hfun : (fun t : ℂ => g (B (Z + t • e0 (s + (k + 1)))))
      = fun t : ℂ => g ((yOf Z, (0 : Fin (k + 2) → ℂ)) + t • ξOf Z) := by
    funext t
    rw [B_line Z hZ0 t]; rfl
  rw [hfun, iteratedDeriv_line_eq (ξOf Z) hgZ j, hordZ j hj,
    ContinuousMultilinearMap.zero_apply]

/-- **The blow-up normal form factorization** `g ∘ B = (z 0)ʳ · N`, from `div_coord0_pow`. -/
lemma normalForm (g : CParam s (k + 2) → ℂ) (r : ℕ)
    (hgB_an : AnalyticAt ℂ (fun Z => g (B Z)) (0 : Fin (s + (k + 1) + 1) → ℂ))
    (hg_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g ((y, 0) : CParam s (k + 2)))
    (hord : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j < r, iteratedFDeriv ℂ j g ((y, 0) : CParam s (k + 2)) = 0) :
    ∃ N : (Fin (s + (k + 1) + 1) → ℂ) → ℂ, AnalyticAt ℂ N 0 ∧
      (∀ᶠ Z in 𝓝 0, g (B Z) = (Z 0) ^ r * N Z) :=
  div_coord0_pow r (by simp) hgB_an (jet_vanish g r hgB_an hg_at hord)

/-- **The discriminant order is constant `= r` on the section**, from the normal form with `N(0) ≠ 0`
(the genericity). -/
lemma order_gB (g : CParam s (k + 2) → ℂ) (r : ℕ) (N : (Fin (s + (k + 1) + 1) → ℂ) → ℂ)
    (hN_an : AnalyticAt ℂ N 0)
    (hfact : ∀ᶠ Z in 𝓝 0, g (B Z) = (Z 0) ^ r * N Z) (hN0 : N 0 ≠ 0) :
    ∀ᶠ Z in 𝓝 (0 : Fin (s + (k + 1) + 1) → ℂ),
      Z 0 = 0 → order ℂ (fun Z => g (B Z)) Z = (r : ℕ∞) := by
  filter_upwards [hfact.eventually_nhds, hN_an.eventually_analyticAt,
    hN_an.continuousAt.eventually_ne hN0] with Z hfactZ hNZ hNneZ
  intro hZ0
  have h1 : order ℂ (fun Z => g (B Z)) Z = order ℂ (fun Z => (Z 0) ^ r * N Z) Z :=
    order_congr_of_eventuallyEq' hfactZ
  rw [h1, order_mul_analytic (fun Z => (Z 0) ^ r) N Z ((analyticAt_coord0 Z).pow r) hNZ,
    order_pow_analytic (fun Z => Z 0) Z (analyticAt_coord0 Z) r, order_coord0_eq_one hZ0,
    order_eq_zero_of_ne N Z hNneZ, mul_one, add_zero]

/-! ### Genericity: the mixed diagonal reduces to the pure-transverse diagonal -/

/-- **Mixed-diagonal reduction.** Under section order-invariance, the `r`-th derivative of `g` along the
line `t ↦ (t·wₛ, t·wₜ)` equals that along the pure-transverse line `t ↦ (0, t·wₜ)`. Both equal
`r!·Ξ(0)` where `Ξ` is the strict transform of the `2`-variable slice `Φ(z) = g(z₁·wₛ, z₀·wₜ)`.

The section directions do not contribute to the top derivative because `g` vanishes to order `≥ r` at
every section point (so the `< r` jets of `Φ` in the `z₀`-direction vanish, giving `Φ = z₀ʳ·Ξ`). -/
lemma mixed_diag (g : CParam s (k + 2) → ℂ) (r : ℕ)
    (ws : Fin s → ℂ) (wt : Fin (k + 2) → ℂ)
    (hg0 : AnalyticAt ℂ g 0)
    (hg_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g ((y, 0) : CParam s (k + 2)))
    (hord : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j < r, iteratedFDeriv ℂ j g ((y, 0) : CParam s (k + 2)) = 0) :
    iteratedDeriv r (fun t : ℂ => g (t • ws, t • wt)) 0
      = iteratedDeriv r (fun t : ℂ => g ((0 : Fin s → ℂ), t • wt)) 0 := by
  classical
  -- the 2-variable slice `Φ z = g (z 1 • ws, z 0 • wt)`
  set L : (Fin 2 → ℂ) →L[ℂ] CParam s (k + 2) :=
    ((ContinuousLinearMap.proj 1).smulRight ws).prod ((ContinuousLinearMap.proj 0).smulRight wt)
    with hL
  set Φ : (Fin 2 → ℂ) → ℂ := fun z => g (L z) with hΦ
  have hLapply : ∀ z : Fin 2 → ℂ, L z = (z 1 • ws, z 0 • wt) := fun z => rfl
  have hL0 : L 0 = 0 := map_zero _
  have hΦ_an : AnalyticAt ℂ Φ 0 := hg0.comp_of_eq (L.analyticAt 0) hL0
  -- section map and its limit
  set secOf : (Fin 2 → ℂ) → (Fin s → ℂ) := fun Z => Z 1 • ws with hsec
  have hsec_tendsto : Tendsto secOf (𝓝 0) (𝓝 0) := by
    have hc : Continuous secOf := by unfold secOf; fun_prop
    have h0 : secOf 0 = 0 := by simp [hsec]
    simpa [h0] using hc.tendsto 0
  -- jet hypothesis for `Φ`
  have hjet : ∀ j, j < r → ∀ᶠ Z in 𝓝 (0 : Fin 2 → ℂ), Z 0 = 0 → (pderiv0)^[j] Φ Z = 0 := by
    intro j hj
    filter_upwards [pderiv0_iterate_eq_iteratedDeriv hΦ_an j,
      hsec_tendsto.eventually hg_at, hsec_tendsto.eventually hord] with Z hbridge hgZ hordZ
    intro hZ0
    rw [hbridge]
    have hfun : (fun t : ℂ => Φ (Z + t • e0 1))
        = fun t : ℂ => g ((secOf Z, (0 : Fin (k + 2) → ℂ)) + t • ((0, wt) : CParam s (k + 2))) := by
      funext t
      have h1 : (Z + t • e0 1) 1 = Z 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, e0]
        rw [Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), smul_zero, add_zero]
      have h0 : (Z + t • e0 1) 0 = t := by
        simp only [Pi.add_apply, Pi.smul_apply, e0, Pi.single_eq_same, smul_eq_mul, mul_one, hZ0,
          zero_add]
      show g (L (Z + t • e0 1)) = g ((secOf Z, 0) + t • ((0, wt) : CParam s (k + 2)))
      rw [hLapply, h1, h0]
      congr 1
      simp [hsec]
    rw [hfun, iteratedDeriv_line_eq ((0, wt) : CParam s (k + 2)) hgZ j, hordZ j hj,
      ContinuousMultilinearMap.zero_apply]
  -- divide: `Φ = (z 0)^r · Ξ`
  obtain ⟨Ξ, hΞ_an, hΞeq⟩ := div_coord0_pow r (by simp) hΦ_an hjet
  -- both diagonals equal `r! · Ξ 0`
  have key : ∀ a : ℂ, iteratedDeriv r (fun t : ℂ => g ((t * a) • ws, t • wt)) 0
      = (r.factorial : ℂ) * Ξ 0 := by
    intro a
    -- the curve `γ t = t • ![1, a]` (coord 0 = t, coord 1 = t·a)
    set γ : ℂ → (Fin 2 → ℂ) := fun t => t • (![1, a] : Fin 2 → ℂ) with hγ
    have hγ_an : AnalyticAt ℂ γ 0 := by
      have he : γ = fun t => (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (![1, a] : Fin 2 → ℂ)) t :=
        by funext t; simp [hγ]
      rw [he]
      exact (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (![1, a] : Fin 2 → ℂ)).analyticAt 0
    have hγ0 : γ 0 = 0 := by simp [hγ]
    have hcurve : (fun t : ℂ => g ((t * a) • ws, t • wt))
        =ᶠ[𝓝 0] fun t : ℂ => t ^ r * Ξ (γ t) := by
      have htend : Tendsto γ (𝓝 0) (𝓝 0) := by simpa [hγ0] using hγ_an.continuousAt.tendsto
      filter_upwards [htend.eventually hΞeq] with t ht
      have hΦγ : Φ (γ t) = g ((t * a) • ws, t • wt) := by
        show g (L (γ t)) = g ((t * a) • ws, t • wt)
        rw [hLapply]
        congr 1 ; · simp [hγ, mul_comm]
      have h0 : (γ t) 0 = t := by simp [hγ]
      rw [← hΦγ, ht, h0]
    rw [hcurve.iteratedDeriv_eq,
      BlowupNormalForm.iteratedDeriv_pow_mul (φ := fun t => Ξ (γ t)) r
        (hΞ_an.comp_of_eq hγ_an hγ0).contDiffAt, hγ0]
  have h1 := key 1
  have h0 := key 0
  simp only [mul_one, mul_zero, zero_smul] at h1 h0
  rw [h1, h0]

/-- **Genericity: a good transverse direction exists.** If `iteratedFDeriv ℂ r g 0 ≠ 0` (i.e. `g` has
order exactly `r`) and `g` is section order-invariant, then some *transverse* direction `(0, ξ)` has
`iteratedFDeriv ℂ r g 0 (·, …, ·) ≠ 0`. (The section directions contribute nothing to the top
derivative; if all transverse diagonals vanished, polarization would force the whole `r`-th derivative
to vanish.) -/
lemma genericity_exists (g : CParam s (k + 2) → ℂ) (r : ℕ)
    (hg0 : AnalyticAt ℂ g 0)
    (hg_at : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), AnalyticAt ℂ g ((y, 0) : CParam s (k + 2)))
    (hord : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j < r, iteratedFDeriv ℂ j g ((y, 0) : CParam s (k + 2)) = 0)
    (hord_ne : iteratedFDeriv ℂ r g (0 : CParam s (k + 2)) ≠ 0) :
    ∃ ξ : Fin (k + 2) → ℂ,
      iteratedFDeriv ℂ r g 0 (fun _ => ((0 : Fin s → ℂ), ξ)) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- all transverse diagonals vanish; deduce all diagonals vanish (mixed-diagonal reduction)
  set F := iteratedFDeriv ℂ r g (0 : CParam s (k + 2)) with hF
  have hdiag : ∀ w : CParam s (k + 2), F (fun _ => w) = 0 := by
    rintro ⟨ws, wt⟩
    have e1 : F (fun _ => (ws, wt)) = iteratedDeriv r (fun t : ℂ => g (t • ws, t • wt)) 0 := by
      rw [hF, ← iteratedDeriv_line_eq ((ws, wt) : CParam s (k + 2)) hg0 r]
      congr 1; funext t; rw [zero_add]; rfl
    have e2 : F (fun _ => ((0 : Fin s → ℂ), wt)) =
        iteratedDeriv r (fun t : ℂ => g ((0 : Fin s → ℂ), t • wt)) 0 := by
      rw [hF, ← iteratedDeriv_line_eq ((0 : Fin s → ℂ), wt) hg0 r]
      congr 1; funext t
      rw [zero_add]; show g (t • ((0 : Fin s → ℂ), wt)) = g ((0 : Fin s → ℂ), t • wt)
      congr 1; simp [Prod.smul_mk]
    rw [e1, mixed_diag g r ws wt hg0 hg_at hord, ← e2]
    exact hcon wt
  -- polarization: zero diagonal ⟹ zero map ⟹ contradiction
  apply hord_ne
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hcomp := ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal F 0 v
  have hfunzero : (fun x : CParam s (k + 2) => F (fun _ => x)) = fun _ => (0 : ℂ) := by
    funext x; exact hdiag x
  rw [hfunzero, iteratedFDeriv_zero_fun, Pi.zero_apply, ContinuousMultilinearMap.zero_apply] at hcomp
  have hsym : ∀ σ : Equiv.Perm (Fin r), F (fun i => v (σ i)) = F v := fun σ =>
    hg0.contDiffAt.iteratedFDeriv_comp_perm v σ
  rw [Finset.sum_congr rfl (fun σ _ => hsym σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin] at hcomp
  have : (r.factorial : ℕ) • F v = 0 := hcomp.symm
  rw [smul_eq_zero] at this
  rcases this with h | h
  · exact absurd h (Nat.factorial_ne_zero r)
  · simpa using h

end ZariskiE2
