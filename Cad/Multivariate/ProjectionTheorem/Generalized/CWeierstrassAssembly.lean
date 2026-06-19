import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs

/-!
# Assembling `weierstrass_division` from its Cauchy-integral ingredients (WIP)

This file is the **assembly spine** of the Cauchy-integral proof of the convergent Weierstrass
division axiom (`weierstrass_division`). The classical proof factors as three layers; this file
proves each layer *taking the deeper layer's output as an explicit hypothesis*, so the whole chain is
sorry-free modulo exactly the two genuinely-missing classical inputs (the several-variable
holomorphy⇒analyticity bridge `CBridge.osgood`, and the argument principle). It is **standalone**
(not imported by `Cad.Multivariate.ProjectionTheorem.lean`) so the main library keeps resting on the single clean axiom.

```
weierstrass_division  (division by a general t-regular germ G)
   ⟸  Layer A (this file, pure germ algebra — NO analysis)
        { preparation:  G = u · W   (u analytic unit, W Weierstrass polynomial)
        , division by W:  F = Q·W + r   (existence + uniqueness) }
   ⟸  Layer B (Cauchy reproducing formula + difference-quotient brick `eval_sub_eval_eq_mul`)
        provides division by W  [needs keystone; NO argument principle]
   ⟸  Layer C (argument principle: power sums + root count; Newton's identities)
        provides preparation     [needs keystone + argument principle]
```

**Layer A — done below, sorry-free.** Division by a general `G` reduces to {preparation, division
by `W`} by *pure analytic-germ algebra*: write `G = u·W` with `u` a unit (`u 0 ≠ 0`, so `u⁻¹` is
analytic), divide `F` by `W` to get `F = Q·W + r`, and set `q = Q·u⁻¹`; then `q·G = Q·u⁻¹·u·W = Q·W`,
so `F = q·G + r`. Uniqueness transports the same way (`q·G = (q·u)·W`). The remainder `r` (a degree
`< m` polynomial in `t` with analytic coefficients) is *unchanged* — preparation only moves the
analytic unit between the two sides.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

variable {s e : ℕ}

/-- **Layer A: division by a general `t`-regular germ reduces to {preparation, division by `W`}.**

Given
* a Weierstrass polynomial `W = weierstrassPoly m a` (`a i 0 = 0`, coefficients analytic) and an
  analytic **unit** `u` (`u 0 ≠ 0`) with `G = u·W` near `0` (the **preparation** input), and
* **division by `W`** as both an existence and a uniqueness statement,

we obtain the full conclusion of `weierstrass_division` for `G` (existence + uniqueness). This is the
top of the assembly tree and uses no analysis beyond analyticity of products and inverses of analytic
germs. -/
theorem weierstrass_division_of_prep_div
    (G : CParam s e × ℂ → ℂ) (m : ℕ)
    (u : CParam s e × ℂ → ℂ) (a : Fin m → (CParam s e → ℂ))
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hGW : G =ᶠ[𝓝 0] fun wt => u wt * (weierstrassPoly m a wt.1).eval wt.2)
    (hdivW_exist : ∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (Q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ Q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => Q wt * (weierstrassPoly m a wt.1).eval wt.2
          + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ))
    (hdivW_uniq : ∀ (Q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ Q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => Q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      Q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0) :
    (∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) ∧
    (∀ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0) := by
  -- the unit is nonzero near `0`
  have hu_ne : ∀ᶠ wt in 𝓝 (0 : CParam s e × ℂ), u wt ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  refine ⟨?_, ?_⟩
  · -- EXISTENCE: divide `F` by `W`, then move the unit to get a division by `G`.
    intro F hF
    obtain ⟨Q, ρ, hQ, hρ, hFeq⟩ := hdivW_exist F hF
    refine ⟨fun wt => Q wt * (u wt)⁻¹, ρ, hQ.mul (hu.inv hu0), hρ, ?_⟩
    filter_upwards [hFeq, hGW, hu_ne] with wt hf hg hne
    rw [hf, hg, mul_assoc (Q wt), inv_mul_cancel_left₀ hne]
  · -- UNIQUENESS: `q·G = (q·u)·W`; apply `W`-uniqueness, then cancel the unit.
    intro q ρ hq hρ hzero
    have hzeroW : (fun wt => (fun wt => q wt * u wt) wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 := by
      filter_upwards [hzero, hGW] with wt hz hg
      rw [mul_assoc, ← hg]; exact hz
    obtain ⟨hQu0, hρ0⟩ := hdivW_uniq (fun wt => q wt * u wt) ρ (hq.mul hu) hρ hzeroW
    refine ⟨?_, hρ0⟩
    filter_upwards [hQu0, hu_ne] with wt h hne
    exact (mul_eq_zero.mp h).resolve_right hne

end
