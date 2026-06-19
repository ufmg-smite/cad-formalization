import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs
import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassSynthesis

/-!
# The classical analytic ingredients: convergent Weierstrass division (PROVED) & Zariski sections

* `weierstrass_division` — convergent Weierstrass division. **No longer an axiom:** it is now a
  `theorem`, discharged by `weierstrass_division_proved` (the full Cauchy-integral proof in Layer
  C/B/A, depending only on `propext, Classical.choice, Quot.sound`).
* `zariski_single_branch` — Zariski's Theorem 4.1.1 (a single holomorphic root section under
  `disc ≢ 0` and constant discriminant order along the section). This remains an axiom.

The basic definitions (`CParam`, `weierstrassPoly`, `weierstrassDiscFn`, and their monic/degree/order
properties) live in the axiom-free base `Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs`, so the proof chain
discharging `weierstrass_division` can be imported here without a cycle.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

/-- **Convergent Weierstrass division (Phase C) — now a theorem.** Discharged by
`weierstrass_division_proved` (several-variable holomorphy⇒analyticity bridge, the argument principle,
Newton's identities, and the `G = u·W` synthesis). -/
theorem weierstrass_division {s e : ℕ}
    (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    (∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) ∧
    (∀ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0) :=
  weierstrass_division_proved G hG m hreg

/-- **Weierstrass division by a Weierstrass polynomial** — the special case `G = h`. -/
theorem weierstrass_division_analytic {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (F : CParam s e × ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
      F =ᶠ[𝓝 0] fun wt => q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ) :=
  (weierstrass_division (fun wt => (weierstrassPoly m a wt.1).eval wt.2)
    (weierstrassPolyEval_analyticAt m a ha_an) m (weierstrassPolyEval_order m a ha0)).1 F hF

/-- **Uniqueness of Weierstrass division by a Weierstrass polynomial** — the `G = h` case. -/
theorem weierstrass_division_unique {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ))
    (hq : AnalyticAt ℂ q 0) (hρ : ∀ i, AnalyticAt ℂ (ρ i) 0)
    (hzero : (fun wt => q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0) :
    q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0 :=
  (weierstrass_division (fun wt => (weierstrassPoly m a wt.1).eval wt.2)
    (weierstrassPolyEval_analyticAt m a ha_an) m (weierstrassPolyEval_order m a ha0)).2 q ρ hq hρ hzero

/-! **Zariski 4.1.1, conclusion (2) — order-invariance in the graph — NO LONGER AN AXIOM.**

The former axiom `zariski_order_invariant_in_graph` is now the theorem `Puiseux.order_invariant_in_graph`
(`Mccalum/Puiseux/Conclusion2General.lean`), and `cluster_root_structure` (`ClusterRootStructure.lean`)
calls it directly. The full general-`e` order-invariance is proved (factorization + Lemma 4.2.8 +
e=0/e=1 dispatch) modulo the single residual `Puiseux.order_eval_value_e2_blowup` (the `e ≥ 2` quadratic
blow-up to codimension one). It cannot live in this file because the Puiseux proof chain transitively
imports it; see the discharge in the `Puiseux` namespace. -/

end
