import Cad.Multivariate.ProjectionTheorem.Generalized.ZariskiNonsplitting
import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2General

/-!
# Single-cluster composition (part 1): disc-order ⟹ root structure

Chains the **Zariski axiom** (`zariski_root_sections`) with the proven **F2** root-extraction
(`weierstrass_section_isRoot`, `weierstrass_section_rootMultiplicity`): from the hypothesis that the
discriminant has constant vanishing order along the section (the output of
`DiscOrder.weierstrassDisc_order_const_along_section`), produce the holomorphic root sections `ψᵢ`
together with the full root/multiplicity structure of the section polynomial.

This is the "back half" of the single-cluster chain `descent → DiscOrder → Zariski → F2 → F1`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **Cluster root structure (single branch, Theorem 4.1.1).** From `disc(h) ≢ 0` and constant
discriminant order along the section, the section Weierstrass polynomial has a single holomorphic
root section `ψ` (the unique root, nonsplitting) of multiplicity `m`, AND (conclusion (2)) the
Weierstrass polynomial `h` is order-invariant in its graph `{((y,0), ψ y)}`. Wraps both
`zariski_single_branch` (conclusion (1)) and `zariski_order_invariant_in_graph` (conclusion (2)). -/
theorem cluster_root_structure {s e : ℕ} (m : ℕ) (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∃ ψ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
        (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ y) = m) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2) ((y, 0), ψ y)
          = order ℂ (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
              ((0, 0), ψ 0)) := by
  obtain ⟨ψ, hψ_an, hψ0, hroots, hmults⟩ := zariski_single_branch m hm a ha_an ha0 hdisc_ne hdisc
  exact ⟨ψ, hψ_an, hψ0, hroots, hmults,
    Puiseux.order_invariant_in_graph m hm a ha_an ha0 hdisc_ne hdisc ψ hψ_an hroots⟩

end
