import Cad.Multivariate.ProjectionTheorem.Generalized.A5Coincidence

/-!
# A5 — distinct factors share a root over the section (axiom-free)

Extracted from `ZariskiNonsplitting` so that the codimension-one reducible nonsplitting
(`ZariskiNonsplittingE1`) — and hence the M5b blow-up proof — can use it without importing the file
that declares the temporary `e ≥ 2` axiom (which would be circular once the blow-up is wired in).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **(A5) Distinct factors coincide over the section — THEOREM (resultant coincidence).**

Any two factors `facᵢ, facⱼ` of the factorization *share a root* over the section, for `y` near `0`.
Proved (no axiom) by `pair_share_root`. -/
theorem irreducible_factors_section_share_root {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_irr : ∀ j, WeierstrassIrreducible (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j : Fin k, fac j w) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ i j : Fin k, ∃ β : ℂ,
        (fac i ((y, 0) : CParam s e)).IsRoot β ∧ (fac j ((y, 0) : CParam s e)).IsRoot β := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact pair_share_root m a hdisc_ne hdisc k deg fac hfac_fam (fun l => (hfac_irr l).1) hfac_eq i j
