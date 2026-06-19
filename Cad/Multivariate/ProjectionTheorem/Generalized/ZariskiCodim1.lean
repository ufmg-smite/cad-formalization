import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs

/-!
# Codimension-1 nonsplitting — the assembly layer

This file is the first concrete step toward discharging the pure-nonsplitting axiom
`zariski_nonsplitting` (the Chapter-4 monodromy kernel of Zariski's Theorem 4.1.1). It supplies the
**algebraic assembly** that the analytic proof of nonsplitting reduces to, with no new axioms.

The thesis proof of nonsplitting (Theorem 4.2.2, the codimension-1 case) runs:

1. **(A2)** factor the Weierstrass polynomial into *irreducible* Weierstrass polynomials
   `h = h₁ ⋯ h_k` over the ring of holomorphic germs;
2. **(A1+A3+A4)** each irreducible factor `hⱼ` has a *single* root over the section `T*`
   (the branched-covering + transitive-monodromy + homotopy-deformation argument — the genuine
   analytic kernel, leveraging Mathlib's covering-space lifting machinery);
3. **(A5)** distinct factors share that root over `T*` (a resultant / zero-system-continuity
   argument), so all the per-factor roots *coincide*;
4. **assembly** the section polynomial therefore has a single root.

Steps 1–3 produce, for `y` near `0`, a factorization of the section polynomial into finitely many
factors **all sharing one common single root** `α`. This file proves step 4 — the assembly —
exactly: `nonsplitting_of_common_single_root` turns that factorization datum into the nonsplitting
conclusion. Discharging `zariski_nonsplitting` then reduces to *producing* the factorization datum
(`hfac` below), which is the covering/monodromy infrastructure scoped as the next sub-project.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **Assembly across a factorization.** If a polynomial is a product of `k ≥ 1` factors that all
share the *same* single distinct root `α`, then it too has `α` as its single distinct root. (Roots of
a product are the union of the roots of the factors; here every factor's root set is `{α}`.) -/
lemma single_root_of_prod {k : ℕ} (q : Fin k → Polynomial ℂ) (α : ℂ) (hk : 0 < k)
    (hq_root : ∀ j β, (q j).IsRoot β ↔ β = α)
    (p : Polynomial ℂ) (hp : p = ∏ j : Fin k, q j) :
    ∀ β, p.IsRoot β ↔ β = α := by
  intro β
  rw [hp, Polynomial.IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩; exact (hq_root j β).mp hj
  · intro hβ; exact ⟨⟨0, hk⟩, Finset.mem_univ _, (hq_root ⟨0, hk⟩ β).mpr hβ⟩

/-- **Codimension-1 nonsplitting, reduced to the factorization datum.** Given (for `y` near `0`) a
factorization of the section Weierstrass polynomial into finitely many factors that all share one
common single root `α(y)` — the output of the irreducible factorization (A2) + per-factor single root
(A1·A3·A4) + cross-factor coincidence (A5) — the section polynomial has a single distinct root. This
is exactly the conclusion shape of `zariski_nonsplitting`; only the analytic hypothesis `hfac`
remains to be supplied (the covering/monodromy infrastructure). -/
theorem nonsplitting_of_common_single_root {s e : ℕ} (m : ℕ)
    (a : Fin m → (CParam s e → ℂ))
    (hfac : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∃ (k : ℕ) (q : Fin k → Polynomial ℂ) (α : ℂ),
      0 < k ∧ weierstrassPoly m a ((y, 0) : CParam s e) = ∏ j : Fin k, q j ∧
        (∀ j β, (q j).IsRoot β ↔ β = α)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot β ↔ β = α := by
  filter_upwards [hfac] with y hy
  obtain ⟨k, q, α, hk, hfac_y, hq_root⟩ := hy
  exact ⟨α, single_root_of_prod q α hk hq_root _ hfac_y⟩

end
