import Cad.Multivariate.ProjectionTheorem.Generalized.SingleCluster
import Cad.Multivariate.ProjectionTheorem.Generalized.MembershipDescent
import Cad.Multivariate.ProjectionTheorem.Generalized.DescentNormIdentity
import Cad.Multivariate.ProjectionTheorem.Generalized.FactorDifferentiate

/-!
# Cluster assembly (A3 friction #3 — plumbing)

`single_cluster_from_weierstrass` wires the whole complex single-cluster chain starting from the
**C-axiom output** (the Weierstrass factorization `polyToFun g =ᶠ u · polyToFun h`) and the
**complexified elimination membership** (`C Pℂ = A·g + B·g'` with analytic cofactors):

  `factor_deriv` (the `t`-derivative factorization `hfac'`)
  → `descent_membership` (germ Bézout → polynomial cofactors over `weierstrassPolyFun`)
  → `descent_norm_identity` (norm identity `Pℂ^m =ᶠ weierstrassResFun · Q`)
  → `single_cluster_complex` (holomorphic root sections + multiplicity structure).

This is the assembly that A3's localization front-end (producing `u`, `a`, the factorization, the
membership, and the section order `hP_oi`) feeds into, per cluster.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **Single cluster from the Weierstrass factorization.** Given the C-axiom factorization of the
section family and the complexified elimination membership (with constant witness section-order),
produce the holomorphic root sections of the section Weierstrass polynomial. -/
theorem single_cluster_from_weierstrass (m : ℕ) (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (g_poly : (CParam s e → ℂ)[X])
    (u : CParam s e × ℂ → ℂ) (hu : AnalyticAt ℂ u 0)
    (hfac : polyToFun s e g_poly =ᶠ[𝓝 0]
      fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt)
    (P : CParam s e → ℂ) (hP_an : AnalyticAt ℂ P 0) (hP_ne : order ℂ P 0 ≠ ⊤)
    (A B : (CParam s e → ℂ)[X]) (hA : AnalyticCoeffs A) (hB : AnalyticCoeffs B)
    (hmem_g : polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0] fun zt =>
        polyToFun s e A zt * polyToFun s e g_poly zt
      + polyToFun s e B zt * polyToFun s e (derivative g_poly) zt)
    (hP_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ P ((y, 0) : CParam s e) = order ℂ P ((0, 0) : CParam s e)) :
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
  -- the t-derivative factorization, with `uder = ptderiv u`
  have huder : AnalyticAt ℂ (ptderiv u) 0 := analyticAt_ptderiv u hu
  have hfac' := factor_deriv m a g_poly u hu hfac
  -- germ Bézout → polynomial cofactors over the Weierstrass polynomial
  obtain ⟨A', B', hA', hB', hmem⟩ :=
    descent_membership hm a ha_an ha0 P hP_an g_poly A B hA hB hmem_g u (ptderiv u) hu huder hfac hfac'
  -- norm identity `P^m =ᶠ weierstrassResFun · Q`
  obtain ⟨Q, hQ_an, hnorm⟩ :=
    descent_norm_identity hm a ha_an P hP_an A' B' hA' hB' hmem
  -- single-cluster pipeline
  exact single_cluster_complex m hm a ha_an ha0 P Q hP_an hQ_an hP_ne hnorm hP_oi

end
