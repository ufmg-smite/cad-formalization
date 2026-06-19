import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Differentiating the Weierstrass factorization in `t` (A3 friction #3 core)

The C axiom yields a factorization `polyToFun g =ᶠ u · polyToFun h` (with `h = weierstrassPolyFun`).
The descent (`descent_membership`) also needs the *`t`-derivative* version
`polyToFun g' =ᶠ uₜ · polyToFun h + u · polyToFun h'` (the product rule, `uₜ = ∂_t u`).

This file builds the partial-`t`-derivative `ptderiv F (z,t) = deriv (τ ↦ F (z,τ)) t`, proves it agrees
with the polynomial derivative through `polyToFun`, respects eventual equality, satisfies the product
rule, and is analytic — assembling the `hfac'` bridge `factor_deriv`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- Partial derivative in the last (`t`) coordinate. -/
def ptderiv (F : CParam s e × ℂ → ℂ) (zt : CParam s e × ℂ) : ℂ :=
  deriv (fun τ => F (zt.1, τ)) zt.2

/-- `ptderiv` through `polyToFun` is the polynomial derivative. -/
lemma ptderiv_polyToFun (p : (CParam s e → ℂ)[X]) (zt : CParam s e × ℂ) :
    ptderiv (polyToFun s e p) zt = polyToFun s e (derivative p) zt := by
  have h1 : (fun τ => polyToFun s e p (zt.1, τ))
      = fun τ => (p.map (Pi.evalRingHom (fun _ => ℂ) zt.1)).eval τ := by
    funext τ; simp [polyToFun_apply]
  have hd := (p.map (Pi.evalRingHom (fun _ => ℂ) zt.1)).hasDerivAt zt.2
  simp only [ptderiv, h1]
  rw [hd.deriv, Polynomial.derivative_map, polyToFun_apply]

/-- `ptderiv` depends only on the germ. -/
lemma ptderiv_congr {F G : CParam s e × ℂ → ℂ}
    (h : F =ᶠ[𝓝 (0 : CParam s e × ℂ)] G) : ptderiv F =ᶠ[𝓝 0] ptderiv G := by
  obtain ⟨U, hUsub, hUopen, hU0⟩ := eventually_nhds_iff.mp h
  show ∀ᶠ zt in 𝓝 (0 : CParam s e × ℂ), ptderiv F zt = ptderiv G zt
  filter_upwards [hUopen.mem_nhds hU0] with zt hzt
  refine Filter.EventuallyEq.deriv_eq ?_
  have hmem : ∀ᶠ τ in 𝓝 zt.2, ((zt.1, τ) : CParam s e × ℂ) ∈ U := by
    have hcont : Continuous (fun τ : ℂ => ((zt.1, τ) : CParam s e × ℂ)) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hzt)
  filter_upwards [hmem] with τ hτ using hUsub _ hτ

/-- The partial `t`-derivative equals the full derivative applied to the `t`-direction. -/
lemma ptderiv_eq_fderiv (u : CParam s e × ℂ → ℂ) (zt : CParam s e × ℂ)
    (hu : DifferentiableAt ℂ u zt) :
    ptderiv u zt = fderiv ℂ u zt ((0, 1) : CParam s e × ℂ) := by
  have hg : HasDerivAt (fun τ : ℂ => ((zt.1, τ) : CParam s e × ℂ)) ((0, 1) : CParam s e × ℂ) zt.2 :=
    (hasDerivAt_const zt.2 zt.1).prodMk (hasDerivAt_id zt.2)
  have hcomp : HasDerivAt (fun τ => u (zt.1, τ)) (fderiv ℂ u zt ((0, 1) : CParam s e × ℂ)) zt.2 := by
    have := (hu.hasFDerivAt.comp_hasDerivAt zt.2 hg)
    simpa using this
  exact hcomp.deriv

/-- `ptderiv` of an analytic function is analytic. -/
lemma analyticAt_ptderiv (u : CParam s e × ℂ → ℂ) (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (ptderiv u) 0 := by
  have hfderiv_an : AnalyticAt ℂ (fun zt => fderiv ℂ u zt ((0, 1) : CParam s e × ℂ)) 0 :=
    (ContinuousLinearMap.apply ℂ ℂ ((0, 1) : CParam s e × ℂ)).analyticAt _ |>.comp hu.fderiv
  refine hfderiv_an.congr ?_
  filter_upwards [hu.eventually_analyticAt] with zt hzt
  exact (ptderiv_eq_fderiv u zt hzt.differentiableAt).symm

/-- **Product rule for `ptderiv`** at points where both factors are differentiable in `t`. -/
lemma ptderiv_mul {u v : CParam s e × ℂ → ℂ} (zt : CParam s e × ℂ)
    (hu : DifferentiableAt ℂ (fun τ => u (zt.1, τ)) zt.2)
    (hv : DifferentiableAt ℂ (fun τ => v (zt.1, τ)) zt.2) :
    ptderiv (fun w => u w * v w) zt = ptderiv u zt * v zt + u zt * ptderiv v zt := by
  simp only [ptderiv]
  exact deriv_mul hu hv

/-- **The `hfac'` bridge.** From the Weierstrass factorization `polyToFun g =ᶠ u · polyToFun h`
(C-axiom output), differentiating in `t` yields the product-rule factorization of `polyToFun g'`
required by `descent_membership`, with `uder = ptderiv u`. -/
lemma factor_deriv (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (g_poly : (CParam s e → ℂ)[X])
    (u : CParam s e × ℂ → ℂ) (hu : AnalyticAt ℂ u 0)
    (hfac : polyToFun s e g_poly =ᶠ[𝓝 0]
      fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt) :
    polyToFun s e (derivative g_poly) =ᶠ[𝓝 0]
      fun zt => ptderiv u zt * polyToFun s e (weierstrassPolyFun m a) zt
        + u zt * polyToFun s e (derivative (weierstrassPolyFun m a)) zt := by
  have h1 : polyToFun s e (derivative g_poly) = ptderiv (polyToFun s e g_poly) := by
    funext zt; rw [ptderiv_polyToFun]
  rw [h1]
  refine (ptderiv_congr hfac).trans ?_
  filter_upwards [hu.eventually_analyticAt] with zt hzt_u
  have hincl : DifferentiableAt ℂ (fun τ : ℂ => ((zt.1, τ) : CParam s e × ℂ)) zt.2 :=
    (differentiableAt_const _).prodMk differentiableAt_id
  have hdu : DifferentiableAt ℂ (fun τ => u (zt.1, τ)) zt.2 :=
    hzt_u.differentiableAt.comp zt.2 hincl
  have hdv : DifferentiableAt ℂ
      (fun τ => polyToFun s e (weierstrassPolyFun m a) (zt.1, τ)) zt.2 := by
    have he : (fun τ => polyToFun s e (weierstrassPolyFun m a) (zt.1, τ))
        = fun τ => ((weierstrassPolyFun m a).map (Pi.evalRingHom (fun _ => ℂ) zt.1)).eval τ := by
      funext τ; simp [polyToFun_apply]
    rw [he]
    exact (Polynomial.differentiable _).differentiableAt
  rw [ptderiv_mul zt hdu hdv, ptderiv_polyToFun]

end
