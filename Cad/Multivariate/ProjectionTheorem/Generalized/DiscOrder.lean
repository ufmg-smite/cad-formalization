import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassEval
import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticGerm

/-!
# Phase D3 application: witness order ⟹ discriminant order constant along the section

This file **wires together** all the proven Phase-D pieces into the single lemma that produces the
hypothesis of the Zariski axiom (`zariski_root_sections`): that the discriminant of the Weierstrass
polynomial has constant vanishing order along the section.

The proof composes:
* the **norm identity with analytic `Q`** (`P^m = weierstrassResFun · Q`) — this is the
  **D1+D2 output**; it is taken here as a hypothesis. The analyticity of `Q` is *essential* and is
  exactly what forces D1 to supply the membership with **analytic Bézout cofactors** (over the germ
  ring `𝒪ₙ`): `norm_identity_elim` builds `Q = norm(AdjoinRoot.mk h b)`, polynomial in the cofactor
  `b`, so `Q` is analytic iff `b` is.
* `order_pow_analytic` (`order(P^m) = m·order P`),
* `order_factor_const_of_mul_analytic` (the preconnected reverse factor bridge along the section),
* `order_weierstrassResFun_eq` (`order(resultant) = order(discriminant)`).

Every hypothesis below is a precise upstream obligation (analyticity of `resultant`/`disc` in the
coefficients — a plumbing lemma; the open/connected domain `U` and section `V` — Phase A; the
norm identity with analytic `Q` — Phase D1+D2). The lemma itself is **sorry-free**.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

/-- **D3 application.** Given the Weierstrass discriminant data analytic on a connected open `U`,
a witness `P` with constant order along the section `{(y,0) : y ∈ V}`, and the norm identity
`P^m = weierstrassResFun · Q` with an **analytic** `Q`, the discriminant `weierstrassDiscFn` has
constant order along the section. This is precisely the `hdisc` hypothesis of `zariski_root_sections`. -/
theorem weierstrassDisc_order_const_along_section
    {s e : ℕ} (m : ℕ) (hm : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (P Q : CParam s e → ℂ)
    {U : Set (CParam s e)} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {V : Set (Fin s → ℂ)} (hV_conn : IsPreconnected V) (hV0 : (0 : Fin s → ℂ) ∈ V)
    (hVU : ∀ y ∈ V, ((y, 0) : CParam s e) ∈ U)
    (hres_an : AnalyticOnNhd ℂ (weierstrassResFun m a) U)
    (hQ_an : AnalyticOnNhd ℂ Q U)
    (hP_an : AnalyticOnNhd ℂ P U)
    (hdisc_an : AnalyticOnNhd ℂ (weierstrassDiscFn m a) U)
    (hres_ne : ∃ z ∈ U, weierstrassResFun m a z ≠ 0)
    (hQ_ne : ∃ z ∈ U, Q z ≠ 0)
    (hnorm : ∀ z ∈ U, P z ^ m = weierstrassResFun m a z * Q z)
    (hP_oi : ∀ y ∈ V, order ℂ P ((y, 0) : CParam s e) = order ℂ P ((0, 0) : CParam s e)) :
    ∀ y ∈ V, order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
      = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s e) := by
  -- The section as a subset of `U`.
  set ι : (Fin s → ℂ) → CParam s e := fun y => (y, 0) with hι
  have hι_cont : Continuous ι := by fun_prop
  set S : Set (CParam s e) := ι '' V with hS
  have hS_conn : IsPreconnected S := hV_conn.image ι hι_cont.continuousOn
  have hSU : S ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hVU y hy
  have hz₀S : ((0, 0) : CParam s e) ∈ S := ⟨0, hV0, rfl⟩
  -- On `U`, `resultant·Q` and `P^m` agree, so their orders agree; and `order(P^m) = m·order P`.
  have horder : ∀ z ∈ U,
      order ℂ (fun w => weierstrassResFun m a w * Q w) z = (m : ℕ∞) * order ℂ P z := by
    intro z hz
    have hee : (fun w => P w ^ m) =ᶠ[𝓝 z] fun w => weierstrassResFun m a w * Q w :=
      eventually_of_mem (hU_open.mem_nhds hz) (fun w hw => hnorm w hw)
    rw [← order_congr_of_eventuallyEq' hee, order_pow_analytic P z (hP_an z hz) m]
  -- The product `resultant·Q` has constant order along `S` (from the witness, via `horder`).
  have hfg_const : ∀ z ∈ S, order ℂ (fun w => weierstrassResFun m a w * Q w) z
      = order ℂ (fun w => weierstrassResFun m a w * Q w) ((0, 0) : CParam s e) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [horder _ (hVU y hy), horder _ (hVU 0 hV0), hP_oi y hy]
  -- Apply the preconnected reverse factor bridge to peel off `resultant`.
  have hbridge := (order_factor_const_of_mul_analytic hU_open hU_conn hS_conn hSU
    (weierstrassResFun m a) Q hres_an hQ_an hres_ne hQ_ne ((0, 0) : CParam s e) hz₀S hfg_const).1
  -- Transfer `order(resultant) = order(disc)` and conclude.
  intro y hy
  have hyS : ι y ∈ S := ⟨y, hy, rfl⟩
  rw [← order_weierstrassResFun_eq m a hm _ (hdisc_an _ (hVU y hy)),
      ← order_weierstrassResFun_eq m a hm _ (hdisc_an _ (hVU 0 hV0))]
  exact hbridge (ι y) hyS

end
