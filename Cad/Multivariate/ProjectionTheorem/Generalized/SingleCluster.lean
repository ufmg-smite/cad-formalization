import Cad.Multivariate.ProjectionTheorem.Generalized.ClusterRootStructure
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassResAnalytic
import Cad.Multivariate.ProjectionTheorem.Generalized.DiscOrder
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Single-cluster composition (front-half glue + full single-cluster result)

`single_cluster_complex` wires the whole complex single-cluster chain:
`descent_norm_identity` output (the `=ᶠ` norm identity `P^m =ᶠ weierstrassResFun·Q` with `Q` analytic)
+ the witness's constant section-order ⟹ (via `DiscOrder` and the analyticity helpers) the
discriminant-order hypothesis ⟹ (via `cluster_root_structure`/Zariski/F2) the holomorphic root
sections and their root/multiplicity structure.

Key point: the non-vanishing of `weierstrassResFun`/`Q` that `DiscOrder` needs is *not* an extra
hypothesis — it follows from `P ≢ 0` (i.e. `order P 0 ≠ ⊤`), since `P^m = weierstrassResFun·Q`.
The open connected neighbourhood `U`/section `V` are taken to be metric balls.
-/

noncomputable section

open Polynomial Filter Metric
open scoped Topology

/-- **Single-cluster (complex).** From the descent's norm identity + constant witness section-order,
produce the holomorphic root sections of the section Weierstrass polynomial with their full root /
multiplicity structure. -/
theorem single_cluster_complex {s e : ℕ} (m : ℕ) (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (P Q : CParam s e → ℂ) (hP_an : AnalyticAt ℂ P 0) (hQ_an : AnalyticAt ℂ Q 0)
    (hP_ne : order ℂ P 0 ≠ ⊤)
    (hnorm : (fun w => P w ^ m) =ᶠ[𝓝 0] fun w => weierstrassResFun m a w * Q w)
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
  have hRan : AnalyticAt ℂ (weierstrassResFun m a) 0 := weierstrassResFun_analyticAt a ha_an
  have hDan : AnalyticAt ℂ (weierstrassDiscFn m a) 0 := weierstrassDiscFn_analyticAt hm a ha_an
  -- A neighbourhood where all four functions are analytic and the norm identity holds.
  have hW : ∀ᶠ z in 𝓝 (0 : CParam s e),
      AnalyticAt ℂ P z ∧ AnalyticAt ℂ Q z ∧ AnalyticAt ℂ (weierstrassResFun m a) z
      ∧ AnalyticAt ℂ (weierstrassDiscFn m a) z ∧ P z ^ m = weierstrassResFun m a z * Q z := by
    filter_upwards [hP_an.eventually_analyticAt, hQ_an.eventually_analyticAt,
      hRan.eventually_analyticAt, hDan.eventually_analyticAt, hnorm] with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  set U := Metric.ball (0 : CParam s e) ε with hU
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_conn : IsConnected U := isConnected_ball hε
  have hU0 : (0 : CParam s e) ∈ U := Metric.mem_ball_self hε
  have hU_nhds : U ∈ 𝓝 (0 : CParam s e) := hU_open.mem_nhds hU0
  -- Non-vanishing: `P ≢ 0` gives a point of `U` with `P ≠ 0`, hence `resFun, Q ≠ 0` there.
  have hPfreq : ∃ᶠ z in 𝓝 (0 : CParam s e), P z ≠ 0 := by
    have hnot : ¬ (P =ᶠ[𝓝 0] 0) := fun h => hP_ne (order_eq_top_of_eventuallyEq_zero P 0 h)
    simpa using Filter.not_eventually.mp hnot
  obtain ⟨z₀, hz₀ne, hz₀U⟩ := (hPfreq.and_eventually hU_nhds).exists
  have hz₀norm : P z₀ ^ m = weierstrassResFun m a z₀ * Q z₀ := (hball hz₀U).2.2.2.2
  have hPmne : P z₀ ^ m ≠ 0 := pow_ne_zero _ hz₀ne
  have hres_ne : ∃ z ∈ U, weierstrassResFun m a z ≠ 0 :=
    ⟨z₀, hz₀U, fun h => hPmne (by rw [hz₀norm, h, zero_mul])⟩
  have hQ_ne : ∃ z ∈ U, Q z ≠ 0 :=
    ⟨z₀, hz₀U, fun h => hPmne (by rw [hz₀norm, h, mul_zero])⟩
  -- The section `V`: a ball inside `(·,0) ⁻¹' U` where the witness order is also constant.
  have hVnhds : (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) ⁻¹' U
      ∩ {y | order ℂ P ((y, 0) : CParam s e) = order ℂ P ((0, 0) : CParam s e)} ∈ 𝓝 (0 : Fin s → ℂ) := by
    refine Filter.inter_mem ?_ hP_oi
    exact (Continuous.continuousAt (by fun_prop)).preimage_mem_nhds (by simpa using hU_nhds)
  obtain ⟨δ, hδ, hVball⟩ := Metric.mem_nhds_iff.mp hVnhds
  set V := Metric.ball (0 : Fin s → ℂ) δ with hV
  have hV0 : (0 : Fin s → ℂ) ∈ V := Metric.mem_ball_self hδ
  have hV_conn : IsPreconnected V := (isConnected_ball hδ).isPreconnected
  have hVU : ∀ y ∈ V, ((y, 0) : CParam s e) ∈ U := fun y hy => (hVball hy).1
  have hP_oiV : ∀ y ∈ V, order ℂ P ((y, 0) : CParam s e) = order ℂ P ((0, 0) : CParam s e) :=
    fun y hy => (hVball hy).2
  -- Apply `DiscOrder` to get constant discriminant order along the section.
  have hdiscV := weierstrassDisc_order_const_along_section m hm a P Q hU_open hU_conn hV_conn hV0 hVU
    (fun z hz => (hball hz).2.2.1) (fun z hz => (hball hz).2.1) (fun z hz => (hball hz).1)
    (fun z hz => (hball hz).2.2.2.1) hres_ne hQ_ne
    (fun z hz => (hball hz).2.2.2.2) hP_oiV
  -- `disc(h) ≢ 0` (from `res ≢ 0`, since `P^m = res·Q` and `P ≢ 0`), then Zariski 4.1.1.
  have hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤ := by
    rw [← order_weierstrassResFun_eq m a hm (0 : CParam s e) hDan]
    exact order_ne_top_of_ne_zero U hU_conn _ (fun z hz => (hball hz).2.2.1) hres_ne 0 hU0
  refine cluster_root_structure m hm a ha_an ha0 hdisc_ne ?_
  filter_upwards [Metric.ball_mem_nhds (0 : Fin s → ℂ) hδ] with y hy
  exact hdiscV y hy

end
