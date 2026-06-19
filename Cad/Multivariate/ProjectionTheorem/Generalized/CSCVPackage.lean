import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVIterated
import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVBridgeN
import Cad.Multivariate.ProjectionTheorem.Generalized.CParamIntegral

/-!
# Packaging the multi-index value into `AnalyticAt` — completing the `ℂⁿ` bridge

`multiIndexCauchy` gives a function differentiable + bounded on a polydisc a multi-index power-series
expansion `f(z₀+y) = ∑_α c_α ∏ⱼ yⱼ^{αⱼ}` with `‖c_α‖ ≤ M/r^{|α|}`. This file packages that value into
a genuine `FormalMultilinearSeries` and `HasFPowerSeriesOnBall`, hence `AnalyticAt`, hence
`HoloBridge (Fin n → ℂ)` — the keystone behind `weierstrass_division`.

The degree-`N` term of the series sums, over all multi-indices `α` of total degree `N`
(`Finset.Nat.antidiagonalTuple n N`), the asymmetric monomial `mtTerm (c α) (realizeAssign N α)`. Both
the radius bound and the value `HasSum` reduce, via `Finset.Nat.sigmaAntidiagonalTupleEquivTuple`, to
the multi-index summability `summable_multiIndex_pow` and `multiIndexCauchy` — no multiplicities.
-/

noncomputable section

open Metric Finset
open scoped Topology

/-- **Degree regrouping.** A `HasSum` over multi-indices `α : Fin n → ℕ` regroups into a `HasSum` over
the total degree `N`, the degree-`N` term being the finite sum over `antidiagonalTuple n N`. -/
theorem hasSum_degree_regroup {n : ℕ} {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] [RegularSpace M] {F : (Fin n → ℕ) → M} {S : M} (h : HasSum F S) :
    HasSum (fun N => ∑ α ∈ Finset.Nat.antidiagonalTuple n N, F α) S := by
  have h2 : HasSum (F ∘ Finset.Nat.sigmaAntidiagonalTupleEquivTuple n) S :=
    (Equiv.hasSum_iff (Finset.Nat.sigmaAntidiagonalTupleEquivTuple n)).mpr h
  refine h2.sigma fun N => ?_
  have key : (∑ c : ↥(Finset.Nat.antidiagonalTuple n N),
      (F ∘ Finset.Nat.sigmaAntidiagonalTupleEquivTuple n) ⟨N, c⟩)
      = ∑ α ∈ Finset.Nat.antidiagonalTuple n N, F α := Finset.sum_coe_sort _ F
  exact key ▸ hasSum_fintype _

/-- The `ℝ`-summability version of degree regrouping. -/
theorem summable_degree_regroup {n : ℕ} {H : (Fin n → ℕ) → ℝ} (h : Summable H) :
    Summable (fun N => ∑ α ∈ Finset.Nat.antidiagonalTuple n N, H α) :=
  (hasSum_degree_regroup h.hasSum).summable

/-- **The multi-index power series** on `ℂⁿ` (`n ≥ 1`): the degree-`N` term sums the monomial term
`mtTerm (c α) (realizeAssign N α)` over all multi-indices `α` of total degree `N`. -/
noncomputable def miSeries {n : ℕ} [NeZero n] (c : (Fin n → ℕ) → ℂ) :
    FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ :=
  fun N => ∑ α ∈ Finset.Nat.antidiagonalTuple n N, mtTerm (c α) (realizeAssign N α)

/-- **Diagonal of `miSeries`:** `(miSeries c) N (y,…,y) = ∑_{|α|=N} c_α · ∏ⱼ yⱼ^{αⱼ}`. -/
theorem miSeries_apply_diag {n : ℕ} [NeZero n] (c : (Fin n → ℕ) → ℂ) (N : ℕ) (y : Fin n → ℂ) :
    miSeries c N (fun _ => y) = ∑ α ∈ Finset.Nat.antidiagonalTuple n N, c α * ∏ j, y j ^ α j := by
  rw [miSeries, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [mtTerm_apply_diag, realizeAssign_prod (Finset.Nat.mem_antidiagonalTuple.mp hα)]

/-- **Norm bound on `miSeries`:** `‖(miSeries c) N‖ ≤ ∑_{|α|=N} ‖c_α‖`. -/
theorem norm_miSeries_le {n : ℕ} [NeZero n] (c : (Fin n → ℕ) → ℂ) (N : ℕ) :
    ‖miSeries c N‖ ≤ ∑ α ∈ Finset.Nat.antidiagonalTuple n N, ‖c α‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_mtTerm_le _ _)

/-- **From the multi-index value to `AnalyticAt`.** If `f(z₀+y) = ∑_α c_α ∏ⱼ yⱼ^{αⱼ}` for `‖y‖ < r`
with the Cauchy bound `‖c_α‖ ≤ M/r^{|α|}`, then `f` is analytic at `z₀`. -/
theorem analyticAt_of_multiIndex {n : ℕ} [NeZero n] {f : (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    {c : (Fin n → ℕ) → ℂ} {M r : ℝ} (hr : 0 < r)
    (hb : ∀ α, ‖c α‖ ≤ M / r ^ (∑ j, α j))
    (hsum : ∀ y : Fin n → ℂ, ‖y‖ < r →
      HasSum (fun α => c α * ∏ j, y j ^ α j) (f (z₀ + y))) :
    AnalyticAt ℂ f z₀ := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  set ρ : NNReal := (r / 2).toNNReal with hρ_def
  have hρc : (ρ : ℝ) = r / 2 := Real.coe_toNNReal _ hr2.le
  have hρr : (ρ : ℝ) < r := by rw [hρc]; linarith
  have hρ0 : (0 : ℝ) < ρ := by rw [hρc]; linarith
  -- the multi-index family `‖c_α‖ · ρ^{|α|}` is summable
  have hHsummable : Summable (fun α : Fin n → ℕ => ‖c α‖ * (ρ : ℝ) ^ (∑ j, α j)) := by
    refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
      ((summable_multiIndex_pow n (by positivity : (0 : ℝ) ≤ ρ / r) ((div_lt_one hr).mpr hρr)).mul_left M)
    calc ‖c α‖ * (ρ : ℝ) ^ (∑ j, α j)
        ≤ (M / r ^ (∑ j, α j)) * (ρ : ℝ) ^ (∑ j, α j) := by gcongr; exact hb α
      _ = M * (ρ / r) ^ (∑ j, α j) := by rw [div_pow]; ring
  refine HasFPowerSeriesOnBall.analyticAt
    (p := miSeries c) (r := (ρ : ENNReal)) ⟨?_, ?_, ?_⟩
  · -- radius
    apply (miSeries c).le_radius_of_summable
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
      (summable_degree_regroup hHsummable)
    calc ‖miSeries c N‖ * (ρ : ℝ) ^ N
        ≤ (∑ α ∈ Finset.Nat.antidiagonalTuple n N, ‖c α‖) * (ρ : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (norm_miSeries_le c N) (by positivity)
      _ = ∑ α ∈ Finset.Nat.antidiagonalTuple n N, ‖c α‖ * (ρ : ℝ) ^ N := by rw [Finset.sum_mul]
      _ = ∑ α ∈ Finset.Nat.antidiagonalTuple n N, ‖c α‖ * (ρ : ℝ) ^ (∑ j, α j) :=
          Finset.sum_congr rfl fun α hα => by
            rw [Finset.Nat.mem_antidiagonalTuple.mp hα]
  · rw [ENNReal.coe_pos, ← NNReal.coe_pos]; exact hρ0
  · intro y hy
    have hyr : ‖y‖ < r := by
      have h := mem_eball_zero_iff.mp hy
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm] at h
      exact lt_trans h hρr
    have hval := hasSum_degree_regroup (hsum y hyr)
    have hfeq : (fun N => miSeries c N (fun _ : Fin N => y))
        = fun N => ∑ α ∈ Finset.Nat.antidiagonalTuple n N, c α * ∏ j, y j ^ α j := by
      funext N; exact miSeries_apply_diag c N y
    rw [hfeq]; exact hval

/-- **The `ℂⁿ` holomorphy⇒analyticity bridge.** Combining the multi-index Cauchy expansion
(`multiIndexCauchy`) with the packaging `analyticAt_of_multiIndex`. -/
theorem holoBridge_finToC (n : ℕ) : HoloBridge (Fin n → ℂ) := by
  cases n with
  | zero => exact holoBridge_finZero
  | succ m =>
    intro f U hU hf x hx
    haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
    -- a closed polydisc-ball `closedBall x R ⊆ U`
    obtain ⟨ε, hε0, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    set R : ℝ := ε / 2 with hR_def
    have hR0 : 0 < R := by rw [hR_def]; linarith
    have hsub : closedBall x R ⊆ U := fun z hz =>
      hεU (by rw [mem_ball]; rw [mem_closedBall] at hz; rw [hR_def] at hz; linarith)
    -- `f` differentiable on the polydisc-ball
    have hdiff : ∀ z ∈ closedBall x R, DifferentiableAt ℂ f z := fun z hz =>
      hf.differentiableAt (hU.mem_nhds (hsub hz))
    -- `f` bounded on the (compact) polydisc-ball
    have hcompact : IsCompact (closedBall x R) := isCompact_closedBall x R
    obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
      (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    -- multi-index expansion at working radius `r = R/2`
    obtain ⟨c, hb, hsum⟩ := multiIndexCauchy (m + 1) f x hdiff hM (by linarith : (0:ℝ) < R / 2)
      (by linarith : R / 2 < R)
    exact analyticAt_of_multiIndex (by linarith : (0:ℝ) < R / 2) hb hsum

/-- **The `ℂ`-holomorphy⇒analyticity bridge on any finite-dimensional `ℂ`-space**, by transporting
`holoBridge_finToC` along the canonical isomorphism `H ≃L[ℂ] (Fin (finrank ℂ H) → ℂ)`. -/
theorem holoBridge_findim {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] : HoloBridge H :=
  HoloBridge.congr
    (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℂ)
      (by rw [Module.finrank_pi, Fintype.card_fin]) :
        H ≃L[ℂ] (Fin (Module.finrank ℂ H) → ℂ)).symm
    (holoBridge_finToC (Module.finrank ℂ H))

/-- **The multi-parameter keystone, now unconditional.** The parametric circle integral
`z ↦ ∮ Φ(z,ζ) dζ` is `AnalyticAt` in the finite-dimensional parameter `z`, with the
several-variable holomorphy⇒analyticity bridge supplied by `holoBridge_findim` (no axiom). -/
theorem circleIntegral_analyticAt_keystone {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] {Φ : H → ℂ → ℂ} {Φ' : H → ℂ → (H →L[ℂ] ℂ)} {c : ℂ} {R : ℝ}
    {z₀ : H} {δ : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (hΦ : ContinuousOn (fun p : H × ℂ => Φ p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hΦ' : ContinuousOn (fun p : H × ℂ => Φ' p.1 p.2) (closedBall z₀ δ ×ˢ sphere c R))
    (hderiv : ∀ z ∈ ball z₀ δ, ∀ ζ ∈ sphere c R, HasFDerivAt (fun w => Φ w ζ) (Φ' z ζ) z) :
    AnalyticAt ℂ (fun z => ∮ ζ in C(c, R), Φ z ζ) z₀ := by
  haveI : ProperSpace H := FiniteDimensional.proper ℂ H
  exact circleIntegral_analyticAt_multi (fun _ _ hU hf => holoBridge_findim hU hf)
    hδ hR hΦ hΦ' hderiv

/-- **The keystone in fiber form (unconditional).** If the integrand `Φ : H × ℂ → ℂ` is `AnalyticAt`
at `(p₀, ζ)` for every `ζ` on the circle, then the parametric circle integral
`p ↦ ∮_{C(0,r)} Φ(p,ζ) dζ` is `AnalyticAt` at `p₀`. This is exactly the `keystone` hypothesis consumed
by `weierstrass_division_W_exists` — now a theorem (no axiom). Proof: a tube around the compact fiber
`{p₀} × sphere` lands in the open analytic locus, giving uniform continuity / differentiability data on
a polydisc; feed `circleIntegral_analyticAt_keystone`. -/
theorem circleIntegral_analyticAt_fiber {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] (Φ : H × ℂ → ℂ) {r : ℝ} {p₀ : H} (hr : 0 < r)
    (hΦan : ∀ ζ ∈ sphere (0 : ℂ) r, AnalyticAt ℂ Φ (p₀, ζ)) :
    AnalyticAt ℂ (fun p : H => ∮ ζ in C(0, r), Φ (p, ζ)) p₀ := by
  obtain ⟨u, v, hu, _, hpu, hsv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_sphere (0 : ℂ) r) (isOpen_analyticAt ℂ Φ)
    (by rintro ⟨z, ζ⟩ ⟨hz, hζ⟩; rw [Set.mem_singleton_iff] at hz; subst hz; exact hΦan ζ hζ)
  obtain ⟨δ, hδ0, hδu⟩ := Metric.isOpen_iff.mp hu p₀ (hpu rfl)
  have htube : closedBall p₀ (δ / 2) ×ˢ sphere (0 : ℂ) r ⊆ u ×ˢ v := by
    rintro ⟨z, ζ⟩ ⟨hz, hζ⟩
    exact Set.mk_mem_prod (hδu (by rw [mem_ball]; rw [mem_closedBall] at hz; linarith)) (hsv hζ)
  have hanTube : ∀ q ∈ closedBall p₀ (δ / 2) ×ˢ sphere (0 : ℂ) r, AnalyticAt ℂ Φ q :=
    fun q hq => huv (htube hq)
  have hfderiv_cont : ContinuousOn (fderiv ℂ Φ) (u ×ˢ v) :=
    ((show AnalyticOnNhd ℂ Φ (u ×ˢ v) from fun q hq => huv hq).fderiv).continuousOn
  refine circleIntegral_analyticAt_keystone (Φ := fun z ζ => Φ (z, ζ))
    (Φ' := fun z ζ => (fderiv ℂ Φ (z, ζ)).comp (ContinuousLinearMap.inl ℂ H ℂ))
    (δ := δ / 2) (by linarith) hr.le ?_ ?_ ?_
  · exact fun q hq => (hanTube q hq).continuousAt.continuousWithinAt
  · have hcomp : Continuous (fun L : (H × ℂ) →L[ℂ] ℂ => L.comp (ContinuousLinearMap.inl ℂ H ℂ)) :=
      ((ContinuousLinearMap.compL ℂ H (H × ℂ) ℂ).flip (ContinuousLinearMap.inl ℂ H ℂ)).continuous
    exact hcomp.comp_continuousOn (hfderiv_cont.mono htube)
  · intro z hz ζ hζ
    have hΦd : HasFDerivAt Φ (fderiv ℂ Φ (z, ζ)) (z, ζ) :=
      (hanTube (z, ζ) (Set.mk_mem_prod (ball_subset_closedBall hz) hζ)).differentiableAt.hasFDerivAt
    have hmap : HasFDerivAt (fun w : H => (w, ζ)) (ContinuousLinearMap.inl ℂ H ℂ) z := by
      simpa using (hasFDerivAt_id z).prodMk (hasFDerivAt_const ζ z)
    exact hΦd.comp z hmap

end
