import Cad.Multivariate.ProjectionTheorem.Puiseux.ParametrizationFamily
import Cad.Multivariate.ProjectionTheorem.Generalized.RootBound
import Cad.Multivariate.ProjectionTheorem.Generalized.DiscNormalForm
import Cad.Multivariate.ProjectionTheorem.Generalized.SeparableDiscr
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Order-invariance via continuity of Cauchy coefficients (route 3)

The codim-1 order-invariance (Zariski 4.1.1, conclusion 2 / Lemmas 4.2.7–4.2.8) is proved here
**analytically**, using the existing Newton–Puiseux parametrization `φ(z,u)` (`exists_param_family`)
together with **continuity** (not analyticity) of the Cauchy-integral coefficients of the analytic
branches. This sidesteps both the formal-Puiseux machinery and the several-variable
analyticity (Hartogs) gap: every place that needs regularity in the section variable `z` needs only
*continuity*, which follows from `continuous_parametric_intervalIntegral_of_continuous'`.

This file starts with the linchpin: a Cauchy-type coefficient `z ↦ ∮_{|u|=ρ} F(z,u)·uᵏ du` is
continuous in `z` whenever `F` is jointly continuous.
-/

noncomputable section

open Filter Topology Complex MeasureTheory intervalIntegral
open scoped Real

namespace Puiseux

/-! ### `order ℂ` invariance under analytic diffeomorphisms (Phase 0 infrastructure)

`ℂ`-coefficient analogues of the `ℝ`-valued order-composition lemmas in `Cad.Multivariate.ProjectionTheorem.OrderComp`, needed to
transport the multivariate `order ℂ` through the analytic `ψ`-translation shear. -/

section OrderCompC

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- If all `ℂ`-Fréchet derivatives of order `< k` of `f` vanish at `x`, then `k ≤ order ℂ f x`. -/
theorem le_order_of_forall_iteratedFDeriv_eq_zero_C {f : E → ℂ} {x : E} {k : ℕ∞}
    (h : ∀ j : ℕ, (↑j : ℕ∞) < k → iteratedFDeriv ℂ j f x = 0) :
    k ≤ order ℂ f x := by
  by_contra hlt
  push_neg at hlt
  have hfin : order ℂ f x ≠ ⊤ := ne_top_of_lt hlt
  have hm : order ℂ f x = ↑(order ℂ f x).toNat := (ENat.coe_toNat hfin).symm
  rw [hm] at hlt
  exact (((order_eq_natCast_iff).mp hm).2) (h _ hlt)

/-- The vanishing `order ℂ` depends only on the germ. -/
theorem order_congr_of_eventuallyEq_C {f₁ f₂ : E → ℂ} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    order ℂ f₁ x = order ℂ f₂ x := by
  have key : ∀ n, iteratedFDeriv ℂ n f₁ x = iteratedFDeriv ℂ n f₂ x :=
    fun n => (h.iteratedFDeriv ℂ n).eq_of_nhds
  apply le_antisymm
  · apply le_order_of_forall_iteratedFDeriv_eq_zero_C
    intro j hj; rw [← key]; exact iteratedFDeriv_eq_zero_of_lt_order hj
  · apply le_order_of_forall_iteratedFDeriv_eq_zero_C
    intro j hj; rw [key]; exact iteratedFDeriv_eq_zero_of_lt_order hj

/-- Composing with an analytic map can only increase `order ℂ` (`ℂ`-valued version). -/
theorem order_le_order_comp_C {g : F → ℂ} {f : E → F} {s : Set E} {t : Set F} {x : E}
    (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hg : ContDiffOn ℂ (⊤ : WithTop ℕ∞) g t) (hf : ContDiffOn ℂ (⊤ : WithTop ℕ∞) f s)
    (hmaps : Set.MapsTo f s t) :
    order ℂ g (f x) ≤ order ℂ (g ∘ f) x := by
  apply le_order_of_forall_iteratedFDeriv_eq_zero_C
  intro j hj
  have hfx_t : f x ∈ t := hmaps hx
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℂ i g t (f x)‖ ≤ 0 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i ht hfx_t,
      iteratedFDeriv_eq_zero_of_lt_order (lt_of_le_of_lt (by exact_mod_cast hi) hj), norm_zero]
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℂ i f s x‖ ≤ D ^ i := by
    refine ⟨1 + ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℂ k f s x‖, ?_⟩
    intro i hi1 hij
    set D := 1 + ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℂ k f s x‖ with hDdef
    have hle : ‖iteratedFDerivWithin ℂ i f s x‖ ≤
        ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℂ k f s x‖ :=
      Finset.single_le_sum (f := fun k => ‖iteratedFDerivWithin ℂ k f s x‖)
        (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
    have hsum_nn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℂ k f s x‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    have h1D : (1 : ℝ) ≤ D := by rw [hDdef]; linarith
    calc ‖iteratedFDerivWithin ℂ i f s x‖ ≤ D := by rw [hDdef]; linarith
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ h1D hi1
  have hbound := norm_iteratedFDerivWithin_comp_le hg hf le_top ht.uniqueDiffOn hs.uniqueDiffOn
    hmaps hx hC hD
  rw [mul_zero, zero_mul] at hbound
  rw [iteratedFDerivWithin_of_isOpen j hs hx] at hbound
  exact norm_le_zero_iff.mp hbound

/-- **`order ℂ` is invariant under a local analytic diffeomorphism.** -/
theorem order_comp_eq_of_diffeo_C {g : F → ℂ} {e : E → F} {e' : F → E} {s : Set E} {t : Set F}
    {x : E} (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hg : ContDiffOn ℂ (⊤ : WithTop ℕ∞) g t)
    (he : ContDiffOn ℂ (⊤ : WithTop ℕ∞) e s) (he' : ContDiffOn ℂ (⊤ : WithTop ℕ∞) e' t)
    (hmaps : Set.MapsTo e s t) (hmaps' : Set.MapsTo e' t s)
    (hinv : e' (e x) = x) (hinv' : ∀ y ∈ t, e (e' y) = y) :
    order ℂ (g ∘ e) x = order ℂ g (e x) := by
  refine le_antisymm ?_ (order_le_order_comp_C hs ht hx hg he hmaps)
  have hge : ContDiffOn ℂ (⊤ : WithTop ℕ∞) (g ∘ e) s := hg.comp he hmaps
  have h1 : order ℂ (g ∘ e) (e' (e x)) ≤ order ℂ ((g ∘ e) ∘ e') (e x) :=
    order_le_order_comp_C ht hs (hmaps hx) hge he' hmaps'
  rw [hinv] at h1
  have h2 : order ℂ ((g ∘ e) ∘ e') (e x) = order ℂ g (e x) := by
    apply order_congr_of_eventuallyEq_C
    filter_upwards [ht.mem_nhds (hmaps hx)] with y hy
    simp only [Function.comp_apply, hinv' y hy]
  rwa [h2] at h1

end OrderCompC

/-- **Order bound from a nonzero Cauchy coefficient.** If `g` is analytic on `ball 0 R`, `ρ ∈ (0,R)`,
and the `K`-th Cauchy coefficient `∮_{|u|=ρ} g(u)·u^(-K-1) du ≠ 0`, then `g` vanishes to order `≤ K`
at `0`. (Contrapositive: if `g` vanishes to order `> K`, then `g(u)·u^(-K-1)` extends analytically
across `0`, so its circle integral is `0` by Cauchy–Goursat.) This is the engine of the
upper-semicontinuity step in Lemma 4.2.7. -/
theorem analyticOrderAt_le_of_circleIntegral_ne {g : ℂ → ℂ} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R)) (K : ℕ)
    (hne : (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) ≠ 0) :
    analyticOrderAt g 0 ≤ (K : ℕ∞) := by
  by_contra h
  rw [not_le] at h
  have hK1 : ((K + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 := by
    rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt h
  have hg0 : AnalyticAt ℂ g 0 := hg 0 (Metric.mem_ball_self (lt_trans hρ hρR))
  obtain ⟨g₁, hg₁an, hfac⟩ := (natCast_le_analyticOrderAt hg0).mp hK1
  set G : ℂ → ℂ := Function.update (fun u => g u * u ^ (-(K : ℤ) - 1)) 0 (g₁ 0) with hG
  -- `G` agrees with `g₁` near `0`
  have hGg₁ : G =ᶠ[𝓝 0] g₁ := by
    filter_upwards [hfac] with u hu
    rcases eq_or_ne u 0 with rfl | hune
    · rw [hG, Function.update_self]
    · rw [hG, Function.update_of_ne hune, hu, sub_zero, smul_eq_mul, ← zpow_natCast u (K + 1)]
      have hexp : ((K + 1 : ℕ) : ℤ) + (-(K : ℤ) - 1) = 0 := by push_cast; ring
      have hpow : (u : ℂ) ^ ((K + 1 : ℕ) : ℤ) * u ^ (-(K : ℤ) - 1) = 1 := by
        rw [← zpow_add₀ hune, hexp, zpow_zero]
      linear_combination g₁ u * hpow
  -- `G` is analytic on `ball 0 R`
  have hGan : AnalyticOnNhd ℂ G (Metric.ball 0 R) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hune
    · exact (hg₁an.congr hGg₁.symm)
    · have : G =ᶠ[𝓝 u] fun v => g v * v ^ (-(K : ℤ) - 1) := by
        filter_upwards [eventually_nhds_iff.mpr ⟨{0}ᶜ, fun _ h => h, isOpen_compl_singleton,
          Set.mem_compl_singleton_iff.mpr hune⟩] with v hv
        have hv' : v ≠ 0 := hv
        rw [hG, Function.update_of_ne hv']
      refine AnalyticAt.congr ?_ this.symm
      exact (hg u hu).mul (analyticAt_id.zpow hune)
  -- the circle integral of `g·u^(-K-1)` equals that of the analytic `G`, which is `0`
  have hcong : (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) = ∮ u in C(0, ρ), G u := by
    refine circleIntegral.integral_congr hρ.le (fun u hu => ?_)
    have hune : u ≠ 0 := by
      rw [Metric.mem_sphere, dist_zero_right] at hu; rw [← norm_pos_iff, hu]; exact hρ
    rw [hG, Function.update_of_ne hune]
  have hzero : (∮ u in C(0, ρ), G u) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero hρ.le ?_
    refine DiffContOnCl.mk ?_ ?_
    · intro u hu
      exact ((hGan u (Metric.ball_subset_ball hρR.le hu)).differentiableAt).differentiableWithinAt
    · refine (hGan.continuousOn).mono ?_
      rw [closure_ball 0 hρ.ne']
      exact Metric.closedBall_subset_ball hρR
  rw [hcong, hzero] at hne
  exact hne rfl

/-- **Nonzero Cauchy coefficient at the exact order.** If `g` is analytic on `ball 0 R`, `ρ ∈ (0,R)`,
and `g` vanishes to order *exactly* `K` at `0`, then the `K`-th Cauchy coefficient
`∮_{|u|=ρ} g(u)·u^(-K-1) du = 2πi·g₁(0) ≠ 0` (where `g = uᴷ·g₁`, `g₁(0) ≠ 0`). Dual to
`analyticOrderAt_le_of_circleIntegral_ne`; together they give upper-semicontinuity of the order. -/
theorem circleIntegral_ne_of_analyticOrderAt_eq {g : ℂ → ℂ} {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R)) (K : ℕ)
    (hord : analyticOrderAt g 0 = (K : ℕ∞)) :
    (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) ≠ 0 := by
  have hg0 : AnalyticAt ℂ g 0 := hg 0 (Metric.mem_ball_self (lt_trans hρ hρR))
  obtain ⟨g₁, hg₁an, hg₁0, hfac⟩ := hg0.analyticOrderAt_eq_natCast.mp hord
  set G : ℂ → ℂ := Function.update (fun u => g u * u ^ (-(K : ℤ))) 0 (g₁ 0) with hG
  have hG0 : G 0 = g₁ 0 := Function.update_self _ _ _
  have hGg₁ : G =ᶠ[𝓝 0] g₁ := by
    filter_upwards [hfac] with u hu
    rcases eq_or_ne u 0 with rfl | hune
    · rw [hG, Function.update_self]
    · rw [hG, Function.update_of_ne hune, hu, sub_zero, smul_eq_mul, ← zpow_natCast u K]
      have hexp : ((K : ℕ) : ℤ) + (-(K : ℤ)) = 0 := by ring
      have hpow : (u : ℂ) ^ ((K : ℕ) : ℤ) * u ^ (-(K : ℤ)) = 1 := by
        rw [← zpow_add₀ hune, hexp, zpow_zero]
      linear_combination g₁ u * hpow
  have hGan : AnalyticOnNhd ℂ G (Metric.ball 0 R) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hune
    · exact hg₁an.congr hGg₁.symm
    · have : G =ᶠ[𝓝 u] fun v => g v * v ^ (-(K : ℤ)) := by
        filter_upwards [eventually_nhds_iff.mpr ⟨{0}ᶜ, fun _ h => h, isOpen_compl_singleton,
          Set.mem_compl_singleton_iff.mpr hune⟩] with v hv
        have hv' : v ≠ 0 := hv
        rw [hG, Function.update_of_ne hv']
      exact AnalyticAt.congr ((hg u hu).mul (analyticAt_id.zpow hune)) this.symm
  -- rewrite the `K`-th coefficient integral as a value integral for `G`
  have hval : (∮ u in C(0, ρ), g u * u ^ (-(K : ℤ) - 1)) = ∮ u in C(0, ρ), (u - 0)⁻¹ • G u := by
    refine circleIntegral.integral_congr hρ.le (fun u hu => ?_)
    have hune : u ≠ 0 := by
      rw [Metric.mem_sphere, dist_zero_right] at hu; rw [← norm_pos_iff, hu]; exact hρ
    have hpow2 : (u : ℂ) ^ (-(K : ℤ) - 1) = u⁻¹ * u ^ (-(K : ℤ)) := by
      rw [← zpow_neg_one, ← zpow_add₀ hune]; congr 1; ring
    rw [hG, Function.update_of_ne hune, sub_zero, smul_eq_mul, hpow2]; ring
  -- Cauchy integral formula for the value
  have hformula : ((2 * π * I : ℂ)⁻¹ • ∮ u in C(0, ρ), (u - 0)⁻¹ • G u) = G 0 :=
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty (Metric.mem_ball_self hρ)
      ((hGan.continuousOn).mono (Metric.closedBall_subset_ball hρR))
      (fun u hu => (hGan u (Metric.ball_subset_ball hρR.le hu.1)).differentiableAt)
  intro hcontra
  rw [hval] at hcontra
  rw [hcontra, smul_zero, hG0] at hformula
  exact hg₁0 hformula.symm

/-- **Local continuity of a parametrized circle integral.** If `F` is jointly continuous on
`S ×ˢ {u ≠ 0}` for some neighbourhood `S` of `z₀`, then the Cauchy-type coefficient
`z ↦ ∮_{|u|=ρ} F z u · uᵏ du` is continuous *at* `z₀`. This is the local form of
`continuous_circleIntegral_param` (which it reuses, restricting to the open subtype `interior S`):
the Puiseux branches are only continuous on a bounded region, so only a *local* hypothesis is
available. -/
theorem continuousAt_circleIntegral_param {W : Type*} [TopologicalSpace W]
    {F : W → ℂ → ℂ} {z₀ : W} {S : Set W} {T : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hT : ∀ θ : ℝ, circleMap 0 ρ θ ∈ T) (hS : S ∈ 𝓝 z₀)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ T)) (k : ℤ) :
    ContinuousAt (fun z => ∮ u in C(0, ρ), F z u * u ^ k) z₀ := by
  have hz₀U : z₀ ∈ interior S := mem_interior_iff_mem_nhds.mpr hS
  have hcm : Continuous fun p : ↥(interior S) × ℝ => circleMap 0 ρ p.2 :=
    (continuous_circleMap 0 ρ).comp continuous_snd
  have hne : ∀ p : ↥(interior S) × ℝ, circleMap 0 ρ p.2 ≠ 0 := fun _ => circleMap_ne_center hρ.ne'
  have hmap : ∀ p : ↥(interior S) × ℝ, ((p.1.val, circleMap 0 ρ p.2) : W × ℂ) ∈ S ×ˢ T :=
    fun p => Set.mk_mem_prod (interior_subset p.1.2) (hT p.2)
  have hF' : Continuous fun p : ↥(interior S) × ℝ => F p.1.val (circleMap 0 ρ p.2) :=
    hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk hcm) hmap
  have hint : Continuous (Function.uncurry fun (z : ↥(interior S)) (θ : ℝ) =>
      deriv (circleMap 0 ρ) θ • (F z.val (circleMap 0 ρ θ) * circleMap 0 ρ θ ^ k)) := by
    simp only [Function.uncurry_def, deriv_circleMap, smul_eq_mul]
    exact ((hcm.mul continuous_const).mul (hF'.mul (hcm.zpow₀ k (fun p => Or.inl (hne p)))))
  have hcont : Continuous (fun z : ↥(interior S) => ∮ u in C(0, ρ), F z.val u * u ^ k) :=
    continuous_parametric_intervalIntegral_of_continuous' hint 0 (2 * π)
  have hrestr : ContinuousOn (fun z => ∮ u in C(0, ρ), F z u * u ^ k) (interior S) := by
    rw [continuousOn_iff_continuous_restrict]; exact hcont
  exact hrestr.continuousAt (isOpen_interior.mem_nhds hz₀U)

/-- **Upper-semicontinuity of the vanishing order (local form).** Like
`analyticOrderAt_le_eventually`, but the joint continuity of `g` is only required on
`S ×ˢ {u ≠ 0}` for a neighbourhood `S` of `z₀`. This is the form usable for the Puiseux branches,
which are analytic only on a bounded region. -/
theorem analyticOrderAt_le_eventually_local {W : Type*} [TopologicalSpace W] {g : W → ℂ → ℂ}
    {z₀ : W} {S : Set W} {T : Set ℂ} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hT : ∀ θ : ℝ, circleMap 0 ρ θ ∈ T) (hS : S ∈ 𝓝 z₀)
    (hg : ContinuousOn (Function.uncurry g) (S ×ˢ T))
    (hgan : ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ (g z) (Metric.ball 0 R)) {K : ℕ}
    (hord : analyticOrderAt (g z₀) 0 = (K : ℕ∞)) :
    ∀ᶠ z in 𝓝 z₀, analyticOrderAt (g z) 0 ≤ (K : ℕ∞) := by
  have hgz₀ : AnalyticOnNhd ℂ (g z₀) (Metric.ball 0 R) := hgan.self_of_nhds
  have hc0 : (∮ u in C(0, ρ), g z₀ u * u ^ (-(K : ℤ) - 1)) ≠ 0 :=
    circleIntegral_ne_of_analyticOrderAt_eq hρ hρR hgz₀ K hord
  have hcont : ContinuousAt (fun z => ∮ u in C(0, ρ), g z u * u ^ (-(K : ℤ) - 1)) z₀ :=
    continuousAt_circleIntegral_param hρ hT hS hg (-(K : ℤ) - 1)
  have hev : ∀ᶠ z in 𝓝 z₀, (∮ u in C(0, ρ), g z u * u ^ (-(K : ℤ) - 1)) ≠ 0 :=
    hcont.eventually_ne hc0
  filter_upwards [hev, hgan] with z hz hzan
  exact analyticOrderAt_le_of_circleIntegral_ne hρ hρR hzan K hz

/-! ### Puiseux branches and the discriminant identity (Lemma 4.2.7 setup) -/

/-- **The `m`-th roots of `uᵐ` are exactly the branch points `ζⁱ·u`.** For a primitive `m`-th root of
unity `ζ` and `u ≠ 0`, `u'ᵐ = uᵐ ↔ u' = ζⁱ·u` for some `i ∈ Fin m`. This underlies the indexed Puiseux
branches `θᵢ(z,u) = φ(z, ζⁱu)`. -/
theorem pow_eq_pow_iff_branch {ζ : ℂ} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    {u u' : ℂ} (hu : u ≠ 0) :
    u' ^ m = u ^ m ↔ ∃ i : Fin m, u' = ζ ^ (i : ℕ) * u := by
  haveI : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro h
    have hpow1 : (u' / u) ^ m = 1 := by rw [div_pow, h, div_self (pow_ne_zero m hu)]
    obtain ⟨i, hi, hpow⟩ := hζ.eq_pow_of_pow_eq_one hpow1
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [hpow]; field_simp
  · rintro ⟨i, rfl⟩
    rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) m, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

open Polynomial in
/-- **Discriminant as a product of root-differences.** For a monic complex polynomial `p` of positive
degree, `discr p = ±∏_{x ∈ roots} ∏_{s ∈ roots.erase x} (x - s)` (the sign is `(-1)^(d(d-1)/2)`).
Derived from `discr = ±resultant(p, p')`, `resultant = ∏ p'(roots)` (monic, splits over `ℂ`), and
`p'(x) = ∏_{s ≠ x}(x - s)` at each root. The order-in-a-parameter of this product is `2·Σ_{i<j}` the
orders of the root-differences — the discriminant–branch relation `r = 2·Σ O(η_{ij})` of Lemma 4.2.7. -/
theorem discr_eq_prod_roots {p : Polynomial ℂ} (hm : p.Monic) (hpos : 0 < p.natDegree) :
    p.discr = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) *
      (p.roots.map (fun x => ((p.roots.erase x).map (fun s => x - s)).prod)).prod := by
  classical
  set k := p.natDegree * (p.natDegree - 1) / 2 with hk
  have hsp : p.Splits := IsAlgClosed.splits p
  have hdeg_pos : 0 < p.degree := by
    rw [degree_eq_natDegree hm.ne_zero]; exact_mod_cast hpos
  have hdeg_der : (derivative p).natDegree = p.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq p hpos)
  have hres_eq : resultant p (derivative p) p.natDegree (derivative p).natDegree
      = (-1) ^ k * p.discr := by
    rw [hdeg_der, resultant_deriv hdeg_pos, hm.leadingCoeff, mul_one]
  have hres_prod : resultant p (derivative p) p.natDegree (derivative p).natDegree
      = (p.roots.map (fun x => (derivative p).eval x)).prod := by
    rw [resultant_eq_prod_eval p (derivative p) (derivative p).natDegree le_rfl hsp,
      hm.leadingCoeff, one_pow, one_mul]
  have heval : (p.roots.map (fun x => (derivative p).eval x)).prod
      = (p.roots.map (fun x => ((p.roots.erase x).map (fun s => x - s)).prod)).prod :=
    congrArg Multiset.prod (Multiset.map_congr rfl (fun x hx => hsp.eval_root_derivative hm hx))
  have h1 : (-1 : ℂ) ^ k * p.discr
      = (p.roots.map (fun x => ((p.roots.erase x).map (fun s => x - s)).prod)).prod := by
    rw [← hres_eq, hres_prod, heval]
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc p.discr = ((-1 : ℂ) ^ k * (-1) ^ k) * p.discr := by rw [hsq, one_mul]
    _ = (-1) ^ k * ((-1) ^ k * p.discr) := by ring
    _ = _ := by rw [h1]

/-- **Ramification multiplies the order.** For `f` analytic at `0` and `m ≥ 1`, the order of
`u ↦ f(uᵐ)` at `0` is `m` times the order of `f` at `0` (substituting `w = uᵐ` scales the leading
exponent by `m`). Turns `ord_w disc` into `ord_u disc(z, uᵐ)`. -/
theorem analyticOrderAt_comp_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {m : ℕ} (hm : 0 < m) :
    analyticOrderAt (fun u => f (u ^ m)) 0 = m * analyticOrderAt f 0 := by
  have h0m : (0 : ℂ) ^ m = 0 := zero_pow hm.ne'
  have htend : Filter.Tendsto (fun u : ℂ => u ^ m) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun u : ℂ => u ^ m) (𝓝 0) (𝓝 ((0 : ℂ) ^ m)) :=
      (continuous_pow m).tendsto 0
    rwa [h0m] at h
  have hpm : AnalyticAt ℂ (fun u : ℂ => u ^ m) 0 := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow m
  have hfm : AnalyticAt ℂ (fun u => f (u ^ m)) 0 :=
    AnalyticAt.comp (g := f) (f := fun u : ℂ => u ^ m)
      (by show AnalyticAt ℂ f ((0 : ℂ) ^ m); rw [h0m]; exact hf) hpm
  rcases eq_or_ne (analyticOrderAt f 0) ⊤ with htop | hfin
  · rw [htop, ENat.mul_top (by exact_mod_cast hm.ne')]
    rw [analyticOrderAt_eq_top] at htop ⊢
    exact htend.eventually htop
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f 0 = (n : ℕ∞) := ⟨_, (ENat.coe_toNat hfin).symm⟩
    obtain ⟨g, hgan, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hn
    rw [hn, ← Nat.cast_mul]
    refine hfm.analyticOrderAt_eq_natCast.mpr ⟨fun u => g (u ^ m), ?_, ?_, ?_⟩
    · exact AnalyticAt.comp (g := g) (f := fun u : ℂ => u ^ m)
        (by show AnalyticAt ℂ g ((0 : ℂ) ^ m); rw [h0m]; exact hgan) hpm
    · simpa [h0m] using hg0
    · filter_upwards [htend.eventually hfac] with u hu
      simp only [sub_zero] at hu ⊢
      rw [hu, ← pow_mul]

/-- **Unit scaling preserves the order.** For `f` analytic at `0` and `a ≠ 0`, the order of
`u ↦ f(a·u)` at `0` equals the order of `f` at `0`. (The branches `φ(z, ζⁱu)` therefore all share the
order `m₁ = ord_u φ(z,·)` — the key input to Lemma 4.2.8.) -/
theorem analyticOrderAt_comp_smul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun u => f (a * u)) 0 = analyticOrderAt f 0 := by
  have htend : Filter.Tendsto (fun u : ℂ => a * u) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun u : ℂ => a * u) (𝓝 0) (𝓝 (a * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rwa [mul_zero] at h
  have hsm : AnalyticAt ℂ (fun u : ℂ => a * u) 0 := analyticAt_const.mul analyticAt_id
  have hfa : AnalyticAt ℂ (fun u => f (a * u)) 0 :=
    AnalyticAt.comp (g := f) (f := fun u : ℂ => a * u)
      (by show AnalyticAt ℂ f (a * 0); rw [mul_zero]; exact hf) hsm
  rcases eq_or_ne (analyticOrderAt f 0) ⊤ with htop | hfin
  · rw [htop, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at htop
    exact htend.eventually htop
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f 0 = (n : ℕ∞) := ⟨_, (ENat.coe_toNat hfin).symm⟩
    obtain ⟨g, hgan, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hn
    rw [hn]
    refine hfa.analyticOrderAt_eq_natCast.mpr ⟨fun u => a ^ n * g (a * u), ?_, ?_, ?_⟩
    · exact analyticAt_const.mul (AnalyticAt.comp (g := g) (f := fun u : ℂ => a * u)
        (by show AnalyticAt ℂ g (a * 0); rw [mul_zero]; exact hgan) hsm)
    · simpa [mul_zero] using mul_ne_zero (pow_ne_zero n ha) hg0
    · filter_upwards [htend.eventually hfac] with u hu
      simp only [sub_zero] at hu ⊢
      rw [hu, mul_pow, smul_eq_mul, smul_eq_mul]; ring

/-- **Reindexing the discriminant product over an injective root family.** If `r : Fin m → ℂ` is
injective, the multiset double-product `∏_{x∈image}∏_{s∈image∖x}(x-s)` from `discr_eq_prod_roots`
equals the indexed double-product `∏ᵢ ∏_{j≠i} (rᵢ - rⱼ)`. -/
theorem prod_roots_erase_eq_prod_fin {m : ℕ} {r : Fin m → ℂ} (hr : Function.Injective r) :
    ((Finset.univ.val.map r).map
        (fun x => (((Finset.univ.val.map r).erase x).map (fun s => x - s)).prod)).prod
      = ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
  classical
  rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [← Multiset.map_erase r hr, Multiset.map_map, ← Finset.erase_val,
    ← Finset.prod_eq_multiset_prod]
  rfl

/-- If `a k ≤ b k` (finite) for all `k` and `∑ a = ∑ b`, then `a k = b k` for each `k`. The
"sum-constancy forces termwise constancy" step of Lemma 4.2.7. -/
theorem enat_eq_of_le_of_sum_eq {κ : Type*} [Fintype κ] {a b : κ → ℕ∞}
    (hle : ∀ k, a k ≤ b k) (hb : ∀ k, b k ≠ ⊤) (hsum : ∑ k, a k = ∑ k, b k) (k : κ) :
    a k = b k := by
  have ha : ∀ j, a j ≠ ⊤ := fun j => (lt_of_le_of_lt (hle j) (hb j).lt_top).ne
  have hac : ∀ j, ((a j).toNat : ℕ∞) = a j := fun j => ENat.coe_toNat (ha j)
  have hbc : ∀ j, ((b j).toNat : ℕ∞) = b j := fun j => ENat.coe_toNat (hb j)
  have hle' : ∀ j, (a j).toNat ≤ (b j).toNat := fun j => by
    rw [← Nat.cast_le (α := ℕ∞), hac, hbc]; exact hle j
  have hsum' : ∑ j, (a j).toNat = ∑ j, (b j).toNat := by
    have h : (↑(∑ j, (a j).toNat) : ℕ∞) = ↑(∑ j, (b j).toNat) := by
      rw [Nat.cast_sum, Nat.cast_sum]; simp only [hac, hbc]; exact hsum
    exact_mod_cast h
  by_contra hne
  have hlt : (a k).toNat < (b k).toNat :=
    lt_of_le_of_ne (hle' k) (fun h => hne (by rw [← hac, ← hbc, h]))
  exact absurd hsum' (ne_of_lt
    (Finset.sum_lt_sum (fun j _ => hle' j) ⟨k, Finset.mem_univ k, hlt⟩))

/-- **Lemma 4.2.7 core (abstract constancy of branch-difference orders).** Given a finite family of
"branch differences" `η k : (Fin n → ℂ) → ℂ → ℂ`, each jointly continuous off `u = 0` and per-slice
analytic on a common disc, with the **sum** of their orders constant near `z₀` (this is the
discriminant relation `ord disc = Σ O(η_{ij})` together with `hdisc`), and each order finite at `z₀`,
then **each** order is individually constant near `z₀`. Engine `analyticOrderAt_le_eventually` gives
`≤` termwise; the constant sum upgrades `≤` to `=`. -/
theorem branch_order_constant {n : ℕ} {κ : Type*} [Fintype κ]
    {η : κ → (Fin n → ℂ) → ℂ → ℂ} {z₀ : Fin n → ℂ} {S : Set (Fin n → ℂ)} {T : Set ℂ}
    (hS : S ∈ 𝓝 z₀) {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hT : ∀ θ : ℝ, circleMap 0 ρ θ ∈ T)
    (hcont : ∀ k, ContinuousOn (Function.uncurry (η k)) (S ×ˢ T))
    (hana : ∀ k, ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ (η k z) (Metric.ball 0 R))
    (hfin : ∀ k, analyticOrderAt (η k z₀) 0 ≠ ⊤)
    (hsumconst : ∀ᶠ z in 𝓝 z₀,
      ∑ k, analyticOrderAt (η k z) 0 = ∑ k, analyticOrderAt (η k z₀) 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ k, analyticOrderAt (η k z) 0 = analyticOrderAt (η k z₀) 0 := by
  have hk : ∀ k, ∀ᶠ z in 𝓝 z₀,
      analyticOrderAt (η k z) 0 ≤ analyticOrderAt (η k z₀) 0 := by
    intro k
    have hKeq : analyticOrderAt (η k z₀) 0 = (((analyticOrderAt (η k z₀) 0).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat (hfin k)).symm
    have h := analyticOrderAt_le_eventually_local hρ hρR hT hS (hcont k) (hana k) hKeq
    rwa [← hKeq] at h
  filter_upwards [Filter.eventually_all.mpr hk, hsumconst] with z hzle hzsum
  exact fun k => enat_eq_of_le_of_sum_eq hzle hfin hzsum k

open Polynomial in
/-- **Discriminant of the Weierstrass family as a product of branch-differences.** At a separable
point `u ≠ 0`, the discriminant of `q(cons(uᵐ, z))` equals `±∏ᵢ ∏_{j≠i} (φ(z,ζⁱu) − φ(z,ζʲu))` — the
concrete instantiation of `discr_eq_prod_roots` + `prod_roots_erase_eq_prod_fin`, using that the roots
are exactly the (distinct) Puiseux branches `φ(z,ζⁱu)` (parametrization iff + `pow_eq_pow_iff_branch`,
distinctness from separability). -/
theorem weierstrass_disc_eq_prod_branches {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z : Fin n → ℂ} {u : ℂ} (hz : ‖z‖ < δz) (hu : 0 < ‖u‖) (hud : ‖u‖ ^ m < Real.exp c)
    (hsepu : (q (Fin.cons (u ^ m) z)).Separable) :
    (q (Fin.cons (u ^ m) z)).discr
      = (-1) ^ (m * (m - 1) / 2)
        * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) := by
  classical
  set p := q (Fin.cons (u ^ m) z) with hp
  set r : Fin m → ℂ := fun i => φ (z, ζ ^ (i : ℕ) * u) with hr
  have hpne : p ≠ 0 := (hmonic _).ne_zero
  have hpm : p.natDegree = m := hdeg _
  have hpdeg : 0 < p.natDegree := by rw [hpm]; exact hm
  have hmem : ∀ x, x ∈ p.roots ↔ ∃ i : Fin m, r i = x := by
    intro x
    rw [mem_roots hpne, IsRoot.def, hiff z u x hz hu hud]
    constructor
    · rintro ⟨u', hu'm, hu'φ⟩
      obtain ⟨i, hi⟩ := (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mp hu'm
      exact ⟨i, by show φ (z, ζ ^ (i : ℕ) * u) = x; rw [← hi]; exact hu'φ⟩
    · rintro ⟨i, hi⟩
      exact ⟨ζ ^ (i : ℕ) * u, (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mpr ⟨i, rfl⟩, hi⟩
  have hrootcard : p.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsepu),
      (splits_iff_card_roots.mp (IsAlgClosed.splits p)), hpm]
  have himg : Finset.image r Finset.univ = p.roots.toFinset := by
    ext x
    rw [Finset.mem_image, Multiset.mem_toFinset, hmem x]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩⟩
  have hrinj : Function.Injective r := by
    rw [← Set.injOn_univ, ← Finset.coe_univ]
    refine Finset.injOn_of_card_image_eq ?_
    rw [himg, hrootcard, Finset.card_univ, Fintype.card_fin]
  have hroots : p.roots = Finset.univ.val.map r := by
    refine (Multiset.Nodup.ext (nodup_roots hsepu) (Finset.univ.nodup.map hrinj)).mpr ?_
    intro x
    rw [hmem x, Multiset.mem_map]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ_val i, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [discr_eq_prod_roots (hmonic _) hpdeg, hroots, prod_roots_erase_eq_prod_fin hrinj, hpm]

open Polynomial in
/-- **The Weierstrass family factors over its Puiseux branches.** At a separable `u ≠ 0` in the
parametrization domain, `q(cons(uᵐ,z)) = ∏ᵢ (X − φ(z,ζⁱu))` — the monic polynomial splits as the
product over its (distinct) branch roots. This applies Vieta (`Splits.eq_prod_roots_of_monic`) to the
root enumeration of `weierstrass_disc_eq_prod_branches`, and turns coefficient orders of `q` into
symmetric-function orders of the branches (Lemma 4.2.8 step (ii)). -/
theorem q_comp_eq_prod_branches {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} {u : ℂ}
    (hz : ‖z‖ < δz) (hu : 0 < ‖u‖) (hud : ‖u‖ ^ m < Real.exp c)
    (hsepu : (q (Fin.cons (u ^ m) z)).Separable) :
    q (Fin.cons (u ^ m) z) = ∏ i : Fin m, (X - C (φ (z, ζ ^ (i : ℕ) * u))) := by
  classical
  set p := q (Fin.cons (u ^ m) z) with hp
  set r : Fin m → ℂ := fun i => φ (z, ζ ^ (i : ℕ) * u) with hr
  have hpne : p ≠ 0 := (hmonic _).ne_zero
  have hpm : p.natDegree = m := hdeg _
  have hmem : ∀ x, x ∈ p.roots ↔ ∃ i : Fin m, r i = x := by
    intro x
    rw [mem_roots hpne, IsRoot.def, hiff z u x hz hu hud]
    constructor
    · rintro ⟨u', hu'm, hu'φ⟩
      obtain ⟨i, hi⟩ := (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mp hu'm
      exact ⟨i, by show φ (z, ζ ^ (i : ℕ) * u) = x; rw [← hi]; exact hu'φ⟩
    · rintro ⟨i, hi⟩
      exact ⟨ζ ^ (i : ℕ) * u, (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mpr ⟨i, rfl⟩, hi⟩
  have hrootcard : p.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsepu),
      (splits_iff_card_roots.mp (IsAlgClosed.splits p)), hpm]
  have himg : Finset.image r Finset.univ = p.roots.toFinset := by
    ext x
    rw [Finset.mem_image, Multiset.mem_toFinset, hmem x]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩⟩
  have hrinj : Function.Injective r := by
    rw [← Set.injOn_univ, ← Finset.coe_univ]
    refine Finset.injOn_of_card_image_eq ?_
    rw [himg, hrootcard, Finset.card_univ, Fintype.card_fin]
  have hroots : p.roots = Finset.univ.val.map r := by
    refine (Multiset.Nodup.ext (nodup_roots hsepu) (Finset.univ.nodup.map hrinj)).mpr ?_
    intro x
    rw [hmem x, Multiset.mem_map]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ_val i, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic (hmonic _), hroots, Multiset.map_map,
    Finset.prod_eq_multiset_prod]
  rfl

open Polynomial in
/-- **Phase 1 core — the Weierstrass family factors over its branches along a *ramified line*.**
For a line direction `v` in the `y`-space with `v 0 = ccᵐ` (`cc` a chosen `m`-th root of the
transverse component), the argument `cons 0 z' + sᵐ·v` coincides with `cons((cc·s)ᵐ, z' + sᵐ·tail v)`,
so `q_comp_eq_prod_branches` applies with section `z' + sᵐ·tail v` and parameter `cc·s`. This is the
key unlock for Lemma 4.2.8's lower bound: substituting `t = sᵐ` along a line turns the (otherwise
fractional) branches into honest analytic functions of `s`, namely `φ(z' + sᵐ·tail v, ζⁱ·cc·s)`. -/
theorem q_ramified_line_eq_prod {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} {v : Fin (n + 1) → ℂ} {cc s : ℂ}
    (hcc : cc ^ m = v 0)
    (hu : 0 < ‖cc * s‖) (hz : ‖z' + s ^ m • Fin.tail v‖ < δz)
    (hud : ‖cc * s‖ ^ m < Real.exp c)
    (hsep : (q (Fin.cons 0 z' + s ^ m • v)).Separable) :
    q (Fin.cons 0 z' + s ^ m • v)
      = ∏ i : Fin m, (X - C (φ (z' + s ^ m • Fin.tail v, ζ ^ (i : ℕ) * (cc * s)))) := by
  have hcons : (Fin.cons 0 z' + s ^ m • v : Fin (n + 1) → ℂ)
      = Fin.cons ((cc * s) ^ m) (z' + s ^ m • Fin.tail v) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Pi.add_apply, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_pow, hcc]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, Fin.cons_succ, smul_eq_mul, Fin.tail]
  rw [hcons]
  exact q_comp_eq_prod_branches hm hmonic hdeg hiff hζ hz hu hud (hcons ▸ hsep)

/-- **Order of a finite product is the sum of orders** (1-variable analytic functions). -/
theorem analyticOrderAt_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) :
    (∀ i ∈ s, AnalyticAt ℂ (f i) 0) →
      analyticOrderAt (fun u => ∏ i ∈ s, f i u) 0 = ∑ i ∈ s, analyticOrderAt (f i) 0 := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp [analyticOrderAt_eq_zero]
  | @insert a s ha ih =>
    intro hf
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, AnalyticAt ℂ (f i) 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprodan : AnalyticAt ℂ (fun u => ∏ i ∈ s, f i u) 0 := Finset.analyticAt_fun_prod s hfs
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [show (fun u => f a u * ∏ i ∈ s, f i u) = (f a) * (fun u => ∏ i ∈ s, f i u) from rfl,
      analyticOrderAt_mul hfa hprodan, ih hfs]

/-- **Order of a finite sum is at least the minimum of the orders** (1-variable). If every summand
vanishes to order `≥ N`, so does the sum. -/
theorem le_analyticOrderAt_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {N : ℕ∞}
    (hN : ∀ i ∈ s, N ≤ analyticOrderAt (f i) 0) :
    N ≤ analyticOrderAt (fun u => ∑ i ∈ s, f i u) 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_of_le_of_eq le_top
      (analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => rfl)).symm
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine le_trans (le_min (hN a (Finset.mem_insert_self a s))
      (ih (fun i hi => hN i (Finset.mem_insert_of_mem hi)))) ?_
    exact le_analyticOrderAt_add (f := f a) (g := fun u => ∑ i ∈ s, f i u)

open Polynomial in
/-- **Coefficients of `∏(X − C(βᵢ u))` are analytic in `u`.** Each coefficient is a polynomial
expression in the analytic functions `βᵢ`, established by induction peeling one linear factor
(`(X − C c)·Q` shifts/scales `Q`'s coefficients). -/
theorem analyticAt_coeff_prod_X_sub_C {ι : Type*} {β : ι → ℂ → ℂ}
    (hβ : ∀ i, AnalyticAt ℂ (β i) 0) (s : Finset ι) (k : ℕ) :
    AnalyticAt ℂ (fun u => (∏ i ∈ s, (X - C (β i u))).coeff k) 0 := by
  classical
  induction s using Finset.induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact analyticAt_const
  | @insert a s ha ih =>
    have heq : (fun u => (∏ i ∈ insert a s, (X - C (β i u))).coeff k)
        = fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff k
          - β a u * (∏ i ∈ s, (X - C (β i u))).coeff k := by
      funext u
      rw [Finset.prod_insert ha, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rw [heq]
    cases k with
    | zero =>
      have h0 : (fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff 0
            - β a u * (∏ i ∈ s, (X - C (β i u))).coeff 0)
          = fun u => (0 : ℂ) - β a u * (∏ i ∈ s, (X - C (β i u))).coeff 0 := by
        funext u
        rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
      rw [h0]
      exact analyticAt_const.sub ((hβ a).mul (ih 0))
    | succ l =>
      have hl : (fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff (l + 1)
            - β a u * (∏ i ∈ s, (X - C (β i u))).coeff (l + 1))
          = fun u => (∏ i ∈ s, (X - C (β i u))).coeff l
            - β a u * (∏ i ∈ s, (X - C (β i u))).coeff (l + 1) := by
        funext u; rw [Polynomial.coeff_X_mul]
      rw [hl]
      exact (ih l).sub ((hβ a).mul (ih (l + 1)))

open Polynomial in
/-- **Symmetric-function order bound.** If each `βᵢ` vanishes to order `≥ N` at `0`, then the
coefficient of `X^{|s|−k}` in `∏_{i∈s}(X − C(βᵢ u))` (i.e. `±` the `(|s|−k)`-th elementary symmetric
function of the `βᵢ`) vanishes to order `≥ (|s|−k)·N`. This is step (ii) of Lemma 4.2.8: with
`βᵢ = ζⁱ·`-branches (`N = m₁`), it bounds `ord_u` of the Weierstrass coefficients by `(m−k)·m₁`. -/
theorem analyticOrderAt_coeff_prod_X_sub_C {ι : Type*} {β : ι → ℂ → ℂ} {N : ℕ}
    (hβ : ∀ i, AnalyticAt ℂ (β i) 0) (hβord : ∀ i, (N : ℕ∞) ≤ analyticOrderAt (β i) 0)
    (s : Finset ι) (k : ℕ) :
    (((s.card - k) * N : ℕ) : ℕ∞)
      ≤ analyticOrderAt (fun u => (∏ i ∈ s, (X - C (β i u))).coeff k) 0 := by
  classical
  induction s using Finset.induction generalizing k with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    have heq : (fun u => (∏ i ∈ insert a s, (X - C (β i u))).coeff k)
        = fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff k
          - β a u * (∏ i ∈ s, (X - C (β i u))).coeff k := by
      funext u
      rw [Finset.prod_insert ha, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rw [heq]
    have hcoeffan : AnalyticAt ℂ (fun u => (∏ i ∈ s, (X - C (β i u))).coeff k) 0 :=
      analyticAt_coeff_prod_X_sub_C hβ s k
    have hterm1 : (((s.card + 1 - k) * N : ℕ) : ℕ∞)
        ≤ analyticOrderAt (fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff k) 0 := by
      cases k with
      | zero =>
        have h0 : (fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff 0) = fun _ => (0 : ℂ) := by
          funext u; rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
        rw [h0, analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => rfl)]
        exact le_top
      | succ l =>
        have hl : (fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff (l + 1))
            = fun u => (∏ i ∈ s, (X - C (β i u))).coeff l := by
          funext u; rw [Polynomial.coeff_X_mul]
        rw [hl, show s.card + 1 - (l + 1) = s.card - l from by omega]
        exact ih l
    have hterm2 : (((s.card + 1 - k) * N : ℕ) : ℕ∞)
        ≤ analyticOrderAt (fun u => β a u * (∏ i ∈ s, (X - C (β i u))).coeff k) 0 := by
      have hmul : analyticOrderAt (fun u => β a u * (∏ i ∈ s, (X - C (β i u))).coeff k) 0
          = analyticOrderAt (β a) 0
            + analyticOrderAt (fun u => (∏ i ∈ s, (X - C (β i u))).coeff k) 0 :=
        analyticOrderAt_mul (hβ a) hcoeffan
      rw [hmul]
      have hnat : (s.card + 1 - k) * N ≤ N + (s.card - k) * N := by
        have h1 : s.card + 1 - k ≤ (s.card - k) + 1 := by omega
        calc (s.card + 1 - k) * N ≤ ((s.card - k) + 1) * N := mul_le_mul_right' h1 N
          _ = N + (s.card - k) * N := by ring
      refine le_trans ?_ (add_le_add (hβord a) (ih k))
      rw [← Nat.cast_add]
      exact_mod_cast hnat
    exact le_trans (le_min hterm1 hterm2)
      (le_analyticOrderAt_sub (f := fun u => (X * ∏ i ∈ s, (X - C (β i u))).coeff k)
        (g := fun u => β a u * (∏ i ∈ s, (X - C (β i u))).coeff k))

open Polynomial in
/-- **Phase 3 — per-direction ramified coefficient bound (assembly).** Given the ramified coefficient
identity (extended across `s = 0` by the identity theorem, bundling Phase 1) and analytic branches
`βᵢ(s)` of order `≥ N` (Phase 2), the line restriction `t ↦ (q(cons 0 z' + t·v)).coeff k` satisfies
`(m−k)·N ≤ m·ord_t`. Combines `analyticOrderAt_comp_pow` (ramify `t = sᵐ`),
`analyticOrderAt_coeff_prod_X_sub_C` (symmetric-function bound), and `analyticOrderAt_congr`. -/
theorem coeff_ramified_line_order_ge {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} {z' : Fin n → ℂ} {v : Fin (n + 1) → ℂ}
    {β : Fin m → ℂ → ℂ} {N k : ℕ}
    (hlinean : AnalyticAt ℂ (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) 0)
    (hcomp : (fun s : ℂ => (q (Fin.cons 0 z' + s ^ m • v)).coeff k)
        =ᶠ[𝓝 (0 : ℂ)] fun s => (∏ i : Fin m, (X - C (β i s))).coeff k)
    (hβan : ∀ i, AnalyticAt ℂ (β i) 0) (hβord : ∀ i, (N : ℕ∞) ≤ analyticOrderAt (β i) 0) :
    ((m - k) * N : ℕ)
      ≤ m * analyticOrderAt (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) 0 := by
  have hpow := analyticOrderAt_comp_pow hlinean hm
  rw [show (fun u : ℂ => (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) (u ^ m))
      = (fun s : ℂ => (q (Fin.cons 0 z' + s ^ m • v)).coeff k) from rfl,
    analyticOrderAt_congr hcomp] at hpow
  have hesymm := analyticOrderAt_coeff_prod_X_sub_C hβan hβord Finset.univ k
  rw [Finset.card_univ, Fintype.card_fin, hpow] at hesymm
  exact hesymm

/-! ### Step A — branches: per-slice analytic extension, continuity, and finiteness -/

open Polynomial in
/-- **Per-slice removable singularity.** For a Weierstrass family `q` and its Puiseux
parametrization `φ` (root + slice-analyticity hypotheses), each slice `w ↦ φ(z, w)` (`‖z‖ < δz`)
is bounded near `0` (its values are roots of `q(cons(wᵐ, z))`, bounded by the Cauchy bound) and
analytic on the punctured disc, hence extends to a function `F` analytic *at* `0`. -/
theorem exists_phi_slice_extend {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z : Fin n → ℂ} (hz : ‖z‖ < δz) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F =ᶠ[𝓝[≠] (0 : ℂ)] (fun w => φ (z, w)) := by
  -- the punctured region near `0`
  have hexp : (0 : ℝ) < Real.exp c := Real.exp_pos c
  have hlt : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖w‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun w : ℂ => ‖w‖ ^ m) 0 :=
      (continuous_norm.pow m).continuousAt
    have h0 : (fun w : ℂ => ‖w‖ ^ m) 0 < Real.exp c := by simpa [zero_pow hm.ne'] using hexp
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ w in 𝓝[≠] (0 : ℂ), (0 : ℝ) < ‖w‖ := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_pos_iff.mpr hw
  -- slice analyticity off `0`
  have hf : ∀ᶠ w in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun w => φ (z, w)) w := by
    filter_upwards [hlt, hpos] with w hw1 hw2
    exact AnalyticAt.comp (g := φ) (f := fun w => (z, w))
      (han z w hz hw2 hw1) (analyticAt_const.prod analyticAt_id)
  -- boundedness via the Cauchy root bound near `0`
  have hcons : Continuous (fun w : ℂ => (Fin.cons (w ^ m) z : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using continuous_pow m
    · simpa using continuous_const
  obtain ⟨ε, _, hεbd⟩ := roots_bound_eventually (fun w : ℂ => q (Fin.cons (w ^ m) z)) m 0
    (fun w => hmonic _) (fun w => hdeg _)
    (fun i => (Continuous.comp (hcoeff i) hcons).continuousAt)
  have hb : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖(fun w => φ (z, w)) w‖ ≤ ε := by
    filter_upwards [hlt, hpos, hεbd.filter_mono nhdsWithin_le_nhds] with w hw1 hw2 hwbd
    refine hwbd (φ (z, w)) ?_
    rw [Multiset.mem_toFinset, mem_roots (hmonic _).ne_zero]
    exact hroot z w hz hw2 hw1
  exact exists_analyticAt_extend_of_bdd hf hb

open Polynomial in
/-- **Phase 1-remainder — removable singularity along a ramified curve.** Generalises
`exists_phi_slice_extend` from a fixed slice to the curve `s ↦ (z' + sᵐ·w', a·s)` (`a ≠ 0`): the
branch `s ↦ φ(z' + sᵐ·w', a·s)` is analytic off `0` (composition with the analytic curve) and bounded
near `0` (its values are roots of `q(cons((a·s)ᵐ, z' + sᵐ·w'))`, bounded by the Cauchy root bound),
hence extends to a function `F` analytic *at* `0`. This produces the analytic branches `βᵢ(s)` (and,
via the identity theorem, the `hcomp` coefficient identity) feeding `coeff_ramified_line_order_ge`. -/
theorem exists_phi_curve_extend {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z' w' : Fin n → ℂ} (hz' : ‖z'‖ < δz) {a : ℂ} (ha : a ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      F =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => φ (z' + s ^ m • w', a * s)) := by
  have hexp : (0 : ℝ) < Real.exp c := Real.exp_pos c
  -- region conditions near `s = 0`
  have hz_ev : ∀ᶠ s in 𝓝 (0 : ℂ), ‖z' + s ^ m • w'‖ < δz := by
    have hc : ContinuousAt (fun s : ℂ => ‖z' + s ^ m • w'‖) 0 := by fun_prop
    have h0 : (fun s : ℂ => ‖z' + s ^ m • w'‖) 0 < δz := by
      simpa [zero_pow hm.ne'] using hz'
    exact hc.eventually_lt continuousAt_const h0
  have hpos : ∀ᶠ s in 𝓝[≠] (0 : ℂ), 0 < ‖a * s‖ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact norm_pos_iff.mpr (mul_ne_zero ha (Set.mem_compl_singleton_iff.mp hs))
  have hlt : ∀ᶠ s in 𝓝 (0 : ℂ), ‖a * s‖ ^ m < Real.exp c := by
    have hc : ContinuousAt (fun s : ℂ => ‖a * s‖ ^ m) 0 := by fun_prop
    have h0 : (fun s : ℂ => ‖a * s‖ ^ m) 0 < Real.exp c := by
      simpa [zero_pow hm.ne'] using hexp
    exact hc.eventually_lt continuousAt_const h0
  -- analyticity off `0`
  have hf : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      AnalyticAt ℂ (fun s => φ (z' + s ^ m • w', a * s)) s := by
    filter_upwards [hz_ev.filter_mono nhdsWithin_le_nhds, hpos,
      hlt.filter_mono nhdsWithin_le_nhds] with s hsz hspos hslt
    refine AnalyticAt.comp (g := φ) (f := fun s => (z' + s ^ m • w', a * s))
      (han _ _ hsz hspos hslt) ?_
    exact (analyticAt_const.add ((analyticAt_id.pow m).smul analyticAt_const)).prod
      (analyticAt_const.mul analyticAt_id)
  -- boundedness via the Cauchy root bound near `0`
  have hcons : Continuous
      (fun s : ℂ => (Fin.cons ((a * s) ^ m) (z' + s ^ m • w') : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using (continuous_const.mul continuous_id).pow m
    · simpa using continuous_const.add (continuous_pow m |>.smul continuous_const)
  obtain ⟨ε, _, hεbd⟩ :=
    roots_bound_eventually (fun s : ℂ => q (Fin.cons ((a * s) ^ m) (z' + s ^ m • w'))) m 0
      (fun s => hmonic _) (fun s => hdeg _)
      (fun i => (Continuous.comp (hcoeff i) hcons).continuousAt)
  have hb : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖(fun s => φ (z' + s ^ m • w', a * s)) s‖ ≤ ε := by
    filter_upwards [hz_ev.filter_mono nhdsWithin_le_nhds, hpos,
      hlt.filter_mono nhdsWithin_le_nhds, hεbd.filter_mono nhdsWithin_le_nhds]
      with s hsz hspos hslt hsbd
    refine hsbd (φ (z' + s ^ m • w', a * s)) ?_
    rw [Multiset.mem_toFinset, mem_roots (hmonic _).ne_zero]
    exact hroot _ _ hsz hspos hslt
  exact exists_analyticAt_extend_of_bdd hf hb

/-- **Phase 2 decomposition — branch order from the frozen branch and the `z`-perturbation.** The
ramified branch `F` (`= φ̃(z'+sᵐ·tail v, a·s)`) splits as the *frozen branch* `s ↦ G(a·s)` (with `G`
the per-slice extension `φ̃(z',·)`, whose order is `M` and is preserved under `s ↦ a·s` by
`analyticOrderAt_comp_smul`) plus the *`z`-perturbation* `F − G(a·s)`. If the perturbation vanishes to
order `≥ mm` (it is `O(sᵐ)` because the section moves by `sᵐ`), then `ord F ≥ min(M, mm)` via
`le_analyticOrderAt_add`. This isolates the remaining kernel (Part B) as the hypothesis `hpert`. -/
theorem branch_order_ge {F G : ℂ → ℂ} (hGan : AnalyticAt ℂ G 0) {a : ℂ} (ha : a ≠ 0) {M mm : ℕ}
    (hGord : (M : ℕ∞) ≤ analyticOrderAt G 0)
    (hpert : (mm : ℕ∞) ≤ analyticOrderAt (fun s => F s - G (a * s)) 0) :
    (min M mm : ℕ∞) ≤ analyticOrderAt F 0 := by
  have hFeq : F = (fun s => G (a * s)) + (fun s => F s - G (a * s)) := by
    funext s; simp
  rw [hFeq]
  refine le_trans (le_min ?_ ?_) le_analyticOrderAt_add
  · rw [analyticOrderAt_comp_smul hGan ha]
    exact le_trans (min_le_left _ _) hGord
  · exact le_trans (min_le_right _ _) hpert

open Metric in
/-- **Cauchy–Lipschitz at the centre.** A function differentiable on `ball 0 R` and bounded by `M`
there is Lipschitz near `0`: for `‖σ‖ ≤ R/4`, `‖g σ − g 0‖ ≤ (2M/R)·‖σ‖`. The derivative is bounded by
`2M/R` on `closedBall 0 (R/4)` by the Cauchy estimate (`norm_deriv_le_of_forall_mem_sphere_norm_le` on
`ball x (R/2)`), then the convex mean-value inequality applies. This is the analytic core of the
`z`-perturbation Lipschitz bound (Phase 2, Part B). -/
theorem norm_sub_zero_le_of_bounded_diffOn {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbd : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ M)
    {σ : ℂ} (hσ : ‖σ‖ ≤ R / 4) :
    ‖g σ - g 0‖ ≤ 2 * M / R * ‖σ‖ := by
  have hbound : ∀ x ∈ closedBall (0 : ℂ) (R / 4), ‖fderiv ℂ g x‖ ≤ 2 * M / R := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    have hsub : closedBall x (R / 2) ⊆ ball (0 : ℂ) R := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball, dist_zero_right]
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ R / 2 + R / 4 := add_le_add hz hx
        _ < R := by linarith
    have hdcc : DiffContOnCl ℂ g (ball x (R / 2)) := by
      refine ⟨hg.mono (subset_trans ball_subset_closedBall hsub), ?_⟩
      rw [closure_ball x (by positivity : (R / 2 : ℝ) ≠ 0)]
      exact (hg.mono hsub).continuousOn
    have hsph : ∀ z ∈ sphere x (R / 2), ‖g z‖ ≤ M := fun z hz =>
      hbd z (hsub (sphere_subset_closedBall hz))
    have hd : ‖deriv g x‖ ≤ M / (R / 2) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hdcc hsph
    rw [← norm_deriv_eq_norm_fderiv]
    calc ‖deriv g x‖ ≤ M / (R / 2) := hd
      _ = 2 * M / R := by rw [div_div_eq_mul_div]; ring
  have hdiff : ∀ x ∈ closedBall (0 : ℂ) (R / 4), DifferentiableAt ℂ g x := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    exact hg.differentiableAt
      (isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; linarith))
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) (R / 4) := mem_closedBall_self (by positivity)
  have hσs : σ ∈ closedBall (0 : ℂ) (R / 4) := by rw [mem_closedBall, dist_zero_right]; exact hσ
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall _ _) h0 hσs
  rwa [sub_zero] at hmvt

open Metric Polynomial in
/-- **Phase 2, Part B — the `z`-perturbation Lipschitz bound.** Along the ramified curve, the root
function's section-variation is `O(sᵐ)`: `‖φ(z'+sᵐ·w', a·s) − φ(z', a·s)‖ ≤ C·‖s‖ᵐ` near `0`. For each
small `s`, `g_s(σ) := φ(z'+σ·w', a·s)` is differentiable on a fixed ball `ball 0 R` (from `han`) and
bounded by `ε` there (uniform root bound via the two-variable `roots_bound_eventually` over `(σ,s)`),
so the Cauchy–Lipschitz core (`norm_sub_zero_le_of_bounded_diffOn`) at `σ = sᵐ` gives the bound. This
feeds `analyticOrderAt_ge_of_bigO` ⟹ the Phase 2 perturbation hypothesis. -/
theorem phi_curve_lipschitz {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z' w' : Fin n → ℂ} (hz' : ‖z'‖ < δz) {a : ℂ} (ha : a ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      ‖φ (z' + s ^ m • w', a * s) - φ (z', a * s)‖ ≤ C * ‖s‖ ^ m := by
  -- the section-curve argument as a continuous family over `(σ, s)`
  have hcons : Continuous
      (fun p : ℂ × ℂ => (Fin.cons ((a * p.2) ^ m) (z' + p.1 • w') : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]
      exact (continuous_const.mul continuous_snd).pow m
    · simp only [Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact continuous_const.add (continuous_fst.mul continuous_const)
  -- uniform root bound near `(0,0)`
  obtain ⟨ε, hε0, hεbd⟩ :=
    roots_bound_eventually (fun p : ℂ × ℂ => q (Fin.cons ((a * p.2) ^ m) (z' + p.1 • w'))) m (0, 0)
      (fun p => hmonic _) (fun p => hdeg _)
      (fun i => (Continuous.comp (hcoeff i) hcons).continuousAt)
  rw [Metric.eventually_nhds_iff] at hεbd
  obtain ⟨δ, hδ0, hδ⟩ := hεbd
  -- the working radius
  have hwpos : (0 : ℝ) < ‖w'‖ + 1 := by positivity
  set R₂ : ℝ := (δz - ‖z'‖) / (‖w'‖ + 1) with hR₂def
  have hR₂pos : 0 < R₂ := div_pos (by linarith) hwpos
  set R : ℝ := min R₂ (δ / 2) with hRdef
  have hRpos : 0 < R := lt_min hR₂pos (by linarith)
  -- on `ball 0 R`, the section argument stays in the domain (`‖z'+σ•w'‖ < δz`)
  have hzbd : ∀ σ : ℂ, ‖σ‖ < R → ‖z' + σ • w'‖ < δz := by
    intro σ hσ
    have hσR₂ : ‖σ‖ < R₂ := lt_of_lt_of_le hσ (min_le_left _ _)
    have hcancel : R₂ * (‖w'‖ + 1) = δz - ‖z'‖ := div_mul_cancel₀ _ (ne_of_gt hwpos)
    have h2 : ‖σ‖ * (‖w'‖ + 1) < δz - ‖z'‖ := by
      rw [← hcancel]; exact mul_lt_mul_of_pos_right hσR₂ hwpos
    calc ‖z' + σ • w'‖ ≤ ‖z'‖ + ‖σ • w'‖ := norm_add_le _ _
      _ = ‖z'‖ + ‖σ‖ * ‖w'‖ := by rw [norm_smul]
      _ ≤ ‖z'‖ + ‖σ‖ * (‖w'‖ + 1) := by nlinarith [norm_nonneg σ]
      _ < δz := by linarith
  refine ⟨2 * ε / R, ?_⟩
  -- conditions on `s`: nonzero, small enough that `aₛ`-conditions hold and `‖sᵐ‖ ≤ R/4`
  have hsmall : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      0 < ‖a * s‖ ∧ ‖a * s‖ ^ m < Real.exp c ∧ ‖s‖ < δ ∧ ‖s ^ m‖ ≤ R / 4 := by
    have hc1 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), 0 < ‖a * s‖ := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact norm_pos_iff.mpr (mul_ne_zero ha (Set.mem_compl_singleton_iff.mp hs))
    have hc2 : ∀ᶠ s in 𝓝 (0 : ℂ), ‖a * s‖ ^ m < Real.exp c := by
      have hcont : ContinuousAt (fun s : ℂ => ‖a * s‖ ^ m) 0 := by fun_prop
      exact hcont.eventually_lt continuousAt_const (by simpa [zero_pow hm.ne'] using Real.exp_pos c)
    have hc3 : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < δ := by
      have hcont : ContinuousAt (fun s : ℂ => ‖s‖) 0 := by fun_prop
      exact hcont.eventually_lt continuousAt_const (by simpa using hδ0)
    have hc4 : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s ^ m‖ ≤ R / 4 := by
      have hcont : ContinuousAt (fun s : ℂ => ‖s ^ m‖) 0 := by fun_prop
      have h0 : (fun s : ℂ => ‖s ^ m‖) 0 < R / 4 := by
        simpa [zero_pow hm.ne'] using (by positivity : (0 : ℝ) < R / 4)
      exact (hcont.eventually_lt continuousAt_const h0).mono (fun s h => le_of_lt h)
    filter_upwards [hc1, hc2.filter_mono nhdsWithin_le_nhds, hc3.filter_mono nhdsWithin_le_nhds,
      hc4.filter_mono nhdsWithin_le_nhds] with s h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  filter_upwards [hsmall] with s ⟨hu, hud, hsδ, hsm⟩
  -- `g_s` is differentiable on `ball 0 R` and bounded by `ε` there
  set g : ℂ → ℂ := fun σ => φ (z' + σ • w', a * s) with hgdef
  have hgdiff : DifferentiableOn ℂ g (ball 0 R) := by
    intro σ hσ
    rw [mem_ball, dist_zero_right] at hσ
    have hanσ : AnalyticAt ℂ g σ := by
      refine AnalyticAt.comp (g := φ) (f := fun σ => (z' + σ • w', a * s))
        (han _ _ (hzbd σ hσ) hu hud) ?_
      exact (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).prod analyticAt_const
    exact hanσ.differentiableAt.differentiableWithinAt
  have hgbd : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ ε := by
    intro σ hσ
    rw [mem_ball, dist_zero_right] at hσ
    have hdist : dist ((σ, s) : ℂ × ℂ) (0, 0) < δ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, max_lt_iff]
      exact ⟨lt_trans (lt_of_lt_of_le hσ (min_le_right _ _)) (by linarith), hsδ⟩
    refine hδ hdist (g σ) ?_
    rw [Multiset.mem_toFinset, mem_roots (hmonic _).ne_zero]
    exact hroot _ _ (hzbd σ hσ) hu hud
  -- Cauchy–Lipschitz at `σ = sᵐ`
  have hkey := norm_sub_zero_le_of_bounded_diffOn hRpos hgdiff hgbd (σ := s ^ m) hsm
  simp only [hgdef, zero_smul, add_zero, norm_pow] at hkey
  exact hkey

/-- **Phase 2 ingredient — `O(sᵐ)` forces vanishing order `≥ m`.** If `D` is analytic at `0` and
`‖D s‖ ≤ C·‖s‖ᵐ` near `0`, then `m ≤ ord_s D`. The quotient `D s / sᵐ` is analytic off `0` and bounded,
so it extends analytically (`exists_analyticAt_extend_of_bdd`); thus `D =ᶠ sᵐ·K̃` with `K̃` analytic, and
`ord D = m + ord K̃ ≥ m`. This is the buildable half of the `z`-perturbation bound (Part B). -/
theorem analyticOrderAt_ge_of_bigO {D : ℂ → ℂ} (hDan : AnalyticAt ℂ D 0) {m : ℕ} {C : ℝ}
    (hbd : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖D s‖ ≤ C * ‖s‖ ^ m) :
    (m : ℕ∞) ≤ analyticOrderAt D 0 := by
  have hsman : AnalyticAt ℂ (fun s : ℂ => s ^ m) 0 := analyticAt_id.pow m
  have hsm_ord : analyticOrderAt (fun s : ℂ => s ^ m) 0 = (m : ℕ∞) := by
    refine hsman.analyticOrderAt_eq_natCast.mpr
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with s; simp
  -- the quotient `K = D / sᵐ` is analytic off `0` and bounded near `0`
  have hf : ∀ᶠ s in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun s => D s / s ^ m) s := by
    filter_upwards [hDan.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hDs hs
    exact hDs.div (analyticAt_id.pow m) (pow_ne_zero m (Set.mem_compl_singleton_iff.mp hs))
  have hb : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖(fun s => D s / s ^ m) s‖ ≤ C := by
    filter_upwards [hbd, self_mem_nhdsWithin] with s hsbd hs
    have hspos : (0 : ℝ) < ‖s‖ ^ m :=
      pow_pos (norm_pos_iff.mpr (Set.mem_compl_singleton_iff.mp hs)) m
    rw [norm_div, norm_pow, div_le_iff₀ hspos]
    exact hsbd
  obtain ⟨K, hKan, hKeq⟩ := exists_analyticAt_extend_of_bdd hf hb
  -- `D =ᶠ sᵐ·K` on a full neighbourhood, by the identity theorem
  have hDeq : D =ᶠ[𝓝 (0 : ℂ)] fun s => s ^ m * K s := by
    have hoff : D =ᶠ[𝓝[≠] (0 : ℂ)] fun s => s ^ m * K s := by
      filter_upwards [hKeq, self_mem_nhdsWithin] with s hKs hs
      rw [hKs, mul_div_cancel₀ _ (pow_ne_zero m (Set.mem_compl_singleton_iff.mp hs))]
    have hRHSan : AnalyticAt ℂ (fun s : ℂ => s ^ m * K s) 0 := hsman.mul hKan
    exact (hDan.frequently_eq_iff_eventually_eq hRHSan).mp hoff.frequently
  have key : analyticOrderAt (fun s : ℂ => s ^ m * K s) 0 = (m : ℕ∞) + analyticOrderAt K 0 := by
    rw [show (fun s : ℂ => s ^ m * K s) = (fun s : ℂ => s ^ m) * K from rfl,
      analyticOrderAt_mul hsman hKan, hsm_ord]
  rw [analyticOrderAt_congr hDeq, key]
  exact le_self_add

open Polynomial in
/-- **Phase 1-remainder (completion) — the analytic ramified branches and the `hcomp` identity.**
Packages the per-branch curve extensions `βᵢ = Fᵢ` (`exists_phi_curve_extend` at `a = ζⁱ·cc`) with the
ramified factorisation (`q_ramified_line_eq_prod`) and the identity theorem into exactly the inputs
`coeff_ramified_line_order_ge` consumes: the branches are analytic at `0`, agree with `φ` off `0`, and
the ramified coefficient agrees with `(∏(X − C βᵢ)).coeff k` on a *full* neighbourhood of `0`. Only the
branch-order bound `N ≤ ord_s βᵢ` (Phase 2) remains to obtain the per-direction order bound. -/
theorem exists_ramified_branches {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} {v : Fin (n + 1) → ℂ} {cc : ℂ}
    (hcc : cc ^ m = v 0) (hcc0 : cc ≠ 0) (hz' : ‖z'‖ < δz) (k : ℕ)
    (hana_pt : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (Fin.cons 0 z'))
    (hsep : ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable) :
    ∃ β : Fin m → ℂ → ℂ, (∀ i, AnalyticAt ℂ (β i) 0) ∧
      (∀ i, β i =ᶠ[𝓝[≠] (0 : ℂ)]
        fun s => φ (z' + s ^ m • Fin.tail v, ζ ^ (i : ℕ) * (cc * s))) ∧
      (fun s : ℂ => (q (Fin.cons 0 z' + s ^ m • v)).coeff k)
        =ᶠ[𝓝 (0 : ℂ)] fun s => (∏ i : Fin m, (X - C (β i s))).coeff k := by
  classical
  have hζ0 : ζ ≠ 0 := by
    have : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hm.ne'
    rw [← norm_pos_iff, this]; norm_num
  have hbr : ∀ i : Fin m, ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      F =ᶠ[𝓝[≠] (0 : ℂ)] fun s => φ (z' + s ^ m • Fin.tail v, (ζ ^ (i : ℕ) * cc) * s) :=
    fun i => exists_phi_curve_extend hm hmonic hdeg hcoeff hroot han (w' := Fin.tail v) hz'
      (a := ζ ^ (i : ℕ) * cc) (mul_ne_zero (pow_ne_zero _ hζ0) hcc0)
  choose F hFan hFeq using hbr
  refine ⟨F, hFan, ?_, ?_⟩
  · intro i
    filter_upwards [hFeq i] with s hs
    rw [hs, mul_assoc]
  · have hz_ev : ∀ᶠ s in 𝓝 (0 : ℂ), ‖z' + s ^ m • Fin.tail v‖ < δz := by
      have hcc' : ContinuousAt (fun s : ℂ => ‖z' + s ^ m • Fin.tail v‖) 0 := by fun_prop
      have h0 : (fun s : ℂ => ‖z' + s ^ m • Fin.tail v‖) 0 < δz := by
        simpa [zero_pow hm.ne'] using hz'
      exact hcc'.eventually_lt continuousAt_const h0
    have hpos : ∀ᶠ s in 𝓝[≠] (0 : ℂ), 0 < ‖cc * s‖ := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact norm_pos_iff.mpr (mul_ne_zero hcc0 (Set.mem_compl_singleton_iff.mp hs))
    have hlt : ∀ᶠ s in 𝓝 (0 : ℂ), ‖cc * s‖ ^ m < Real.exp c := by
      have hcc' : ContinuousAt (fun s : ℂ => ‖cc * s‖ ^ m) 0 := by fun_prop
      have h0 : (fun s : ℂ => ‖cc * s‖ ^ m) 0 < Real.exp c := by
        simpa [zero_pow hm.ne'] using Real.exp_pos c
      exact hcc'.eventually_lt continuousAt_const h0
    have hall : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
        ∀ i : Fin m, F i s = φ (z' + s ^ m • Fin.tail v, (ζ ^ (i : ℕ) * cc) * s) :=
      Filter.eventually_all.mpr hFeq
    have hoff : (fun s : ℂ => (q (Fin.cons 0 z' + s ^ m • v)).coeff k)
        =ᶠ[𝓝[≠] (0 : ℂ)] fun s => (∏ i : Fin m, (X - C (F i s))).coeff k := by
      filter_upwards [hsep, hz_ev.filter_mono nhdsWithin_le_nhds, hpos,
        hlt.filter_mono nhdsWithin_le_nhds, hall] with s hssep hsz hspos hslt hsall
      rw [q_ramified_line_eq_prod hm hmonic hdeg hiff hζ hcc hspos hsz hslt hssep]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hsall i, mul_assoc]
    have hLHSan : AnalyticAt ℂ (fun s : ℂ => (q (Fin.cons 0 z' + s ^ m • v)).coeff k) 0 := by
      have hcurve : AnalyticAt ℂ (fun s : ℂ => (Fin.cons 0 z' + s ^ m • v : Fin (n + 1) → ℂ)) 0 :=
        analyticAt_const.add ((analyticAt_id.pow m).smul analyticAt_const)
      have hpt : AnalyticAt ℂ (fun y => (q y).coeff k)
          ((fun s : ℂ => Fin.cons 0 z' + s ^ m • v) 0) := by
        simp only [zero_pow hm.ne', zero_smul, add_zero]; exact hana_pt k
      exact AnalyticAt.comp (g := fun y => (q y).coeff k)
        (f := fun s : ℂ => Fin.cons 0 z' + s ^ m • v) hpt hcurve
    have hRHSan : AnalyticAt ℂ (fun s : ℂ => (∏ i : Fin m, (X - C (F i s))).coeff k) 0 :=
      analyticAt_coeff_prod_X_sub_C hFan Finset.univ k
    exact (hLHSan.frequently_eq_iff_eventually_eq hRHSan).mp hoff.frequently

/-- Multiplication by a nonzero constant maps the punctured neighbourhood of `0` to itself. -/
theorem tendsto_const_mul_punctured {s : ℂ} (hs : s ≠ 0) :
    Filter.Tendsto (fun u : ℂ => s * u) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Filter.Tendsto (fun u : ℂ => s * u) (𝓝 (0 : ℂ)) (𝓝 (s * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero hs (Set.mem_compl_singleton_iff.mp hu))

/-- **Phase 2 (complete) — the ramified branch order bound.** For a curve branch `F =ᶠ φ(z'+sᵐ·w', a·s)`
and the frozen slice extension `G =ᶠ φ(z',·)` (order `≥ M`), `ord_s F ≥ min(M, m)`. The `z`-perturbation
`F − G(a·s)` is `O(sᵐ)` (`phi_curve_lipschitz`), hence vanishes to order `≥ m`
(`analyticOrderAt_ge_of_bigO`); `branch_order_ge` then combines with the frozen order `M`. This produces
the `hβord` input for `coeff_ramified_line_order_ge`. -/
theorem curve_branch_order_ge {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z' w' : Fin n → ℂ} (hz' : ‖z'‖ < δz) {a : ℂ} (ha : a ≠ 0)
    {F G : ℂ → ℂ} (hFan : AnalyticAt ℂ F 0)
    (hFeq : F =ᶠ[𝓝[≠] (0 : ℂ)] fun s => φ (z' + s ^ m • w', a * s))
    (hGan : AnalyticAt ℂ G 0) (hGeq : G =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w))
    {M : ℕ} (hM : (M : ℕ∞) ≤ analyticOrderAt G 0) :
    (min M m : ℕ∞) ≤ analyticOrderAt F 0 := by
  obtain ⟨C, hlip⟩ := phi_curve_lipschitz hm hmonic hdeg hcoeff hroot han (w' := w') hz' ha
  have hgas_an : AnalyticAt ℂ (fun s => G (a * s)) 0 :=
    AnalyticAt.comp (g := G) (f := fun s => a * s) (by simpa using hGan)
      (analyticAt_const.mul analyticAt_id)
  have hG_as : (fun s => G (a * s)) =ᶠ[𝓝[≠] (0 : ℂ)] fun s => φ (z', a * s) :=
    (tendsto_const_mul_punctured ha).eventually hGeq
  have hbound : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖F s - G (a * s)‖ ≤ C * ‖s‖ ^ m := by
    filter_upwards [hFeq, hG_as, hlip] with s hF hG hl
    rw [hF, hG]; exact hl
  exact branch_order_ge hGan ha hM (analyticOrderAt_ge_of_bigO (hFan.sub hgas_an) hbound)

/-- **Phase 4 (per-direction) — the line coefficient order bound.** For a direction `v` with
`v 0 = ccᵐ`, the line `t ↦ (q(cons 0 z' + t·v)).coeff k` satisfies `(m−k)·min(M,m) ≤ m·ord_t`. Combines
the analytic ramified branches (`exists_ramified_branches`), their order bound (`curve_branch_order_ge`
per branch, with the shared frozen slice order `M`), and the symmetric-function/ramification bound
(`coeff_ramified_line_order_ge`). This is the per-direction input to `le_order_of_forall_line`. -/
theorem coeff_line_order_ge {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} {v : Fin (n + 1) → ℂ} {cc : ℂ}
    (hcc : cc ^ m = v 0) (hcc0 : cc ≠ 0) (hz' : ‖z'‖ < δz) (k : ℕ)
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G 0) (hGeq : G =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w))
    {M : ℕ} (hM : (M : ℕ∞) ≤ analyticOrderAt G 0)
    (hana_pt : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (Fin.cons 0 z'))
    (hlinean : AnalyticAt ℂ (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) 0)
    (hsep : ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable) :
    ((m - k) * min M m : ℕ)
      ≤ m * analyticOrderAt (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) 0 := by
  have hζ0 : ζ ≠ 0 := by
    have : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hm.ne'
    rw [← norm_pos_iff, this]; norm_num
  obtain ⟨β, hβan, hβeq, hcomp⟩ :=
    exists_ramified_branches hm hmonic hdeg hcoeff hroot han hiff hζ hcc hcc0 hz' k hana_pt hsep
  have hβord : ∀ i : Fin m, ((min M m : ℕ) : ℕ∞) ≤ analyticOrderAt (β i) 0 := by
    intro i
    have hFeq_i : β i =ᶠ[𝓝[≠] (0 : ℂ)]
        fun s => φ (z' + s ^ m • Fin.tail v, (ζ ^ (i : ℕ) * cc) * s) := by
      filter_upwards [hβeq i] with s h; rw [h, mul_assoc]
    refine le_trans (le_min ?_ ?_) (curve_branch_order_ge hm hmonic hdeg hcoeff hroot han hz'
      (mul_ne_zero (pow_ne_zero _ hζ0) hcc0) (hβan i) hFeq_i hGan hGeq hM)
    · exact_mod_cast min_le_left M m
    · exact_mod_cast min_le_right M m
  exact coeff_ramified_line_order_ge (N := min M m) hm hlinean hcomp hβan hβord

/-- **Branch-difference is analytic on a full disc.** For two unit-modulus constants `a, b`, the
slice `u ↦ φ(z, a·u) − φ(z, b·u)` is analytic on `ball 0 R` (`Rᵐ < exp c`): away from `0` directly
from the slice-analyticity of `φ`, at `0` by the removable singularity (`exists_phi_slice_extend`)
since both branches share the limit of the extension `F` (so the difference vanishes at `0`). -/
theorem branchDiff_slice_analyticOnNhd {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {z : Fin n → ℂ} (hz : ‖z‖ < δz) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {R : ℝ} (hRc : R ^ m < Real.exp c) :
    AnalyticOnNhd ℂ (fun u => φ (z, a * u) - φ (z, b * u)) (Metric.ball 0 R) := by
  have ha0 : a ≠ 0 := by rw [← norm_pos_iff, ha]; norm_num
  have hb0 : b ≠ 0 := by rw [← norm_pos_iff, hb]; norm_num
  intro u₀ hu₀
  rw [Metric.mem_ball, dist_zero_right] at hu₀
  rcases eq_or_ne u₀ 0 with rfl | hu₀ne
  · -- at `0`: use the analytic extension of the slice
    obtain ⟨F, hFan, hFeq⟩ := exists_phi_slice_extend hm hmonic hdeg hcoeff hroot han hz
    have hHan : AnalyticAt ℂ (fun u => F (a * u) - F (b * u)) 0 := by
      have h1 : AnalyticAt ℂ (fun u => F (a * u)) 0 :=
        AnalyticAt.comp (g := F) (f := fun u => a * u)
          (by simpa using hFan) (analyticAt_const.mul analyticAt_id)
      have h2 : AnalyticAt ℂ (fun u => F (b * u)) 0 :=
        AnalyticAt.comp (g := F) (f := fun u => b * u)
          (by simpa using hFan) (analyticAt_const.mul analyticAt_id)
      exact h1.sub h2
    have hEqa : ∀ᶠ u in 𝓝[≠] (0 : ℂ), F (a * u) = φ (z, a * u) :=
      (tendsto_const_mul_punctured ha0).eventually hFeq
    have hEqb : ∀ᶠ u in 𝓝[≠] (0 : ℂ), F (b * u) = φ (z, b * u) :=
      (tendsto_const_mul_punctured hb0).eventually hFeq
    have hpunc : (fun u => F (a * u) - F (b * u)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun u => φ (z, a * u) - φ (z, b * u)) := by
      filter_upwards [hEqa, hEqb] with u e1 e2; rw [e1, e2]
    have hval : (fun u => F (a * u) - F (b * u)) 0 = (fun u => φ (z, a * u) - φ (z, b * u)) 0 := by
      simp
    exact hHan.congr (eventuallyEq_nhds_of_nhdsWithin_ne hpunc hval)
  · -- away from `0`: direct slice-analyticity of `φ`
    have hu0n : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
    have hnorm : ∀ s : ℂ, ‖s‖ = 1 → 0 < ‖s * u₀‖ ∧ ‖s * u₀‖ ^ m < Real.exp c := by
      intro s hs
      rw [norm_mul, hs, one_mul]
      exact ⟨hu0n, lt_trans (pow_lt_pow_left₀ hu₀ (norm_nonneg u₀) hm.ne') hRc⟩
    have h1 : AnalyticAt ℂ (fun u => φ (z, a * u)) u₀ :=
      AnalyticAt.comp (g := φ) (f := fun u => (z, a * u))
        (han z (a * u₀) hz (hnorm a ha).1 (hnorm a ha).2)
        (analyticAt_const.prod (analyticAt_const.mul analyticAt_id))
    have h2 : AnalyticAt ℂ (fun u => φ (z, b * u)) u₀ :=
      AnalyticAt.comp (g := φ) (f := fun u => (z, b * u))
        (han z (b * u₀) hz (hnorm b hb).1 (hnorm b hb).2)
        (analyticAt_const.prod (analyticAt_const.mul analyticAt_id))
    exact h1.sub h2

/-- **Branch-difference is jointly continuous off `u = 0`.** On `S ×ˢ {0 < ‖u‖ ∧ ‖u‖ᵐ < exp c}`
(with `S` inside the parametrization domain `‖z‖ < δz`), the branch difference `φ(z,a·u) − φ(z,b·u)`
is continuous, since `φ` is analytic (hence continuous) at each such point. -/
theorem branchDiff_continuousOn {n m : ℕ} {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {S : Set (Fin n → ℂ)}
    (hSsub : ∀ z ∈ S, ‖z‖ < δz) :
    ContinuousOn (Function.uncurry (fun z u => φ (z, a * u) - φ (z, b * u)))
      (S ×ˢ {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c}) := by
  rintro ⟨z, u⟩ hp
  have hzδ : ‖z‖ < δz := hSsub z hp.1
  have hnorm : ∀ s : ℂ, ‖s‖ = 1 → 0 < ‖s * u‖ ∧ ‖s * u‖ ^ m < Real.exp c := by
    intro s hs; rw [norm_mul, hs, one_mul]; exact ⟨hp.2.1, hp.2.2⟩
  have hfa : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => (p.1, a * p.2)) (z, u) :=
    continuousAt_fst.prodMk (continuousAt_const.mul continuousAt_snd)
  have hfb : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => (p.1, b * p.2)) (z, u) :=
    continuousAt_fst.prodMk (continuousAt_const.mul continuousAt_snd)
  have c1 : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => φ (p.1, a * p.2)) (z, u) :=
    ContinuousAt.comp (g := φ) (f := fun p : (Fin n → ℂ) × ℂ => (p.1, a * p.2)) (x := (z, u))
      (han z (a * u) hzδ (hnorm a ha).1 (hnorm a ha).2).continuousAt hfa
  have c2 : ContinuousAt (fun p : (Fin n → ℂ) × ℂ => φ (p.1, b * p.2)) (z, u) :=
    ContinuousAt.comp (g := φ) (f := fun p : (Fin n → ℂ) × ℂ => (p.1, b * p.2)) (x := (z, u))
      (han z (b * u) hzδ (hnorm b hb).1 (hnorm b hb).2).continuousAt hfb
  exact (c1.sub c2).continuousWithinAt

open Polynomial in
/-- **The Puiseux branches are distinct at a separable point.** At `u ≠ 0` (in the parametrization
domain) where `q(cons(uᵐ, z))` is separable, the map `i ↦ φ(z, ζⁱ·u)` is injective (the `m` branches
enumerate the `m` distinct roots). -/
theorem branches_injective {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} {u : ℂ}
    (hz : ‖z‖ < δz) (hu : 0 < ‖u‖) (hud : ‖u‖ ^ m < Real.exp c)
    (hsepu : (q (Fin.cons (u ^ m) z)).Separable) :
    Function.Injective (fun i : Fin m => φ (z, ζ ^ (i : ℕ) * u)) := by
  classical
  set p := q (Fin.cons (u ^ m) z) with hp
  set r : Fin m → ℂ := fun i => φ (z, ζ ^ (i : ℕ) * u) with hr
  have hpne : p ≠ 0 := (hmonic _).ne_zero
  have hpm : p.natDegree = m := hdeg _
  have hmem : ∀ x, x ∈ p.roots ↔ ∃ i : Fin m, r i = x := by
    intro x
    rw [mem_roots hpne, IsRoot.def, hiff z u x hz hu hud]
    constructor
    · rintro ⟨u', hu'm, hu'φ⟩
      obtain ⟨i, hi⟩ := (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mp hu'm
      exact ⟨i, by show φ (z, ζ ^ (i : ℕ) * u) = x; rw [← hi]; exact hu'φ⟩
    · rintro ⟨i, hi⟩
      exact ⟨ζ ^ (i : ℕ) * u, (pow_eq_pow_iff_branch hm hζ (norm_pos_iff.mp hu)).mpr ⟨i, rfl⟩, hi⟩
  have hrootcard : p.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsepu),
      (splits_iff_card_roots.mp (IsAlgClosed.splits p)), hpm]
  have himg : Finset.image r Finset.univ = p.roots.toFinset := by
    ext x
    rw [Finset.mem_image, Multiset.mem_toFinset, hmem x]
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩⟩
  rw [← Set.injOn_univ, ← Finset.coe_univ]
  refine Finset.injOn_of_card_image_eq ?_
  rw [himg, hrootcard, Finset.card_univ, Fintype.card_fin]

/-- **Branch-difference has finite order at `0`.** For `i ≠ j`, the difference `φ(z,ζⁱ·) − φ(z,ζʲ·)`
does not vanish identically near `0` (the branches are distinct off `0` by separability), so its
analytic order at `0` is finite. -/
theorem branchDiff_order_ne_top {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    (hsep_punc : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {i j : Fin m} (hij : i ≠ j) :
    analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  -- region near `0`
  have hreg : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖u‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun u : ℂ => ‖u‖ ^ m) 0 := (continuous_norm.pow m).continuousAt
    have h0 : (fun u : ℂ => ‖u‖ ^ m) 0 < Real.exp c := by
      simpa [zero_pow hm.ne'] using Real.exp_pos c
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  have hcontra : ∀ᶠ u in 𝓝[≠] (0 : ℂ), False := by
    filter_upwards [htop.filter_mono nhdsWithin_le_nhds, hsep_punc, hreg,
      self_mem_nhdsWithin] with u hu0 hsepu hudu huneq
    have hune : u ≠ 0 := huneq
    have hu : 0 < ‖u‖ := norm_pos_iff.mpr hune
    have hinj := branches_injective hm hmonic hdeg hiff hζ hz hu hudu hsepu
    exact hij (hinj (by simpa using sub_eq_zero.mp hu0))
  exact (NeBot.ne (by infer_instance) (Filter.eventually_false_iff_eq_bot.mp hcontra))

open Polynomial in
/-- **Lemma 4.2.8, step (b) — ramification.** The order in `u` of the coefficient
`u ↦ (q(cons(uᵐ,z))).coeff k` is `m` times the order in the transverse coordinate `w` of
`w ↦ (q(cons(w,z))).coeff k` at `w = 0` (substituting `w = uᵐ`). Immediate from
`analyticOrderAt_comp_pow`. -/
theorem coeff_order_ramified {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    {z : Fin n → ℂ} (k : ℕ)
    (hg : AnalyticAt ℂ (fun w => (q (Fin.cons w z)).coeff k) 0) :
    analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z)).coeff k) 0
      = m * analyticOrderAt (fun w => (q (Fin.cons w z)).coeff k) 0 :=
  analyticOrderAt_comp_pow hg hm

open Polynomial in
/-- **Lemma 4.2.8, step (c) — the constant-term order is exactly `m·m₁`.** The constant term
`a_m = (q(cons(uᵐ,z))).coeff 0 = (-1)ᵐ ∏ᵢ βᵢ` (Vieta), so its order in `u` is *exactly*
`Σᵢ ord βᵢ = m·m₁` (`analyticOrderAt_prod`; the `±1` is a unit). With ramification this gives
`t_m = m₁` exactly — the order achieved at `j = m`, the minimum in Case II of Lemma 4.2.8. -/
theorem coeff_zero_order_eq {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F 0) (hFeq : F =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z, w))
    (hLHSan0 : AnalyticAt ℂ (fun u => (q (Fin.cons (u ^ m) z)).coeff 0) 0)
    (hsep : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable) :
    analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z)).coeff 0) 0 = m * analyticOrderAt F 0 := by
  classical
  have hζ0 : ζ ≠ 0 := by
    have : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hm.ne'
    rw [← norm_pos_iff, this]; norm_num
  set β : Fin m → ℂ → ℂ := fun i u => F (ζ ^ (i : ℕ) * u) with hβdef
  have hβan : ∀ i, AnalyticAt ℂ (β i) 0 := fun i =>
    AnalyticAt.comp (g := F) (f := fun u => ζ ^ (i : ℕ) * u) (by simpa using hFan)
      (analyticAt_const.mul analyticAt_id)
  have hreg : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖u‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun u : ℂ => ‖u‖ ^ m) 0 := (continuous_norm.pow m).continuousAt
    have h0 : (fun u : ℂ => ‖u‖ ^ m) 0 < Real.exp c := by
      simpa [zero_pow hm.ne'] using Real.exp_pos c
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ∀ i : Fin m, β i u = φ (z, ζ ^ (i : ℕ) * u) :=
    Filter.eventually_all.mpr fun i =>
      (tendsto_const_mul_punctured (pow_ne_zero (i : ℕ) hζ0)).eventually hFeq
  -- the constant term equals `(-1)ᵐ ∏ βᵢ` off `0`
  have heq : (fun u => (q (Fin.cons (u ^ m) z)).coeff 0)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun u => (-1 : ℂ) ^ m * ∏ i : Fin m, β i u := by
    filter_upwards [hsep, hreg, self_mem_nhdsWithin, hall] with u husep hureg huneq huall
    have hune : u ≠ 0 := huneq
    rw [q_comp_eq_prod_branches hm hmonic hdeg hiff hζ hz (norm_pos_iff.mpr hune) hureg husep,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    have hfac : ∀ i : Fin m,
        ((X - C (φ (z, ζ ^ (i : ℕ) * u))) : ℂ[X]).eval 0 = -β i u := fun i => by
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
      rw [huall i]
    rw [Finset.prod_congr rfl (fun i _ => hfac i),
      show (fun i : Fin m => -β i u) = (fun i => (-1 : ℂ) * β i u) from
        funext (fun i => (neg_one_mul _).symm),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hRHSan : AnalyticAt ℂ (fun u => (-1 : ℂ) ^ m * ∏ i : Fin m, β i u) 0 :=
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => hβan i))
  have hfull := (hLHSan0.frequently_eq_iff_eventually_eq hRHSan).mp heq.frequently
  rw [analyticOrderAt_congr hfull,
    show (fun u => (-1 : ℂ) ^ m * ∏ i : Fin m, β i u)
      = (fun _ => (-1 : ℂ) ^ m) * (fun u => ∏ i : Fin m, β i u) from rfl,
    analyticOrderAt_mul analyticAt_const (Finset.analyticAt_fun_prod _ (fun i _ => hβan i)),
    analyticAt_const.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ (by norm_num)), zero_add,
    analyticOrderAt_prod Finset.univ β (fun i _ => hβan i)]
  have hβord : ∀ i, analyticOrderAt (β i) 0 = analyticOrderAt F 0 := fun i => by
    rw [hβdef, analyticOrderAt_comp_smul hFan (pow_ne_zero _ hζ0)]
  rw [Finset.sum_congr rfl (fun i _ => hβord i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-! ### Step (d) infrastructure — multivariate order via line restrictions -/

/-- **The multivariate order is bounded by every line-restriction order.** For `f` analytic at `x₀`
and any direction `w`, `order ℂ f x₀ ≤ analyticOrderAt (t ↦ f(x₀ + t·w)) 0`. (If `f` vanishes to
multivariate order `≥ N`, all its iterated Fréchet derivatives of degree `< N` vanish, so the
line-restriction's Taylor coefficients of degree `< N` vanish too.) This gives the *upper bound* side
of Lemma 4.2.8 (`ord h ≤ m` via the `x`-axis line, `≤ m₁` via the transverse line), sidestepping the
general Newton-polygon no-cancellation. -/
theorem order_le_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x₀ w : E) (hf : AnalyticAt ℂ f x₀) :
    order ℂ f x₀ ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 := by
  have hline : AnalyticAt ℂ (fun t : ℂ => f (x₀ + t • w)) 0 :=
    analyticAt_line_restriction f x₀ w hf
  have hkey : ∀ N : ℕ, (N : ℕ∞) ≤ order ℂ f x₀ →
      (N : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 := by
    intro N hN
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hline]
    intro k hk
    rw [iteratedDeriv_line_eq_iteratedFDeriv_diag f x₀ w k hf,
      iteratedFDeriv_eq_zero_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk) hN)]
    rfl
  rcases eq_or_ne (order ℂ f x₀) ⊤ with htop | hfin
  · rw [htop, top_le_iff]
    by_contra hne
    obtain ⟨M, hM⟩ : ∃ M : ℕ, analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0 = (M : ℕ∞) :=
      ⟨_, (ENat.coe_toNat hne).symm⟩
    have hcontra := hkey (M + 1) (by rw [htop]; exact le_top)
    rw [hM] at hcontra
    exact absurd (by exact_mod_cast hcontra : M + 1 ≤ M) (by omega)
  · obtain ⟨N, hNeq⟩ : ∃ N : ℕ, order ℂ f x₀ = (N : ℕ∞) := ⟨_, (ENat.coe_toNat hfin).symm⟩
    rw [hNeq]; exact hkey N (by rw [hNeq])

/-- **The multivariate order is at least `V` iff every line restriction has order `≥ V`** (lower-bound
direction). If every line `t ↦ f(x₀ + t·w)` vanishes to order `≥ V`, then `f` vanishes to multivariate
order `≥ V`. (For `k < V`, every diagonal value `(iteratedFDeriv k f x₀)(w,…,w) = iteratedDeriv k(line)
0 = 0`; by polarization a symmetric multilinear map with zero diagonal is zero.) This is the dual of
`order_le_line` — the tool for the *lower* bound in Lemma 4.2.8. -/
theorem le_order_of_forall_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x₀ : E} (hf : AnalyticAt ℂ f x₀) {V : ℕ}
    (h : ∀ w : E, (V : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => f (x₀ + t • w)) 0) :
    (V : ℕ∞) ≤ order ℂ f x₀ := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨K, hKeq⟩ : ∃ K : ℕ, order ℂ f x₀ = (K : ℕ∞) :=
    ⟨_, (ENat.coe_toNat (ne_top_of_lt hlt)).symm⟩
  have hK_lt : K < V := by rw [hKeq] at hlt; exact_mod_cast hlt
  refine absurd (order_eq_natCast_iff.mp hKeq).2 ?_
  push_neg
  refine symmetric_multilinear_eq_zero_of_diagonal_zero _
    (fun v σ => hf.contDiffAt.iteratedFDeriv_comp_perm v σ) ?_
  intro w
  rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag f x₀ w K hf]
  have hline := h w
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (analyticAt_line_restriction f x₀ w hf)] at hline
  exact hline K hK_lt

/-- **Order of a multivariate sum is at least the minimum of the orders.** If every summand vanishes
to multivariate order `≥ V`, so does the sum. (The easy direction of the Newton polygon: via line
restrictions, `analyticOrderAt(Σ lines) ≥ min` reduces to the 1-variable
`le_analyticOrderAt_finset_sum`.) -/
theorem le_order_finset_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} {x₀ : E} {V : ℕ}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) x₀) (hV : ∀ i ∈ s, (V : ℕ∞) ≤ order ℂ (f i) x₀) :
    (V : ℕ∞) ≤ order ℂ (fun y => ∑ i ∈ s, f i y) x₀ := by
  refine le_order_of_forall_line (Finset.analyticAt_fun_sum s hf) (fun w => ?_)
  exact le_analyticOrderAt_finset_sum s (fun i hi =>
    le_trans (hV i hi) (order_le_line (f i) x₀ w (hf i hi)))

/-- **Newton-polygon arithmetic.** With `N ≤ m`, the floor `⌊(m−k)·N/m⌋ + k ≥ N`. The `k = m` term
`xᵐ` contributes `m`, the `k = 0` term contributes `N`, intermediate terms stay `≥ N`. -/
theorem nat_newton {N k m : ℕ} (hN : N ≤ m) : N ≤ (m - k) * N / m + k := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact le_trans (show N ≤ 0 by omega) (Nat.zero_le _)
  · have h1 : N - k ≤ (m - k) * N / m := by
      rw [Nat.le_div_iff_mul_le hmpos, Nat.sub_mul, Nat.sub_mul, Nat.mul_comm N m]
      exact Nat.sub_le_sub_left (by gcongr) _
    exact le_trans (by omega) (Nat.add_le_add_right h1 k)

/-- Cancellation of a positive natural multiplier in `ℕ∞`. -/
theorem enat_le_of_mul_le_mul_left {m : ℕ} (hm : 0 < m) {a b : ℕ∞}
    (h : (m : ℕ∞) * a ≤ (m : ℕ∞) * b) : a ≤ b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · exact le_top
  · lift b to ℕ using hb with b'
    rcases eq_or_ne a ⊤ with rfl | ha
    · rw [ENat.mul_top (by exact_mod_cast hm.ne' : (m : ℕ∞) ≠ 0), ← Nat.cast_mul] at h
      exact absurd h (ENat.coe_lt_top _).not_ge
    · lift a to ℕ using ha with a'
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le] at h
      exact_mod_cast Nat.le_of_mul_le_mul_left h hm

/-- **Order of the monomial `x^k` in a product space.** `order ℂ (fun yx => yx.2 ^ k) (p, 0) ≥ k`:
every line restriction `t ↦ (t·w.2)^k` vanishes to order `≥ k`. The Phase 5 term `aₖ·xᵏ` inherits the
`+k` from this. -/
theorem order_snd_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (p : E) (k : ℕ) :
    (k : ℕ∞) ≤ order ℂ (fun yx : E × ℂ => yx.2 ^ k) (p, 0) := by
  have hsndpow : AnalyticAt ℂ (fun yx : E × ℂ => yx.2 ^ k) (p, 0) := analyticAt_snd.pow k
  refine le_order_of_forall_line hsndpow (fun w => ?_)
  have hline : (fun t : ℂ => (fun yx : E × ℂ => yx.2 ^ k) ((p, 0) + t • w))
      = fun t : ℂ => (t * w.2) ^ k := by
    funext t; simp [Prod.snd_add, Prod.smul_snd]
  rw [hline]
  have hsman : AnalyticAt ℂ (fun t : ℂ => t ^ k) 0 := analyticAt_id.pow k
  have hsm_ord : analyticOrderAt (fun t : ℂ => t ^ k) 0 = (k : ℕ∞) := by
    refine hsman.analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with t; simp
  have heq : analyticOrderAt (fun t : ℂ => (t * w.2) ^ k) 0
      = (k : ℕ∞) + analyticOrderAt (fun _ : ℂ => w.2 ^ k) 0 := by
    rw [show (fun t : ℂ => (t * w.2) ^ k) = (fun t : ℂ => t ^ k) * (fun _ => w.2 ^ k) from by
      funext t; simp [mul_pow], analyticOrderAt_mul hsman analyticAt_const, hsm_ord]
  rw [heq]; exact le_self_add

open Polynomial in
/-- **Phase 5 — the Newton lower bound for `h`.** Writing `h(y,x) = Σₖ (q y).coeff k · xᵏ`, the order of
`h` at `(cons 0 z', 0)` is at least the minimum of the term orders. Each term `(coeff k)·xᵏ` has order
`order(coeffₖ∘fst) + k` (`order_mul_analytic` + `order_snd_pow`), so if `V ≤ order(coeffₖ∘fst) + k` for
all `k ≤ m` then `V ≤ order ℂ h`. -/
theorem order_eval_ge {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hdeg : ∀ y, (q y).natDegree = m) {z' : Fin n → ℂ} {V : ℕ}
    (hcoeff_an : ∀ k, AnalyticAt ℂ
      (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k) (Fin.cons 0 z', 0))
    (hbound : ∀ k ∈ Finset.range (m + 1),
      (V : ℕ∞) ≤ order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k) (Fin.cons 0 z', 0)
        + k) :
    (V : ℕ∞) ≤ order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', 0) := by
  have hh : (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      = fun yx => ∑ k ∈ Finset.range (m + 1), (q yx.1).coeff k * yx.2 ^ k := by
    funext yx
    exact Polynomial.eval_eq_sum_range' (by rw [hdeg]; omega) yx.2
  rw [hh]
  have hsndan : ∀ k : ℕ, AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => yx.2 ^ k)
      (Fin.cons 0 z', 0) := fun k => analyticAt_snd.pow k
  refine le_order_finset_sum (Finset.range (m + 1)) (fun k _ => (hcoeff_an k).mul (hsndan k))
    (fun k hk => ?_)
  rw [order_mul_analytic (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k)
    (fun yx => yx.2 ^ k) (Fin.cons 0 z', 0) (hcoeff_an k) (hsndan k)]
  refine le_trans (hbound k hk) ?_
  gcongr
  exact order_snd_pow (Fin.cons 0 z' : Fin (n + 1) → ℂ) k

open Polynomial in
/-- **Phase 4 — the multivariate coefficient order bound.** Lifting the per-direction bound over all
directions via `le_order_of_forall_line`: `order ℂ (coeffₖ∘fst) (cons 0 z', 0) ≥ ⌊(m−k)·min(M,m)/m⌋`.
Directions with `w 0 ≠ 0` use `coeff_line_order_ge` (with `cc` an `m`-th root of `w 0`, separability
from `hsep`); directions with `w 0 = 0` stay in the central fibre `Xᵐ` (coefficient `0` for `k < m`,
order `0 = ⌊0⌋` for `k = m`). -/
theorem coeff_fst_order_ge {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} (hz' : ‖z'‖ < δz) {k : ℕ} (hk : k ≤ m)
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G 0) (hGeq : G =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w))
    {M : ℕ} (hM : (M : ℕ∞) ≤ analyticOrderAt G 0)
    (hcentral : ∀ᶠ z in 𝓝 z', q (Fin.cons 0 z) = X ^ m)
    (hana_pt : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (Fin.cons 0 z'))
    (hsep : ∀ v : Fin (n + 1) → ℂ, v 0 ≠ 0 →
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable) :
    (((m - k) * min M m / m : ℕ) : ℕ∞)
      ≤ order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k) (Fin.cons 0 z', 0) := by
  have hfan : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k)
      (Fin.cons 0 z', 0) :=
    AnalyticAt.comp (g := fun y => (q y).coeff k) (f := fun yx : (Fin (n + 1) → ℂ) × ℂ => yx.1)
      (hana_pt k) analyticAt_fst
  refine le_order_of_forall_line hfan (fun w => ?_)
  have hline : (fun t : ℂ =>
        (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k) ((Fin.cons 0 z', 0) + t • w))
      = fun t => (q (Fin.cons 0 z' + t • w.1)).coeff k := by
    funext t; simp [Prod.fst_add, Prod.smul_fst]
  rw [hline]
  set v := w.1 with hvdef
  have hlinean : AnalyticAt ℂ (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) 0 := by
    have hcurve : AnalyticAt ℂ (fun t : ℂ => (Fin.cons 0 z' + t • v : Fin (n + 1) → ℂ)) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hpt : AnalyticAt ℂ (fun y => (q y).coeff k)
        ((fun t : ℂ => Fin.cons 0 z' + t • v) 0) := by simpa using hana_pt k
    exact AnalyticAt.comp (g := fun y => (q y).coeff k)
      (f := fun t : ℂ => Fin.cons 0 z' + t • v) hpt hcurve
  rcases eq_or_ne (v 0) 0 with hv0 | hv0
  · have htend : Filter.Tendsto (fun t : ℂ => z' + t • Fin.tail v) (𝓝 0) (𝓝 z') := by
      have hcont : Continuous (fun t : ℂ => z' + t • Fin.tail v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using hcont.tendsto 0
    have hcons_ev : (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k)
        =ᶠ[𝓝 0] fun _ : ℂ => (X ^ m : ℂ[X]).coeff k := by
      filter_upwards [htend.eventually hcentral] with t ht
      have heq : (Fin.cons 0 z' + t • v : Fin (n + 1) → ℂ)
          = Fin.cons 0 (z' + t • Fin.tail v) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [Fin.cons_zero, hv0]
        · simp [Fin.cons_succ, Fin.tail]
      rw [heq, ht]
    rw [analyticOrderAt_congr hcons_ev]
    rcases lt_or_eq_of_le hk with hklt | hkm
    · rw [show (X ^ m : ℂ[X]).coeff k = 0 from by
        rw [Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hklt)],
        analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => rfl)]
      exact le_top
    · rw [show ((m - k) * min M m / m : ℕ) = 0 from by
        have : m - k = 0 := by omega
        rw [this]; simp]
      exact zero_le _
  · obtain ⟨cc, hcc⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) hm
    have hcc0 : cc ≠ 0 := fun h => hv0 (by rw [← hcc, h, zero_pow hm.ne'])
    have hcl := coeff_line_order_ge hm hmonic hdeg hcoeff hroot han hiff hζ hcc hcc0 hz' k
      hGan hGeq hM hana_pt hlinean (hsep v hv0)
    refine enat_le_of_mul_le_mul_left hm ?_
    calc (m : ℕ∞) * (((m - k) * min M m / m : ℕ) : ℕ∞)
        = ((m * ((m - k) * min M m / m) : ℕ) : ℕ∞) := by rw [Nat.cast_mul]
      _ ≤ (((m - k) * min M m : ℕ) : ℕ∞) := by
          rw [Nat.cast_le, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
      _ ≤ (m : ℕ∞) * analyticOrderAt (fun t : ℂ => (q (Fin.cons 0 z' + t • v)).coeff k) 0 := hcl

open Polynomial in
/-- **Lemma 4.2.8, the lower bound `order ℂ h ≥ min(m, M)` (Phases 4+5).** Combines the multivariate
coefficient bound (`coeff_fst_order_ge`) with the Newton sum (`order_eval_ge`) and the Newton
arithmetic (`nat_newton`). `M` is the order of the frozen slice `φ(z',·)`; with the matching upper
bound this pins `order ℂ h (cons 0 z', 0) = min(m, M)` in the centered case (`q(cons 0 z) = Xᵐ`). -/
theorem order_eval_ge_min {n m : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} (hz' : ‖z'‖ < δz)
    {G : ℂ → ℂ} (hGan : AnalyticAt ℂ G 0) (hGeq : G =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w))
    {M : ℕ} (hM : (M : ℕ∞) ≤ analyticOrderAt G 0)
    (hcentral : ∀ᶠ z in 𝓝 z', q (Fin.cons 0 z) = X ^ m)
    (hana_pt : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (Fin.cons 0 z'))
    (hsep : ∀ v : Fin (n + 1) → ℂ, v 0 ≠ 0 →
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable) :
    ((min m M : ℕ) : ℕ∞)
      ≤ order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', 0) := by
  refine order_eval_ge hdeg (fun k => AnalyticAt.comp (g := fun y => (q y).coeff k)
    (f := fun yx : (Fin (n + 1) → ℂ) × ℂ => yx.1) (hana_pt k) analyticAt_fst) (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hVk := coeff_fst_order_ge hm hmonic hdeg hcoeff hroot han hiff hζ hz'
    (show k ≤ m by omega) hGan hGeq hM hcentral hana_pt hsep
  have hnat : min m M ≤ (m - k) * min M m / m + k := by
    have := @nat_newton (min M m) k m (min_le_right M m); omega
  calc ((min m M : ℕ) : ℕ∞) ≤ (((m - k) * min M m / m + k : ℕ) : ℕ∞) := by exact_mod_cast hnat
    _ = (((m - k) * min M m / m : ℕ) : ℕ∞) + (k : ℕ∞) := by push_cast; ring
    _ ≤ order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).coeff k) (Fin.cons 0 z', 0)
          + (k : ℕ∞) := by gcongr

/-- **Local version of `order_eval_translate`.** The ψ-shear identity where `ψfun` need only be
analytic at the base point `cons 0 z'` — not globally `ContDiff` — matching the axiom's section `ψ`,
which is only locally analytic. Order is a local invariant, so `order_comp_eq_of_diffeo_C` applies on
the analyticity neighborhoods of `ψfun` and the evaluation map. -/
theorem order_eval_translate_local {n : ℕ} {q : (Fin (n + 1) → ℂ) → Polynomial ℂ} {z' : Fin n → ℂ}
    {ψfun : (Fin (n + 1) → ℂ) → ℂ} (hψ : AnalyticAt ℂ ψfun (Fin.cons 0 z'))
    (hg_an : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      (Fin.cons 0 z', ψfun (Fin.cons 0 z'))) :
    order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
        (Fin.cons 0 z', ψfun (Fin.cons 0 z'))
      = order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval (yx.2 + ψfun yx.1))
        (Fin.cons 0 z', 0) := by
  set g := fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2 with hgdef
  set Ψ : (Fin (n + 1) → ℂ) × ℂ → (Fin (n + 1) → ℂ) × ℂ :=
    fun yx => (yx.1, yx.2 + ψfun yx.1) with hΨdef
  set Ψ' : (Fin (n + 1) → ℂ) × ℂ → (Fin (n + 1) → ℂ) × ℂ :=
    fun yx => (yx.1, yx.2 - ψfun yx.1) with hΨ'def
  set x : (Fin (n + 1) → ℂ) × ℂ := (Fin.cons 0 z', 0) with hxdef
  obtain ⟨P, hPan, hP_open, hP_mem⟩ := eventually_nhds_iff.mp hψ.eventually_analyticAt
  obtain ⟨t₀, ht₀an, ht₀_open, ht₀_mem⟩ := eventually_nhds_iff.mp hg_an.eventually_analyticAt
  have hψ_on : AnalyticOnNhd ℂ ψfun P := fun y hy => hPan y hy
  have hψ_cdo : ContDiffOn ℂ (⊤ : WithTop ℕ∞) ψfun P := hψ_on.contDiffOn_of_completeSpace
  set t : Set ((Fin (n + 1) → ℂ) × ℂ) := t₀ ∩ (P ×ˢ Set.univ) with htdef
  have hPU_open : IsOpen (P ×ˢ (Set.univ : Set ℂ)) := hP_open.prod isOpen_univ
  have ht_open : IsOpen t := ht₀_open.inter hPU_open
  have ht_sub_P : t ⊆ P ×ˢ Set.univ := Set.inter_subset_right
  have hΨx : Ψ x = (Fin.cons 0 z', ψfun (Fin.cons 0 z')) := by simp [hΨdef, hxdef]
  have ht_mem : Ψ x ∈ t := by rw [hΨx]; exact ⟨ht₀_mem, hP_mem, Set.mem_univ _⟩
  have hΨ_cont : ContinuousOn Ψ (P ×ˢ Set.univ) :=
    continuousOn_fst.prodMk (continuousOn_snd.add
      (hψ_cdo.continuousOn.comp continuousOn_fst (fun yx hyx => hyx.1)))
  set s : Set ((Fin (n + 1) → ℂ) × ℂ) := (P ×ˢ Set.univ) ∩ Ψ ⁻¹' t with hsdef
  have hs_open : IsOpen s := hΨ_cont.isOpen_inter_preimage hPU_open ht_open
  have hx_s : x ∈ s := ⟨⟨hP_mem, Set.mem_univ _⟩, by rw [Set.mem_preimage]; exact ht_mem⟩
  have hg_on : AnalyticOnNhd ℂ g t := fun y hy => ht₀an y hy.1
  have hg_cdo : ContDiffOn ℂ (⊤ : WithTop ℕ∞) g t := hg_on.contDiffOn_of_completeSpace
  have hΨ_cdo : ContDiffOn ℂ (⊤ : WithTop ℕ∞) Ψ s :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add
      (hψ_cdo.comp contDiffOn_fst (fun yx hyx => hyx.1.1)))
  have hΨ'_cdo : ContDiffOn ℂ (⊤ : WithTop ℕ∞) Ψ' t :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sub
      (hψ_cdo.comp contDiffOn_fst (fun yx hyx => (ht_sub_P hyx).1)))
  have hmaps : Set.MapsTo Ψ s t := fun yx hyx => hyx.2
  have hmaps' : Set.MapsTo Ψ' t s := by
    intro y hy
    refine ⟨⟨(ht_sub_P hy).1, Set.mem_univ _⟩, ?_⟩
    rw [Set.mem_preimage, show Ψ (Ψ' y) = y from by simp [hΨdef, hΨ'def]]; exact hy
  have hinv : Ψ' (Ψ x) = x := by simp [hΨdef, hΨ'def, hxdef]
  have hinv' : ∀ y ∈ t, Ψ (Ψ' y) = y := fun y _ => by simp [hΨdef, hΨ'def]
  have hcomp := order_comp_eq_of_diffeo_C (g := g) (e := Ψ) (e' := Ψ')
    hs_open ht_open hx_s hg_cdo hΨ_cdo hΨ'_cdo hmaps hmaps' hinv hinv'
  rw [hΨx] at hcomp
  rw [show (g ∘ Ψ) = fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval (yx.2 + ψfun yx.1) from by
    funext yx; simp [hgdef, hΨdef, Function.comp]] at hcomp
  exact hcomp.symm

open Polynomial in
/-- **Final wiring — the frozen-slice order equals the transverse order.** The order `M` of the frozen
slice `φ(z,·)` (used in the lower bound `order_eval_ge_min`) equals the transverse order
`M' = ord_t((q(cons t z)).eval 0)` (used in the upper bound `order_eval_le_min`). Via the constant-term
identity (`coeff_zero_order_eq`, `ord_u = m·ord F`) and ramification (`coeff_order_ramified`,
`ord_u = m·ord_t`), then cancelling `m`. This is what aligns the two bounds to pin `order ℂ h`. -/
theorem frozen_order_eq_transverse {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F 0) (hFeq : F =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z, w))
    (hLHSan0 : AnalyticAt ℂ (fun u => (q (Fin.cons (u ^ m) z)).coeff 0) 0)
    (hsep : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    (hg : AnalyticAt ℂ (fun w => (q (Fin.cons w z)).coeff 0) 0) :
    analyticOrderAt (fun t : ℂ => (q (Fin.cons t z)).eval 0) 0 = analyticOrderAt F 0 := by
  have h1 := coeff_zero_order_eq hm hmonic hdeg hiff hζ hz hFan hFeq hLHSan0 hsep
  have h2 := coeff_order_ramified hm 0 hg
  have h3 : (m : ℕ∞) * analyticOrderAt (fun w => (q (Fin.cons w z)).coeff 0) 0
      = (m : ℕ∞) * analyticOrderAt F 0 := by rw [← h2]; exact h1
  have h4 : analyticOrderAt (fun w => (q (Fin.cons w z)).coeff 0) 0 = analyticOrderAt F 0 :=
    le_antisymm (enat_le_of_mul_le_mul_left hm h3.le) (enat_le_of_mul_le_mul_left hm h3.ge)
  rw [show (fun t : ℂ => (q (Fin.cons t z)).eval 0) = fun w => (q (Fin.cons w z)).coeff 0 from
    funext fun w => (Polynomial.coeff_zero_eq_eval_zero _).symm, h4]

open Polynomial in
/-- **Lemma 4.2.8, upper bound (Case I direction).** If the central section polynomial is
`q(cons(0,z')) = (X − ψ)ᵐ` (the single root `ψ` of multiplicity `m`, from Conclusion 1), then the
full multivariate order of `h(y,x) = (q y).eval x` at the graph point `(cons(0,z'), ψ)` is `≤ m`. The
`x`-axis line restriction is `t ↦ ((X − ψ)ᵐ).eval(ψ + t) = tᵐ`, of order `m`. -/
theorem order_eval_le_deg {n m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) {z' : Fin n → ℂ} {ψ : ℂ}
    (hq_central : q (Fin.cons 0 z') = (X - C ψ) ^ m)
    (hf : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      (Fin.cons 0 z', ψ)) :
    order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', ψ)
      ≤ (m : ℕ∞) := by
  refine le_trans (order_le_line _ (Fin.cons 0 z', ψ) ((0 : Fin (n + 1) → ℂ), (1 : ℂ)) hf)
    (le_of_eq ?_)
  have hline_eq :
      (fun t : ℂ => (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
        ((Fin.cons 0 z', ψ) + t • ((0 : Fin (n + 1) → ℂ), (1 : ℂ)))) = fun t => t ^ m := by
    funext t
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, smul_eq_mul, mul_one]
    rw [hq_central]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      add_sub_cancel_left]
  rw [hline_eq]
  refine (analyticAt_id.pow m).analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, analyticAt_const,
    one_ne_zero, ?_⟩
  filter_upwards with t
  simp

open Polynomial in
/-- **Lemma 4.2.8, upper bound (Case II direction).** The full order of `h` at `(cons 0 z', ψ)` is
bounded by `m₁ := ord_t((q(cons t z')).eval ψ)` — the order in the transverse coordinate `t` of the
section polynomial's value at the (fixed) root `ψ`. The transverse-axis line restriction is exactly
`t ↦ (q(cons t z')).eval ψ`. (This `m₁` equals the Puiseux order of `φ` relative to the section; here
only the *definition* is needed for the upper bound, sidestepping the branch computation.) -/
theorem order_eval_le_transverse {n : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) {z' : Fin n → ℂ}
    {ψ : ℂ}
    (hf : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      (Fin.cons 0 z', ψ)) :
    order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', ψ)
      ≤ analyticOrderAt (fun t : ℂ => (q (Fin.cons t z')).eval ψ) 0 := by
  refine le_trans (order_le_line _ (Fin.cons 0 z', ψ)
    ((Pi.single 0 1 : Fin (n + 1) → ℂ), (0 : ℂ)) hf) (le_of_eq ?_)
  congr 1
  funext t
  have hcons : (Fin.cons 0 z' + t • (Pi.single 0 1 : Fin (n + 1) → ℂ)) = Fin.cons t z' := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ]
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hcons]

open Polynomial in
/-- **Lemma 4.2.8, the upper bound `≤ min(m, m₁)`.** Combining the `x`-axis (`≤ m`) and transverse
(`≤ m₁`) line restrictions. The lower bound `≥ min(m, m₁)` is the remaining (hard, equisingularity)
direction. -/
theorem order_eval_le_min {n m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) {z' : Fin n → ℂ} {ψ : ℂ}
    (hq_central : q (Fin.cons 0 z') = (X - C ψ) ^ m)
    (hf : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      (Fin.cons 0 z', ψ)) :
    order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', ψ)
      ≤ min (m : ℕ∞) (analyticOrderAt (fun t : ℂ => (q (Fin.cons t z')).eval ψ) 0) :=
  le_min (order_eval_le_deg q hq_central hf) (order_eval_le_transverse q hf)

open Polynomial in
/-- **Lemma 4.2.8 (centered case) — the exact order `= min(m, m₁)`.** For a centered Weierstrass family
(`q(cons 0 z) = Xᵐ`, finite Puiseux order `m₁ = ord F`), the full multivariate order of
`h(y,x) = (q y).eval x` at the central graph point `(cons 0 z', 0)` is exactly `min(m, m₁)`. Combines the
lower bound (`order_eval_ge_min`), the upper bound (`order_eval_le_min`), and the frozen-vs-transverse
order identification (`frozen_order_eq_transverse`). The general (non-centered) case follows by
`order_eval_translate`. -/
theorem order_eval_eq_min {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z' : Fin n → ℂ} (hz' : ‖z'‖ < δz)
    {F : ℂ → ℂ} (hFan : AnalyticAt ℂ F 0) (hFeq : F =ᶠ[𝓝[≠] (0 : ℂ)] fun w => φ (z', w))
    (hFfin : analyticOrderAt F 0 ≠ ⊤)
    (hcentral : ∀ᶠ z in 𝓝 z', q (Fin.cons 0 z) = X ^ m)
    (hana_pt : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (Fin.cons 0 z'))
    (hsep_dir : ∀ v : Fin (n + 1) → ℂ, v 0 ≠ 0 →
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable)
    (hLHSan0 : AnalyticAt ℂ (fun u => (q (Fin.cons (u ^ m) z')).coeff 0) 0)
    (hsep_u : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z')).Separable)
    (hg0 : AnalyticAt ℂ (fun w => (q (Fin.cons w z')).coeff 0) 0) :
    order ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2) (Fin.cons 0 z', 0)
      = min (m : ℕ∞) (analyticOrderAt F 0) := by
  have hf : AnalyticAt ℂ (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
      (Fin.cons 0 z', 0) := by
    rw [show (fun yx : (Fin (n + 1) → ℂ) × ℂ => (q yx.1).eval yx.2)
        = fun yx => ∑ k ∈ Finset.range (m + 1), (q yx.1).coeff k * yx.2 ^ k from by
      funext yx; exact Polynomial.eval_eq_sum_range' (by rw [hdeg]; omega) yx.2]
    refine Finset.analyticAt_fun_sum _ (fun k _ => ?_)
    exact (AnalyticAt.comp (g := fun y => (q y).coeff k)
      (f := fun yx : (Fin (n + 1) → ℂ) × ℂ => yx.1) (hana_pt k) analyticAt_fst).mul
      (analyticAt_snd.pow k)
  have hle := order_eval_le_min q (ψ := 0)
    (by rw [map_zero, sub_zero]; exact hcentral.self_of_nhds) hf
  rw [frozen_order_eq_transverse hm hmonic hdeg hiff hζ hz' hFan hFeq hLHSan0 hsep_u hg0] at hle
  have hM : ((analyticOrderAt F 0).toNat : ℕ∞) ≤ analyticOrderAt F 0 := ENat.coe_toNat_le_self _
  have hge := order_eval_ge_min hm hmonic hdeg hcoeff hroot han hiff hζ hz' hFan hFeq hM hcentral
    hana_pt hsep_dir
  have hMF : ((analyticOrderAt F 0).toNat : ℕ∞) = analyticOrderAt F 0 := ENat.coe_toNat hFfin
  have hcast : ((min m (analyticOrderAt F 0).toNat : ℕ) : ℕ∞)
      = min (m : ℕ∞) ((analyticOrderAt F 0).toNat : ℕ∞) := by
    rcases le_total m (analyticOrderAt F 0).toNat with h | h
    · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
    · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
  rw [hcast, hMF] at hge
  exact le_antisymm hle hge

open Polynomial in
/-- **Instantiation — per-direction separability from the disc normal form.** Given the disc normal
form `disc(q y) = (y 0)ʳ · G(y)` (`G ≠ 0`) on an open `U ∋ cons 0 z'`, `q` is separable along every
ramified curve `cons 0 z' + sᵐ·v` (`v 0 ≠ 0`, `s ≠ 0` near `0`): the disc there is `(sᵐ·v₀)ʳ · G ≠ 0`.
This is the `hsep_dir` input for `order_eval_eq_min`/`coeff_fst_order_ge`. -/
theorem sep_dir_of_disc {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U) {r : ℕ} {G : (Fin (n + 1) → ℂ) → ℂ}
    (hGeq : ∀ y ∈ U, (q y).discr = (y 0) ^ r * G y) (hGne : ∀ y ∈ U, G y ≠ 0)
    {z' : Fin n → ℂ} (hz'U : (Fin.cons 0 z' : Fin (n + 1) → ℂ) ∈ U)
    {v : Fin (n + 1) → ℂ} (hv0 : v 0 ≠ 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), (q (Fin.cons 0 z' + s ^ m • v)).Separable := by
  have hcurve_U : ∀ᶠ s in 𝓝 (0 : ℂ), (Fin.cons 0 z' + s ^ m • v : Fin (n + 1) → ℂ) ∈ U := by
    have hcont : ContinuousAt
        (fun s : ℂ => (Fin.cons 0 z' + s ^ m • v : Fin (n + 1) → ℂ)) 0 := by fun_prop
    have h0 : (fun s : ℂ => (Fin.cons 0 z' + s ^ m • v : Fin (n + 1) → ℂ)) 0 = Fin.cons 0 z' := by
      simp [zero_pow hm.ne']
    exact hcont.eventually (by rw [h0]; exact hU.mem_nhds hz'U)
  filter_upwards [hcurve_U.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hsU hs0
  refine separable_of_discr_ne_zero (hmonic _) (by rw [hdeg]; exact hm) ?_
  rw [hGeq _ hsU]
  have hcoord0 : (Fin.cons 0 z' + s ^ m • v : Fin (n + 1) → ℂ) 0 = s ^ m * v 0 := by
    simp [Fin.cons_zero]
  rw [hcoord0]
  exact mul_ne_zero (pow_ne_zero r (mul_ne_zero (pow_ne_zero m
    (Set.mem_compl_singleton_iff.mp hs0)) hv0)) (hGne _ hsU)

/-! ### Step B — order of the branch product equals the sum of branch-difference orders -/

/-- **Sum of branch-difference orders = order of the branch product.** With the off-diagonal
"branch difference" family `η_{ij} = φ(z,ζⁱ·) − φ(z,ζʲ·)` (and diagonal entries set to the unit `1`),
the sum over all pairs of the analytic orders equals the order of the full product
`∏ᵢ ∏_{j≠i} η_{ij}` (which is `±disc` by `weierstrass_disc_eq_prod_branches`). Diagonal entries
contribute `0`; the product splits by `analyticOrderAt_prod`. -/
theorem sum_order_eq_order_branchProd {n m : ℕ} {φ : (Fin n → ℂ) × ℂ → ℂ} {ζ : ℂ} {z : Fin n → ℂ}
    (hdiff_an : ∀ i j : Fin m, i ≠ j →
      AnalyticAt ℂ (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0) :
    (∑ k : Fin m × Fin m, analyticOrderAt
        (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) 0)
      = analyticOrderAt
        (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 := by
  classical
  -- RHS as a double sum via `analyticOrderAt_prod`
  have hRHS : analyticOrderAt
      (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
        (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
          analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 := by
    rw [analyticOrderAt_prod (Finset.univ : Finset (Fin m))
      (fun i => fun u => ∏ j ∈ Finset.univ.erase i,
        (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)))
      (fun i _ => Finset.analyticAt_fun_prod _
        (fun j hj => hdiff_an i j ((Finset.mem_erase.mp hj).1).symm))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact analyticOrderAt_prod (Finset.univ.erase i)
      (fun j => fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))
      (fun j hj => hdiff_an i j ((Finset.mem_erase.mp hj).1).symm)
  -- LHS as the same double sum: diagonal terms vanish
  rw [hRHS, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [↓reduceIte]
  have hc : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 0 = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  rw [hc, zero_add]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [if_neg (Ne.symm hji)]

/-! ### Bridge — analyticity of the discriminant of an analytic family -/

/-- **Determinant of a matrix with analytic entries is analytic.** `det` is a finite signed sum of
products of the entries (`Matrix.det_apply`), so analyticity is inherited from the entries. -/
theorem analyticAt_matrix_det {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : W → Matrix ι ι ℂ}
    {z₀ : W} (h : ∀ i j, AnalyticAt ℂ (fun u => M u i j) z₀) :
    AnalyticAt ℂ (fun u => (M u).det) z₀ := by
  have he : (fun u => (M u).det)
      = fun u => ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M u (σ i) i := by
    funext u; rw [Matrix.det_apply]
  rw [he]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  exact (Finset.analyticAt_fun_prod _ (fun i _ => h (σ i) i)).const_smul

open Polynomial in
/-- **The discriminant of the ramified Weierstrass family is analytic in `u`.** Since
`disc f = ± resultant f f' = ± det(sylvester f f')` and the Sylvester entries are coefficients of
`f = q(cons(uᵐ,z))` and `f' = f.derivative` (analytic in `u`), the map `u ↦ disc(q(cons(uᵐ,z)))` is
analytic. This is the missing regularity that lets the order of the branch product be identified with
the order of the discriminant. -/
theorem analyticAt_disc_comp {n m : ℕ} (hm : 0 < m) {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {g : W → Fin (n + 1) → ℂ} {u₀ : W}
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (g u₀)) (hg : AnalyticAt ℂ g u₀) :
    AnalyticAt ℂ (fun u => (q (g u)).discr) u₀ := by
  classical
  -- coefficients of `f = q(g u)` and `f' = derivative f` are analytic in `u`
  have hPan : ∀ k, AnalyticAt ℂ (fun u => (q (g u)).coeff k) u₀ := fun k =>
    AnalyticAt.comp (g := fun y => (q y).coeff k) (f := g) (hcoeff k) hg
  have hQan : ∀ k, AnalyticAt ℂ (fun u => (q (g u)).derivative.coeff k) u₀ := by
    intro k
    simp only [coeff_derivative]
    exact (hPan (k + 1)).mul analyticAt_const
  -- entries of the Sylvester matrix are analytic
  have hentry : ∀ i j : Fin (m + (m - 1)),
      AnalyticAt ℂ (fun u => sylvester (q (g u)) (q (g u)).derivative m (m - 1) i j) u₀ := by
    intro i j
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      by_cases hcond : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + (m - 1))
      · simp only [if_pos hcond]; exact hQan _
      · simp only [if_neg hcond]; exact analyticAt_const
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      by_cases hcond : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + m)
      · simp only [if_pos hcond]; exact hPan _
      · simp only [if_neg hcond]; exact analyticAt_const
  -- `disc f = ± resultant f f' m (m-1)`, pointwise
  have hdisceq : ∀ u, (q (g u)).discr
      = (-1) ^ (m * (m - 1) / 2)
        * resultant (q (g u)) (q (g u)).derivative m (m - 1) := by
    intro u
    have hfdeg : (q (g u)).natDegree = m := hdeg _
    have hfmonic : (q (g u)).Monic := hmonic _
    have hdpos : 0 < (q (g u)).degree := by
      rw [degree_eq_natDegree hfmonic.ne_zero, hfdeg]; exact_mod_cast hm
    have hrd := resultant_deriv hdpos
    rw [hfdeg, hfmonic.leadingCoeff, mul_one] at hrd
    have hsq : ((-1 : ℂ)) ^ (m * (m - 1) / 2) * (-1) ^ (m * (m - 1) / 2) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [hrd, ← mul_assoc, hsq, one_mul]
  rw [show (fun u => (q (g u)).discr)
      = fun u => (-1) ^ (m * (m - 1) / 2)
        * (sylvester (q (g u)) (q (g u)).derivative m (m - 1)).det
      from funext hdisceq]
  exact analyticAt_const.mul (analyticAt_matrix_det hentry)

/-- The ramified specialisation `g = u ↦ cons(uᵐ, z)` of `analyticAt_disc_comp`. -/
theorem analyticAt_disc_comp_pow {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m) (z : Fin n → ℂ) (u₀ : ℂ)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (Fin.cons (u₀ ^ m) z)) :
    AnalyticAt ℂ (fun u => (q (Fin.cons (u ^ m) z)).discr) u₀ :=
  analyticAt_disc_comp hm hmonic hdeg hcoeff
    (g := fun u => (Fin.cons (u ^ m) z : Fin (n + 1) → ℂ)) (by
      rw [analyticAt_pi_iff]
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; exact analyticAt_id.pow m
      · simp only [Fin.cons_succ]; exact analyticAt_const)

open Polynomial in
/-- **Ramification of the discriminant order.** The order in `u` of `disc(q(cons(uᵐ,z)))` is `m`
times the order in `w` (the transverse coordinate) of `disc(q(cons(w,z)))` at `w = 0`. Immediate
from `analyticOrderAt_comp_pow` applied to the analytic slice `w ↦ disc(q(cons(w,z)))`. This converts
the (ramified) `u`-order appearing in the branch analysis into the genuine transverse-coordinate
order that the discriminant normal form controls. -/
theorem disc_comp_pow_order_eq {n m : ℕ} (hm : 0 < m) {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m) (z : Fin n → ℂ)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (Fin.cons 0 z)) :
    analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z)).discr) 0
      = m * analyticOrderAt (fun w => (q (Fin.cons w z)).discr) 0 := by
  have hf : AnalyticAt ℂ (fun w => (q (Fin.cons w z)).discr) 0 :=
    analyticAt_disc_comp hm hmonic hdeg hcoeff
      (g := fun w => (Fin.cons w z : Fin (n + 1) → ℂ)) (by
        rw [analyticAt_pi_iff]
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp only [Fin.cons_zero]; exact analyticAt_id
        · simp only [Fin.cons_succ]; exact analyticAt_const)
  exact analyticOrderAt_comp_pow hf hm

/-! ### Bridge ingredient — the discriminant equals the branch product near `u = 0` -/

open Polynomial in
/-- **Discriminant = branch product on the punctured disc.** For fixed `z` in the domain, where
`q(cons(uᵐ, z))` is separable for small `u ≠ 0`, the discriminant `u ↦ disc(q(cons(uᵐ, z)))` agrees
with `±` the branch product `∏ᵢ ∏_{j≠i} (φ(z,ζⁱu) − φ(z,ζʲu))` on a punctured neighbourhood of `0`
(pointwise `weierstrass_disc_eq_prod_branches`). This is the analytic identity feeding the bridge:
the order of the branch product (Step B) equals the order of the discriminant, which the discriminant
theory controls. -/
theorem disc_eventuallyEq_branchProd {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    (hsep : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable) :
    (fun u => (q (Fin.cons (u ^ m) z)).discr) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun u => (-1) ^ (m * (m - 1) / 2)
        * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) := by
  have hlt : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖u‖ ^ m < Real.exp c := by
    have hcont0 : ContinuousAt (fun u : ℂ => ‖u‖ ^ m) 0 := (continuous_norm.pow m).continuousAt
    have h0 : (fun u : ℂ => ‖u‖ ^ m) 0 < Real.exp c := by
      simpa [zero_pow hm.ne'] using Real.exp_pos c
    exact (hcont0.eventually_lt continuousAt_const h0).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsep, hlt, self_mem_nhdsWithin] with u hsepu hudu huneq
  have hune : u ≠ 0 := huneq
  exact weierstrass_disc_eq_prod_branches hm hmonic hdeg hiff hζ hz (norm_pos_iff.mpr hune) hudu hsepu

open Polynomial in
/-- **Branch-product order = discriminant order.** For `z` in the domain with `q(cons(uᵐ,z))`
separable for small `u ≠ 0`, the order at `0` of the branch product equals the order of the
discriminant `u ↦ disc(q(cons(uᵐ,z)))`. The two functions agree on a punctured neighbourhood
(`disc_eventuallyEq_branchProd`) and are *both analytic at `0`* (Step A for the product,
`analyticAt_disc_comp_pow` for the discriminant), so the identity theorem
(`frequently_eq_iff_eventually_eq`) upgrades the agreement across `0`; the `±1` factor is a unit. -/
theorem branchProd_order_eq_disc_order {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {z : Fin n → ℂ} (hz : ‖z‖ < δz)
    (hana : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (Fin.cons 0 z))
    {R : ℝ} (hR : 0 < R) (hRc : R ^ m < Real.exp c)
    (hsep : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable) :
    analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
        (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z)).discr) 0 := by
  have hnormζ : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hm.ne'
  have hnormζp : ∀ i : Fin m, ‖ζ ^ (i : ℕ)‖ = 1 := fun i => by rw [norm_pow, hnormζ, one_pow]
  have hdiff_an : ∀ i j : Fin m, i ≠ j →
      AnalyticAt ℂ (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 := by
    intro i j _
    exact branchDiff_slice_analyticOnNhd hm hmonic hdeg hcont hroot han hz
      (hnormζp i) (hnormζp j) hRc 0 (Metric.mem_ball_self hR)
  have hbp_an : AnalyticAt ℂ (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
      (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 := by
    refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
    exact Finset.analyticAt_fun_prod _
      (fun j hj => hdiff_an i j ((Finset.mem_erase.mp hj).1).symm)
  have hdisc_an : AnalyticAt ℂ (fun u => (q (Fin.cons (u ^ m) z)).discr) 0 :=
    analyticAt_disc_comp_pow hm hmonic hdeg z 0
      (fun i => by simpa only [zero_pow hm.ne'] using hana i)
  have hrhs_an : AnalyticAt ℂ (fun u => (-1) ^ (m * (m - 1) / 2)
      * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 := analyticAt_const.mul hbp_an
  have heqp := disc_eventuallyEq_branchProd hm hmonic hdeg hiff hζ hz hsep
  have heqfull := (hdisc_an.frequently_eq_iff_eventually_eq hrhs_an).mp heqp.frequently
  have hord_rhs : analyticOrderAt (fun u => (-1) ^ (m * (m - 1) / 2)
      * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 := by
    rw [show (fun u => (-1 : ℂ) ^ (m * (m - 1) / 2)
          * ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
              (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)))
        = (fun _ => (-1 : ℂ) ^ (m * (m - 1) / 2))
          * (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
              (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) from rfl,
      analyticOrderAt_mul analyticAt_const hbp_an,
      analyticAt_const.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ (by norm_num)), zero_add]
  rw [analyticOrderAt_congr heqfull, hord_rhs]

/-! ### Bridge — transverse-slice order from the discriminant normal form -/

/-- **Slice order from a coordinate-`0` factorization.** If `D = (coord 0)ʳ · G` near
`cons 0 z₀` with `G` analytic and `G(cons 0 z₀) ≠ 0` (the discriminant *normal form* `disc =
wʳ·unit`), then the order in the transverse coordinate `w` of the slice `w ↦ D(cons w z)` is exactly
`r` for all `z` near `z₀` — in particular *constant*. This is the bridge from the discriminant
normal form to `hslice_const`. -/
theorem slice_order_eq_of_factor {n : ℕ} {D G : (Fin (n + 1) → ℂ) → ℂ} {z₀ : Fin n → ℂ} {r : ℕ}
    (hG : AnalyticAt ℂ G (Fin.cons 0 z₀)) (hG0 : G (Fin.cons 0 z₀) ≠ 0)
    (hfac : D =ᶠ[𝓝 (Fin.cons 0 z₀)] fun y => (y 0) ^ r * G y) :
    ∀ᶠ z in 𝓝 z₀, analyticOrderAt (fun w => D (Fin.cons w z)) 0 = (r : ℕ∞) := by
  -- the gluing map `(z, w) ↦ cons w z`
  have hκ : Continuous (fun p : (Fin n → ℂ) × ℂ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; exact continuous_snd
    · simp only [Fin.cons_succ]; exact (continuous_apply i).comp continuous_fst
  have hcons0 : Continuous (fun z : Fin n → ℂ => (Fin.cons 0 z : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; exact continuous_const
    · simp only [Fin.cons_succ]; exact continuous_apply i
  -- pull the factorization back to the slices
  have hpre := (hκ.continuousAt (x := (z₀, 0))).eventually hfac
  rw [nhds_prod_eq] at hpre
  have hGne : ∀ᶠ z in 𝓝 z₀, G (Fin.cons 0 z) ≠ 0 :=
    ((hG.continuousAt.comp hcons0.continuousAt).eventually_ne hG0)
  have hGan : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ G (Fin.cons 0 z) :=
    hcons0.continuousAt.eventually hG.eventually_analyticAt
  filter_upwards [hpre.curry, hGne, hGan] with z hslice hz0 hzan
  -- the slice base map `w ↦ cons w z` is analytic
  have hcons_w : AnalyticAt ℂ (fun w : ℂ => (Fin.cons w z : Fin (n + 1) → ℂ)) 0 := by
    rw [analyticAt_pi_iff]
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; exact analyticAt_id
    · simp only [Fin.cons_succ]; exact analyticAt_const
  have hg_an : AnalyticAt ℂ (fun w => G (Fin.cons w z)) 0 :=
    AnalyticAt.comp (g := G) (f := fun w => (Fin.cons w z : Fin (n + 1) → ℂ)) hzan hcons_w
  have hg0 : (fun w => G (Fin.cons w z)) 0 ≠ 0 := hz0
  have hf_eq : (fun w => D (Fin.cons w z)) =ᶠ[𝓝 (0 : ℂ)]
      fun w => (w - 0) ^ r • G (Fin.cons w z) := by
    filter_upwards [hslice] with w hw
    simp only [hw, Fin.cons_zero, sub_zero, smul_eq_mul]
  have hf_an : AnalyticAt ℂ (fun w => D (Fin.cons w z)) 0 :=
    (((analyticAt_id.sub analyticAt_const).pow r).smul hg_an).congr hf_eq.symm
  exact hf_an.analyticOrderAt_eq_natCast.mpr ⟨fun w => G (Fin.cons w z), hg_an, hg0, hf_eq⟩

/-! ### Assembly — branch-difference orders are locally constant (modulo the bridge) -/

/-- **Lemma 4.2.7 (branch-order constancy), assembled.** Given the Newton–Puiseux parametrization
data for a Weierstrass family `q` and a base point `z₀` in the domain, with the branch points
`ζⁱ·u`, IF the order of the branch product `∏ᵢ ∏_{j≠i} (φ(z,ζⁱu) − φ(z,ζʲu))` (which is `±disc`) is
locally constant in `z` (the *bridge* hypothesis, supplied by the discriminant theory), THEN each
branch-difference order is locally constant. This combines Step A (`branchDiff_*`,
`branchDiff_order_ne_top`), Step B (`sum_order_eq_order_branchProd`), and the abstract heart
`branch_order_constant`. -/
theorem branchDiff_orders_eventually_constant {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z₀ : Fin n → ℂ} (hz₀ : ‖z₀‖ < δz)
    (hsep₀ : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z₀)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    (hbridge : ∀ᶠ z in 𝓝 z₀,
        analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
            (φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u))) 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ i j : Fin m, i ≠ j →
      analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
      = analyticOrderAt (fun u => φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u)) 0 := by
  classical
  have hnormζ : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hm.ne'
  have hnormζp : ∀ i : Fin m, ‖ζ ^ (i : ℕ)‖ = 1 := fun i => by rw [norm_pow, hnormζ, one_pow]
  have hR : 0 < R := lt_trans hρ hρR
  -- a neighbourhood of `z₀` inside the domain
  have hrz : 0 < δz - ‖z₀‖ := by linarith
  have hS : Metric.ball z₀ (δz - ‖z₀‖) ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ hrz
  have hSsub : ∀ z ∈ Metric.ball z₀ (δz - ‖z₀‖), ‖z‖ < δz := by
    intro z hz
    have hd : dist z z₀ < δz - ‖z₀‖ := Metric.mem_ball.mp hz
    have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by simpa using norm_add_le z₀ (z - z₀)
    rw [dist_eq_norm] at hd; linarith
  have hzev : ∀ᶠ z in 𝓝 z₀, ‖z‖ < δz := Filter.eventually_of_mem hS hSsub
  -- the contour radius lies in the punctured `u`-domain
  have hTc : ∀ θ : ℝ, circleMap 0 ρ θ ∈ {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c} := by
    intro θ
    rw [Set.mem_setOf_eq, norm_circleMap_zero, abs_of_pos hρ]
    exact ⟨hρ, lt_trans (pow_lt_pow_left₀ hρR hρ.le hm.ne') hRc⟩
  -- per-slice analyticity of branch differences (Step A)
  have hdiff_an : ∀ z, ‖z‖ < δz → ∀ i j : Fin m, i ≠ j →
      AnalyticAt ℂ (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0 := by
    intro z hz i j _
    exact branchDiff_slice_analyticOnNhd hm hmonic hdeg hcoeff hroot han hz
      (hnormζp i) (hnormζp j) hRc 0 (Metric.mem_ball_self hR)
  -- Step B: the pair-sum of orders equals the order of the branch product
  have hsum_at : ∀ z, ‖z‖ < δz →
      (∑ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) 0)
      = analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0 :=
    fun z hz => sum_order_eq_order_branchProd (fun i j hij => hdiff_an z hz i j hij)
  -- the hypotheses of `branch_order_constant`
  have hcont : ∀ k : Fin m × Fin m, ContinuousOn (Function.uncurry
      (fun (z : Fin n → ℂ) (u : ℂ) => if k.1 = k.2 then (1 : ℂ)
        else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)))
      (Metric.ball z₀ (δz - ‖z₀‖) ×ˢ {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c}) := by
    intro k
    rcases eq_or_ne k.1 k.2 with h | h
    · simp only [if_pos h]; exact continuousOn_const
    · simp only [if_neg h]
      exact branchDiff_continuousOn han (hnormζp k.1) (hnormζp k.2) hSsub
  have hana : ∀ k : Fin m × Fin m, ∀ᶠ z in 𝓝 z₀, AnalyticOnNhd ℂ
      (fun u => if k.1 = k.2 then (1 : ℂ)
        else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) (Metric.ball 0 R) := by
    intro k
    rcases eq_or_ne k.1 k.2 with h | h
    · filter_upwards with z; simp only [if_pos h]; exact analyticOnNhd_const
    · filter_upwards [hzev] with z hz; simp only [if_neg h]
      exact branchDiff_slice_analyticOnNhd hm hmonic hdeg hcoeff hroot han hz
        (hnormζp k.1) (hnormζp k.2) hRc
  have hfin : ∀ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
      else φ (z₀, ζ ^ (k.1 : ℕ) * u) - φ (z₀, ζ ^ (k.2 : ℕ) * u)) 0 ≠ ⊤ := by
    intro k
    rcases eq_or_ne k.1 k.2 with h | h
    · simp only [if_pos h]
      have h0 : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 0 = 0 :=
        analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
      rw [h0]; exact (by decide)
    · simp only [if_neg h]
      exact branchDiff_order_ne_top hm hmonic hdeg hiff hζ hz₀ hsep₀ h
  have hbp0 := hsum_at z₀ hz₀
  have hsumconst : ∀ᶠ z in 𝓝 z₀,
      (∑ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u)) 0)
      = ∑ k : Fin m × Fin m, analyticOrderAt (fun u => if k.1 = k.2 then (1 : ℂ)
          else φ (z₀, ζ ^ (k.1 : ℕ) * u) - φ (z₀, ζ ^ (k.2 : ℕ) * u)) 0 := by
    filter_upwards [hbridge, hzev] with z hbz hz
    rw [hsum_at z hz, hbz, ← hbp0]
  have key := branch_order_constant (η := fun (k : Fin m × Fin m) (z : Fin n → ℂ) (u : ℂ) =>
      if k.1 = k.2 then (1 : ℂ) else φ (z, ζ ^ (k.1 : ℕ) * u) - φ (z, ζ ^ (k.2 : ℕ) * u))
      (z₀ := z₀) (S := Metric.ball z₀ (δz - ‖z₀‖))
      (T := {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ ^ m < Real.exp c})
      hS hρ hρR hTc hcont hana hfin hsumconst
  filter_upwards [key] with z hz
  intro i j hij
  have h := hz (i, j)
  simp only [if_neg hij] at h
  exact h

open Polynomial in
/-- **Lemma 4.2.7, reduced to discriminant-order constancy.** This is `branchDiff_orders_eventually_
constant` with the bridge hypothesis replaced by the *more primitive* and natural condition that the
order in `u` of the discriminant `u ↦ disc(q(cons(uᵐ,z)))` is locally constant in `z`. The branch
product order is identified with the discriminant order (`branchProd_order_eq_disc_order`) at each
`z` near `z₀`, discharging the bridge. The remaining input `hdisc_const` is what the discriminant
theory (ramification + normal form, cf. `analyticOrderAt_comp_pow` and `DiscNormalForm`) supplies. -/
theorem branchDiff_orders_eventually_constant_of_disc {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z₀ : Fin n → ℂ} (hz₀ : ‖z₀‖ < δz)
    (hana_ev : ∀ᶠ z in 𝓝 z₀, ∀ i, AnalyticAt ℂ (fun z' => (q z').coeff i) (Fin.cons 0 z))
    (hsep_nbhd : ∀ᶠ z in 𝓝 z₀, ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    (hdisc_const : ∀ᶠ z in 𝓝 z₀,
        analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z)).discr) 0
      = analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z₀)).discr) 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ i j : Fin m, i ≠ j →
      analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
      = analyticOrderAt (fun u => φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u)) 0 := by
  have hR : 0 < R := lt_trans hρ hρR
  have hrz : 0 < δz - ‖z₀‖ := by linarith
  have hS : Metric.ball z₀ (δz - ‖z₀‖) ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ hrz
  have hSsub : ∀ z ∈ Metric.ball z₀ (δz - ‖z₀‖), ‖z‖ < δz := by
    intro z hz
    have hd : dist z z₀ < δz - ‖z₀‖ := Metric.mem_ball.mp hz
    have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by simpa using norm_add_le z₀ (z - z₀)
    rw [dist_eq_norm] at hd; linarith
  have hzev : ∀ᶠ z in 𝓝 z₀, ‖z‖ < δz := Filter.eventually_of_mem hS hSsub
  have hsep₀ : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z₀)).Separable :=
    hsep_nbhd.self_of_nhds
  -- discharge the branch-product bridge from discriminant-order constancy (part a)
  have hbp0 := branchProd_order_eq_disc_order hm hmonic hdeg hcont hroot han hiff hζ hz₀
    hana_ev.self_of_nhds hR hRc hsep₀
  have hbridge : ∀ᶠ z in 𝓝 z₀,
      analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u))) 0
      = analyticOrderAt (fun u => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i,
          (φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u))) 0 := by
    filter_upwards [hsep_nbhd, hdisc_const, hzev, hana_ev] with z hsepz hdiscz hz hanaz
    rw [branchProd_order_eq_disc_order hm hmonic hdeg hcont hroot han hiff hζ hz hanaz hR hRc hsepz,
      hdiscz, ← hbp0]
  exact branchDiff_orders_eventually_constant hm hmonic hdeg hcont hroot han hiff hζ hz₀
    hsep₀ hρ hρR hRc hbridge

open Polynomial in
/-- **Lemma 4.2.7, reduced to transverse-coordinate discriminant-order constancy.** The cleanest
interface to the discriminant theory: the bridge holds as soon as the order in the *transverse
coordinate* `w` of `disc(q(cons(w,z)))` at `w = 0` is locally constant in the section variable `z`.
This is exactly the statement supplied by the discriminant normal form together with the axiom's
hypothesis that the (multivariate) discriminant has constant order along the section. The ramification
factor `m` (`disc_comp_pow_order_eq`) cancels. -/
theorem branchDiff_orders_eventually_constant_of_disc_slice {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z₀ : Fin n → ℂ} (hz₀ : ‖z₀‖ < δz)
    (hana_ev : ∀ᶠ z in 𝓝 z₀, ∀ i, AnalyticAt ℂ (fun z' => (q z').coeff i) (Fin.cons 0 z))
    (hsep_nbhd : ∀ᶠ z in 𝓝 z₀, ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    (hslice_const : ∀ᶠ z in 𝓝 z₀,
        analyticOrderAt (fun w => (q (Fin.cons w z)).discr) 0
      = analyticOrderAt (fun w => (q (Fin.cons w z₀)).discr) 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ i j : Fin m, i ≠ j →
      analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
      = analyticOrderAt (fun u => φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u)) 0 := by
  have hdisc_const : ∀ᶠ z in 𝓝 z₀,
      analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z)).discr) 0
      = analyticOrderAt (fun u => (q (Fin.cons (u ^ m) z₀)).discr) 0 := by
    filter_upwards [hslice_const, hana_ev] with z hsz hanaz
    rw [disc_comp_pow_order_eq hm hmonic hdeg z hanaz,
      disc_comp_pow_order_eq hm hmonic hdeg z₀ hana_ev.self_of_nhds, hsz]
  exact branchDiff_orders_eventually_constant_of_disc hm hmonic hdeg hcont hroot han hiff hζ hz₀
    hana_ev hsep_nbhd hρ hρR hRc hdisc_const

open Polynomial in
/-- **Lemma 4.2.7, reduced to the discriminant normal form.** The final, cleanest interface: the
branch-difference orders are locally constant as soon as the discriminant `y ↦ disc(q y)` admits the
normal form `disc = (coord 0)ʳ · G` near `cons 0 z₀` with `G(cons 0 z₀) ≠ 0` (`G` a unit). This is
exactly what the discriminant theory (`DiscNormalForm`: `disc` divisible by the transverse coordinate
to its full order, with non-vanishing cofactor) produces from the axiom's hypothesis that the
discriminant has finite, section-constant order. The transverse-slice order is then identically `r`
(`slice_order_eq_of_factor`), discharging the bridge entirely. -/
theorem branchDiff_orders_eventually_constant_of_factor {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    {z₀ : Fin n → ℂ} (hz₀ : ‖z₀‖ < δz)
    (hana_ev : ∀ᶠ z in 𝓝 z₀, ∀ i, AnalyticAt ℂ (fun z' => (q z').coeff i) (Fin.cons 0 z))
    (hsep_nbhd : ∀ᶠ z in 𝓝 z₀, ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    {r : ℕ} {G : (Fin (n + 1) → ℂ) → ℂ}
    (hG : AnalyticAt ℂ G (Fin.cons 0 z₀)) (hG0 : G (Fin.cons 0 z₀) ≠ 0)
    (hfac : (fun y => (q y).discr) =ᶠ[𝓝 (Fin.cons 0 z₀)] fun y => (y 0) ^ r * G y) :
    ∀ᶠ z in 𝓝 z₀, ∀ i j : Fin m, i ≠ j →
      analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
      = analyticOrderAt (fun u => φ (z₀, ζ ^ (i : ℕ) * u) - φ (z₀, ζ ^ (j : ℕ) * u)) 0 := by
  have hslice := slice_order_eq_of_factor hG hG0 hfac
  have h0 : analyticOrderAt (fun w => (q (Fin.cons w z₀)).discr) 0 = (r : ℕ∞) :=
    hslice.self_of_nhds
  have hslice_const : ∀ᶠ z in 𝓝 z₀,
      analyticOrderAt (fun w => (q (Fin.cons w z)).discr) 0
      = analyticOrderAt (fun w => (q (Fin.cons w z₀)).discr) 0 := by
    filter_upwards [hslice] with z hz
    rw [hz, h0]
  exact branchDiff_orders_eventually_constant_of_disc_slice hm hmonic hdeg hcont hroot han hiff hζ
    hz₀ hana_ev hsep_nbhd hρ hρR hRc hslice_const

open Polynomial in
/-- **Lemma 4.2.7, from the discriminant's `order` hypotheses (full bridge closed).** The
branch-difference orders are locally constant around the central section point `0`, given the
*discriminant theory* hypotheses in the exact form supplied by the axiom / `DiscNormalForm`:
the discriminant `y ↦ disc(q y)` is analytic, vanishes on the hyperplane `{y 0 = 0}` near `0`, has
finite order, and its multivariate `order` is constant along the section. `DiscNormalForm.exists_
coord0_pow_factor` turns these into the normal form `disc = (y 0)ʳ · G` with `G 0 ≠ 0`, and
`branchDiff_orders_eventually_constant_of_factor` finishes. This closes the bridge: no hypothesis here
mentions the Puiseux branches or the discriminant *normal form witness* — only the raw `order`
conditions of the axiom. -/
theorem branchDiff_orders_eventually_constant_of_discNormalForm {n m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    {φ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ}
    (hroot : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0)
    (han : ∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u))
    (hiff : ∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hz₀ : ‖(0 : Fin n → ℂ)‖ < δz)
    (hsep_nbhd : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      ∀ᶠ u in 𝓝[≠] (0 : ℂ), (q (Fin.cons (u ^ m) z)).Separable)
    {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hRc : R ^ m < Real.exp c)
    (hdisc_vanish : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), y 0 = 0 → (q y).discr = 0)
    (hdisc_ne : order ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ) ≠ ⊤)
    (hdisc_const : ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
        order ℂ (fun y => (q y).discr) w = order ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ)) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i j : Fin m, i ≠ j →
      analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
      = analyticOrderAt
          (fun u => φ ((0 : Fin n → ℂ), ζ ^ (i : ℕ) * u) - φ ((0 : Fin n → ℂ), ζ ^ (j : ℕ) * u)) 0 := by
  have hcz : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
    funext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp
  have hDan : AnalyticAt ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ) :=
    analyticAt_disc_comp hm hmonic hdeg (W := Fin (n + 1) → ℂ) (g := fun y => y) hana0 analyticAt_id
  -- coefficients are analytic on a neighbourhood of `0`, hence at `cons 0 z` for `z` near `0`
  have hev : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) y := by
    have hfin : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ),
        ∀ i ∈ Finset.range (m + 1), AnalyticAt ℂ (fun z => (q z).coeff i) y :=
      (Filter.eventually_all_finset _).mpr (fun i _ => (hana0 i).eventually_analyticAt)
    filter_upwards [hfin] with y hy i
    by_cases hi : i ≤ m
    · exact hy i (Finset.mem_range.mpr (by omega))
    · have hzero : (fun z => (q z).coeff i) = fun _ => (0 : ℂ) := by
        funext z; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg z]; omega)
      rw [hzero]; exact analyticAt_const
  have hcons0 : Continuous (fun z : Fin n → ℂ => (Fin.cons 0 z : Fin (n + 1) → ℂ)) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; exact continuous_const
    · simp only [Fin.cons_succ]; exact continuous_apply i
  have htend : Filter.Tendsto (fun z : Fin n → ℂ => (Fin.cons 0 z : Fin (n + 1) → ℂ))
      (𝓝 0) (𝓝 0) := by have := hcons0.tendsto (0 : Fin n → ℂ); rwa [hcz] at this
  have hana_ev : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),
      ∀ i, AnalyticAt ℂ (fun z' => (q z').coeff i) (Fin.cons 0 z) := htend.eventually hev
  obtain ⟨G, hGan, hG0, hfac⟩ := DiscNormalForm.exists_coord0_pow_factor
    (order ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ)).toNat (fun y => (q y).discr)
    hDan hdisc_vanish rfl hdisc_ne hdisc_const
  refine branchDiff_orders_eventually_constant_of_factor hm hmonic hdeg hcont hroot han hiff hζ
    hz₀ hana_ev hsep_nbhd hρ hρR hRc (r := (order ℂ (fun y => (q y).discr) (0 : Fin (n + 1) → ℂ)).toNat)
    (G := G) ?_ ?_ ?_
  · rw [hcz]; exact hGan
  · rw [hcz]; exact hG0
  · rw [hcz]; exact hfac

end Puiseux
