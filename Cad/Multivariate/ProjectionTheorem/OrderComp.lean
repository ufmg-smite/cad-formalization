import Cad.Multivariate.ProjectionTheorem.Order
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Vanishing order is invariant under local analytic diffeomorphisms

The vanishing `order` (least `n` with `iteratedFDeriv n f x ≠ 0`) is a local analytic
invariant: composing with a local analytic diffeomorphism does not change it. This is the
key lemma for transferring an *ambient* order-invariance hypothesis through a straightening
chart, replacing the (often infinite) chart-restricted order along a submanifold.

## Main results

* `order_le_order_comp` — composing with an analytic map can only increase order.
* `order_comp_eq_of_diffeo` — order is preserved under a local analytic diffeomorphism.

The one-directional step avoids the full Faà-di-Bruno formula: it uses only the *bound*
`norm_iteratedFDerivWithin_comp_le`, with the outer derivatives all zero (so `C = 0`), which
forces the composite's derivative norm to be `≤ 0`, hence zero.
-/

noncomputable section

open Filter Set
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If all Fréchet derivatives of order `< k` of `f` vanish at `x`, then `k ≤ order f x`. -/
theorem le_order_of_forall_iteratedFDeriv_eq_zero {f : E → ℝ} {x : E} {k : ℕ∞}
    (h : ∀ j : ℕ, (↑j : ℕ∞) < k → iteratedFDeriv ℝ j f x = 0) :
    k ≤ order ℝ f x := by
  by_contra hlt
  push_neg at hlt
  have hfin : order ℝ f x ≠ ⊤ := ne_top_of_lt hlt
  have hm : order ℝ f x = ↑(order ℝ f x).toNat := (ENat.coe_toNat hfin).symm
  rw [hm] at hlt
  exact (((order_eq_natCast_iff).mp hm).2) (h _ hlt)

/-- The vanishing order depends only on the germ. -/
theorem order_congr_of_eventuallyEq {f₁ f₂ : E → ℝ} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    order ℝ f₁ x = order ℝ f₂ x := by
  have key : ∀ n, iteratedFDeriv ℝ n f₁ x = iteratedFDeriv ℝ n f₂ x :=
    fun n => (h.iteratedFDeriv ℝ n).eq_of_nhds
  apply le_antisymm
  · apply le_order_of_forall_iteratedFDeriv_eq_zero
    intro j hj
    rw [← key]; exact iteratedFDeriv_eq_zero_of_lt_order hj
  · apply le_order_of_forall_iteratedFDeriv_eq_zero
    intro j hj
    rw [key]; exact iteratedFDeriv_eq_zero_of_lt_order hj

/-- **One-directional order bound under composition.**
If `g` and `f` are smooth on open sets `t ∋ f x` and `s ∋ x` with `f` mapping `s` into `t`,
then composing can only *increase* the vanishing order: `order g (f x) ≤ order (g ∘ f) x`.

The proof feeds `norm_iteratedFDerivWithin_comp_le` the bound `C = 0` (all lower derivatives
of `g` at `f x` vanish), forcing `‖iteratedFDeriv j (g ∘ f) x‖ ≤ 0`. -/
theorem order_le_order_comp
    {g : F → ℝ} {f : E → F} {s : Set E} {t : Set F} {x : E}
    (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hg : ContDiffOn ℝ (⊤ : WithTop ℕ∞) g t) (hf : ContDiffOn ℝ (⊤ : WithTop ℕ∞) f s)
    (hmaps : MapsTo f s t) :
    order ℝ g (f x) ≤ order ℝ (g ∘ f) x := by
  apply le_order_of_forall_iteratedFDeriv_eq_zero
  intro j hj
  have hfx_t : f x ∈ t := hmaps hx
  -- C = 0: all derivatives of `g` of order `≤ j` vanish at `f x` (since `j < order g (f x)`)
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ 0 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i ht hfx_t,
      iteratedFDeriv_eq_zero_of_lt_order (lt_of_le_of_lt (by exact_mod_cast hi) hj), norm_zero]
  -- D: a uniform bound on the derivatives of `f` up to order `j`
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D ^ i := by
    refine ⟨1 + ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ k f s x‖, ?_⟩
    intro i hi1 hij
    set D := 1 + ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ k f s x‖ with hDdef
    have hsum_nn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ k f s x‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    have hle : ‖iteratedFDerivWithin ℝ i f s x‖ ≤
        ∑ k ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ k f s x‖ :=
      Finset.single_le_sum (f := fun k => ‖iteratedFDerivWithin ℝ k f s x‖)
        (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
    have h1D : (1 : ℝ) ≤ D := by rw [hDdef]; linarith
    calc ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D := by rw [hDdef]; linarith
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ h1D hi1
  have hbound := norm_iteratedFDerivWithin_comp_le hg hf le_top ht.uniqueDiffOn hs.uniqueDiffOn
    hmaps hx hC hD
  rw [mul_zero, zero_mul] at hbound
  rw [iteratedFDerivWithin_of_isOpen j hs hx] at hbound
  exact norm_le_zero_iff.mp hbound

/-- **Order is invariant under a local analytic diffeomorphism.**
If `e : s → t` and `e' : t → s` are mutually inverse smooth maps between open sets
(`e' (e x) = x` and `e ∘ e' = id` on `t`), then `order (g ∘ e) x = order g (e x)`. -/
theorem order_comp_eq_of_diffeo
    {g : F → ℝ} {e : E → F} {e' : F → E} {s : Set E} {t : Set F} {x : E}
    (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hg : ContDiffOn ℝ (⊤ : WithTop ℕ∞) g t)
    (he : ContDiffOn ℝ (⊤ : WithTop ℕ∞) e s) (he' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) e' t)
    (hmaps : MapsTo e s t) (hmaps' : MapsTo e' t s)
    (hinv : e' (e x) = x) (hinv' : ∀ y ∈ t, e (e' y) = y) :
    order ℝ (g ∘ e) x = order ℝ g (e x) := by
  refine le_antisymm ?_ (order_le_order_comp hs ht hx hg he hmaps)
  have hge : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (g ∘ e) s := hg.comp he hmaps
  have h1 : order ℝ (g ∘ e) (e' (e x)) ≤ order ℝ ((g ∘ e) ∘ e') (e x) :=
    order_le_order_comp ht hs (hmaps hx) hge he' hmaps'
  rw [hinv] at h1
  have h2 : order ℝ ((g ∘ e) ∘ e') (e x) = order ℝ g (e x) := by
    apply order_congr_of_eventuallyEq
    filter_upwards [ht.mem_nhds (hmaps hx)] with y hy
    simp only [Function.comp_apply, hinv' y hy]
  rwa [h2] at h1

/-- **Order transfer through a chart.** For a partial homeomorphism `Φ` that is analytic on
its source, with `Φ.symm` analytic at `x ∈ Φ.target`, and `g` globally smooth, the vanishing
order is preserved: `order (g ∘ Φ.symm) x = order g (Φ.symm x)`.

This packages the open-set / mutual-inverse bookkeeping of `order_comp_eq_of_diffeo` for the
straightening chart, where `Φ.symm` is only known to be analytic at one point. -/
theorem order_comp_partialHomeomorph_symm [CompleteSpace E] [CompleteSpace F]
    (Φ : OpenPartialHomeomorph E F) (g : E → ℝ) (x : F)
    (hx : x ∈ Φ.target)
    (hΦ_an : ∀ z ∈ Φ.source, AnalyticAt ℝ (⇑Φ) z)
    (hΦsymm_an : AnalyticAt ℝ (⇑Φ.symm) x)
    (hg : ContDiff ℝ (⊤ : WithTop ℕ∞) g) :
    order ℝ (g ∘ Φ.symm) x = order ℝ g (Φ.symm x) := by
  obtain ⟨W, hW_sub, hW_open, hxW⟩ := eventually_nhds_iff.mp hΦsymm_an.eventually_analyticAt
  set s₀ := Φ.target ∩ W with hs₀def
  set t₀ := Φ.source ∩ Φ ⁻¹' W with ht₀def
  have hs₀_open : IsOpen s₀ := Φ.open_target.inter hW_open
  have ht₀_open : IsOpen t₀ := Φ.continuousOn.isOpen_inter_preimage Φ.open_source hW_open
  have hx_s₀ : x ∈ s₀ := ⟨hx, hxW⟩
  have hsymm_an : AnalyticOnNhd ℝ (⇑Φ.symm) s₀ := fun z hz => hW_sub z hz.2
  have hΦ_an' : AnalyticOnNhd ℝ (⇑Φ) t₀ := fun z hz => hΦ_an z hz.1
  have he : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (⇑Φ.symm) s₀ :=
    hsymm_an.contDiffOn hs₀_open.uniqueDiffOn
  have he' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (⇑Φ) t₀ :=
    hΦ_an'.contDiffOn ht₀_open.uniqueDiffOn
  have hmaps : MapsTo Φ.symm s₀ t₀ := fun z hz =>
    ⟨Φ.map_target hz.1, by show Φ (Φ.symm z) ∈ W; rw [Φ.right_inv hz.1]; exact hz.2⟩
  have hmaps' : MapsTo Φ t₀ s₀ := fun z hz => ⟨Φ.map_source hz.1, hz.2⟩
  exact order_comp_eq_of_diffeo hs₀_open ht₀_open hx_s₀ hg.contDiffOn he he' hmaps hmaps'
    (Φ.right_inv hx) (fun y hy => Φ.left_inv hy.1)

end
