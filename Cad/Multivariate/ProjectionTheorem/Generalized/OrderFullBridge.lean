import Cad.Multivariate.ProjectionTheorem.OrderComp
import Cad.Multivariate.ProjectionTheorem.Invariance
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# `orderFull` as a section-family order, through a straightening chart (L_bridge)

The codim order-invariance conclusion is phrased with `orderFull f a y = polyOrder (n+1) (toMvPoly f)
(Fin.cons y a)` — McCallum's multivariate order of the **full** `(n+1)`-variable `f`. The
Weierstrass/Zariski transport, however, lives on the **section family** `g(w) = specialize f (Φ.symm w)`
(a polynomial in the transverse variable `t`). This file bridges the two:

* `orderFull_eq_order_section` — `orderFull f a t = order ℝ ((w,t) ↦ (specialize f w).eval t) (a, t)`,
  a pure `Fin.cons` change of variables (the linear diffeo `(a,t) ↦ Fin.cons t a`).
* `orderFull_eq_order_section_chart` — composes the above with the straightening chart `Φ` on the base
  coordinate, landing on the section family `w ↦ (specialize f (Φ.symm w)).eval t` at the chart point.

Both are proved from `order_comp_eq_of_diffeo` (order is a local analytic invariant); no new axioms.
-/

noncomputable section

open MvPolynomial Polynomial Set Filter
open scoped Topology

variable {n : ℕ}

/-- `(specialize g a).eval y = (toMvPoly g)` evaluated at `Fin.cons y a` (re-derivation of the
private helper in `OrderInvariantFactor`). -/
private lemma eval_specialize_eq (g : PolyR n) (a : Fin n → ℝ) (y : ℝ) :
    (specialize g a).eval y = MvPolynomial.eval (Fin.cons y a) (toMvPoly g) := by
  simp only [specialize, toMvPoly]
  rw [MvPolynomial.eval_eq_eval_mv_eval',
    (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply g]

/-- `v ↦ eval v (toMvPoly f)` is smooth. -/
private lemma contDiff_mvEval (g : MvPolynomial (Fin (n + 1)) ℝ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun v => MvPolynomial.eval v g) :=
  (show AnalyticOnNhd ℝ (fun v => MvPolynomial.eval v g) univ from
    fun v hv => AnalyticOnNhd.eval_mvPolynomial g v hv).contDiff

/-- The `Fin.cons` map `(a, t) ↦ Fin.cons t a` is smooth. -/
private lemma contDiff_finCons :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)) := by
  rw [contDiff_pi]; intro i
  refine Fin.cases ?_ ?_ i
  · exact contDiff_snd
  · intro j; exact (contDiff_pi.mp contDiff_id j).comp contDiff_fst

/-- The inverse `v ↦ (Fin.tail v, v 0)` of the `Fin.cons` map is smooth. -/
private lemma contDiff_finUncons :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun v : Fin (n + 1) → ℝ => ((Fin.tail v : Fin n → ℝ), v 0)) := by
  refine ContDiff.prodMk ?_ ?_
  · rw [contDiff_pi]; intro j; exact contDiff_pi.mp contDiff_id j.succ
  · exact contDiff_pi.mp contDiff_id 0

/-- **L_bridge (cons change of variables).** McCallum's order `orderFull f a t` of the full
`(n+1)`-variable polynomial equals the vanishing order of the section-family evaluation
`(a, t) ↦ (specialize f a).eval t` at `(a, t)`. The map `(a,t) ↦ Fin.cons t a` is a global analytic
diffeomorphism, so order is preserved (`order_comp_eq_of_diffeo`). -/
theorem orderFull_eq_order_section (f : PolyR n) (a : Fin n → ℝ) (t : ℝ) :
    orderFull f a t
      = order ℝ (fun p : (Fin n → ℝ) × ℝ => (specialize f p.1).eval p.2) (a, t) := by
  set H : (Fin (n + 1) → ℝ) → ℝ := fun v => MvPolynomial.eval v (toMvPoly f) with hH
  set e : (Fin n → ℝ) × ℝ → (Fin (n + 1) → ℝ) := fun p => Fin.cons p.2 p.1 with he
  set e' : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ := fun v => (Fin.tail v, v 0) with he'
  have hHe : (fun p : (Fin n → ℝ) × ℝ => (specialize f p.1).eval p.2) = H ∘ e := by
    funext p; exact eval_specialize_eq f p.1 p.2
  have hcomp := order_comp_eq_of_diffeo (g := H) (e := e) (e' := e')
    (s := univ) (t := univ) (x := (a, t))
    isOpen_univ isOpen_univ (mem_univ _)
    (contDiff_mvEval (toMvPoly f)).contDiffOn
    contDiff_finCons.contDiffOn contDiff_finUncons.contDiffOn
    (mapsTo_univ _ _) (mapsTo_univ _ _)
    (by simp [e, e', Fin.tail_cons, Fin.cons_zero])
    (fun y _ => by simp [e, e', Fin.cons_self_tail])
  rw [hHe, hcomp]
  rfl

/-- **L_bridge (full real transport).** Composing the `Fin.cons` change of variables with a
straightening chart `Φ` (analytic on its source, with analytic inverse at `w`), McCallum's order
`orderFull f (Φ.symm w) t` of the full polynomial at the chart point equals the vanishing order of
the **section family** `q ↦ (specialize f (Φ.symm q.1)).eval q.2` at `(w, t)`. This lands the
order-invariance question on the section family `g(w) = specialize f (Φ.symm w)` — exactly the object
the Weierstrass/Zariski transport produces. Proved by `order_comp_eq_of_diffeo` applied to the product
diffeomorphism `(w, t) ↦ (Φ.symm w, t)` (mirroring `order_comp_partialHomeomorph_symm`, with the
extra transverse coordinate carried along by the identity). -/
theorem orderFull_eq_order_section_chart {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : PolyR n) (Φ : OpenPartialHomeomorph (Fin n → ℝ) B)
    (w : B) (t : ℝ) (hw : w ∈ Φ.target)
    (hΦ_an : ∀ z ∈ Φ.source, AnalyticAt ℝ (⇑Φ) z)
    (hΦsymm_an : AnalyticAt ℝ (⇑Φ.symm) w) :
    orderFull f (Φ.symm w) t
      = order ℝ (fun q : B × ℝ => (specialize f (Φ.symm q.1)).eval q.2) (w, t) := by
  rw [orderFull_eq_order_section f (Φ.symm w) t]
  set Gsec : (Fin n → ℝ) × ℝ → ℝ := fun p => (specialize f p.1).eval p.2 with hGsec
  have hGsec_cd : ContDiff ℝ (⊤ : WithTop ℕ∞) Gsec := by
    have hcompeq : Gsec
        = (fun v => MvPolynomial.eval v (toMvPoly f)) ∘ (fun p => Fin.cons p.2 p.1) := by
      funext p; exact eval_specialize_eq f p.1 p.2
    rw [hcompeq]; exact (contDiff_mvEval (toMvPoly f)).comp contDiff_finCons
  obtain ⟨W, hW_sub, hW_open, hwW⟩ := eventually_nhds_iff.mp hΦsymm_an.eventually_analyticAt
  set e : B × ℝ → (Fin n → ℝ) × ℝ := fun q => (Φ.symm q.1, q.2) with he
  set e' : (Fin n → ℝ) × ℝ → B × ℝ := fun p => (Φ p.1, p.2) with he'
  set s₀ : Set (B × ℝ) := (Φ.target ∩ W) ×ˢ univ with hs₀
  set t₀ : Set ((Fin n → ℝ) × ℝ) := (Φ.source ∩ Φ ⁻¹' W) ×ˢ univ with ht₀
  have hs₀_open : IsOpen s₀ := (Φ.open_target.inter hW_open).prod isOpen_univ
  have ht₀_open : IsOpen t₀ :=
    (Φ.continuousOn.isOpen_inter_preimage Φ.open_source hW_open).prod isOpen_univ
  have hx_s₀ : (w, t) ∈ s₀ := ⟨⟨hw, hwW⟩, mem_univ _⟩
  have he_an : AnalyticOnNhd ℝ e s₀ := fun z hz =>
    ((hW_sub z.1 hz.1.2).comp analyticAt_fst).prod analyticAt_snd
  have he'_an : AnalyticOnNhd ℝ e' t₀ := fun z hz =>
    ((hΦ_an z.1 hz.1.1).comp analyticAt_fst).prod analyticAt_snd
  have he_cd : ContDiffOn ℝ (⊤ : WithTop ℕ∞) e s₀ := he_an.contDiffOn hs₀_open.uniqueDiffOn
  have he'_cd : ContDiffOn ℝ (⊤ : WithTop ℕ∞) e' t₀ := he'_an.contDiffOn ht₀_open.uniqueDiffOn
  have hmaps : MapsTo e s₀ t₀ := fun z hz =>
    ⟨⟨Φ.map_target hz.1.1, by
        show Φ (Φ.symm z.1) ∈ W; rw [Φ.right_inv hz.1.1]; exact hz.1.2⟩, mem_univ _⟩
  have hmaps' : MapsTo e' t₀ s₀ := fun z hz => ⟨⟨Φ.map_source hz.1.1, hz.1.2⟩, mem_univ _⟩
  have hcomp := order_comp_eq_of_diffeo (g := Gsec) (e := e) (e' := e')
    hs₀_open ht₀_open hx_s₀ hGsec_cd.contDiffOn he_cd he'_cd hmaps hmaps'
    (by show (Φ (Φ.symm w), t) = (w, t); rw [Φ.right_inv hw])
    (fun z hz => by show (Φ.symm (Φ z.1), z.2) = z; rw [Φ.left_inv hz.1.1])
  rw [← hcomp]
  rfl

/-- **Section-family order is `1` at a simple root.** For a real polynomial family `g` with analytic
coefficients (degree `≤ Ng`), if `t₀` is a *simple* root of `g w₀` (`g w₀` vanishes, its derivative
does not), then the multivariate vanishing order of the section evaluation `(w, t) ↦ (g w).eval t` at
`(w₀, t₀)` is exactly `1`. This is the separable-case order-invariance value (all branches simple ⟹
order `≡ 1`), the analogue of `orderFull_eq_one_of_simple_root` for an abstract section family. -/
theorem order_section_eq_one_of_simple {s e : ℕ}
    (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (Ng : ℕ)
    (hg_deg : ∀ w, (g w).natDegree ≤ Ng)
    (w₀ : (Fin s → ℝ) × (Fin e → ℝ)) (t₀ : ℝ)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) w₀)
    (hroot : (g w₀).IsRoot t₀)
    (hsimple : (Polynomial.derivative (g w₀)).eval t₀ ≠ 0) :
    order ℝ (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ => (g q.1).eval q.2) (w₀, t₀) = 1 := by
  set G : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ → ℝ := fun q => (g q.1).eval q.2 with hG
  -- `G` is analytic (hence differentiable) at `(w₀, t₀)`
  have hG_an : AnalyticAt ℝ G (w₀, t₀) := by
    have hsum : AnalyticAt ℝ
        (fun q : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ =>
          ∑ i ∈ Finset.range (Ng + 1), (g q.1).coeff i * q.2 ^ i) (w₀, t₀) := by
      apply Finset.analyticAt_fun_sum; intro i _
      exact ((hcoeff i).comp_of_eq analyticAt_fst rfl).mul (analyticAt_snd.pow i)
    refine hsum.congr (Filter.Eventually.of_forall fun q => ?_)
    exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hg_deg q.1)) q.2).symm
  -- the `t`-partial of `G` at `(w₀, t₀)` is `(g w₀)'.eval t₀ ≠ 0`, so `fderiv G ≠ 0`
  have hF_diff : DifferentiableAt ℝ G (w₀, t₀) := hG_an.differentiableAt
  have hpartial : fderiv ℝ G (w₀, t₀) (0, 1) = (Polynomial.derivative (g w₀)).eval t₀ := by
    have hderiv : HasDerivAt (fun t => G (w₀, t)) ((Polynomial.derivative (g w₀)).eval t₀) t₀ :=
      (g w₀).hasDerivAt t₀
    have hι : DifferentiableAt ℝ (fun t : ℝ => ((w₀ : (Fin s → ℝ) × (Fin e → ℝ)), t)) t₀ :=
      (differentiableAt_const _).prodMk differentiableAt_id
    have hfk : fderiv ℝ (fun t => G (w₀, t)) t₀ 1 = (Polynomial.derivative (g w₀)).eval t₀ := by
      rw [hderiv.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        one_mul]
    have hchain : fderiv ℝ (fun t => G (w₀, t)) t₀ =
        (fderiv ℝ G (w₀, t₀)).comp
          (fderiv ℝ (fun t : ℝ => ((w₀ : (Fin s → ℝ) × (Fin e → ℝ)), t)) t₀) :=
      (hF_diff.hasFDerivAt.comp t₀ hι.hasFDerivAt).fderiv
    have hι_k : fderiv ℝ (fun t : ℝ => ((w₀ : (Fin s → ℝ) × (Fin e → ℝ)), t)) t₀ 1 = (0, 1) := by
      have hfd : HasFDerivAt (fun t : ℝ => ((w₀ : (Fin s → ℝ) × (Fin e → ℝ)), t))
          ((0 : ℝ →L[ℝ] (Fin s → ℝ) × (Fin e → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)) t₀ :=
        (hasFDerivAt_const w₀ t₀).prodMk (hasFDerivAt_id t₀)
      rw [hfd.fderiv]; simp
    calc fderiv ℝ G (w₀, t₀) (0, 1)
        = fderiv ℝ G (w₀, t₀)
            (fderiv ℝ (fun t : ℝ => ((w₀ : (Fin s → ℝ) × (Fin e → ℝ)), t)) t₀ 1) := by rw [hι_k]
      _ = fderiv ℝ (fun t => G (w₀, t)) t₀ 1 := by rw [hchain]; rfl
      _ = (Polynomial.derivative (g w₀)).eval t₀ := hfk
  have hfderiv_ne : fderiv ℝ G (w₀, t₀) ≠ 0 := by
    intro h
    apply hsimple
    rw [← hpartial, h, ContinuousLinearMap.zero_apply]
  -- assemble `order = 1`
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, order_eq_natCast_iff]
  refine ⟨fun m hm => ?_, ?_⟩
  · interval_cases m
    ext v
    simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply]
    show G (w₀, t₀) = 0
    exact hroot
  · intro hzero
    have h1 := iteratedFDeriv_one_apply (𝕜 := ℝ) (f := G) (x := (w₀, t₀))
      (fun _ : Fin 1 => ((0 : (Fin s → ℝ) × (Fin e → ℝ)), (1 : ℝ)))
    simp only [hzero, ContinuousMultilinearMap.zero_apply] at h1
    rw [hpartial] at h1
    exact hsimple h1.symm

end
