import Cad.Multivariate.ProjectionTheorem.Puiseux.Conclusion2ValueE1
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic

/-!
# Conclusion 2, codim-1 — factorization assembly (Thm 4.2.3)

The axiom's Weierstrass polynomial `weierstrassPoly m a` need not be irreducible. This file assembles
the per-factor order constancy (`order_eval_value_e1_weierstrass` for each irreducible factor) into the
order constancy of the whole family, via the additivity `order(∏) = Σ order` (`order_mul_analytic`).
-/

noncomputable section

open Polynomial Filter Metric Set
open scoped Topology

namespace Puiseux

/-- **Additivity of the vanishing order over a finite product.** For finitely many functions analytic
at `x`, the order of their product is the sum of the orders. (Induction on the finset using the
two-factor `order_mul_analytic`.) -/
theorem order_finset_prod_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → E → ℂ) (x : E)
    (h_an : ∀ i ∈ s, AnalyticAt ℂ (h i) x) :
    order ℂ (fun z => ∏ i ∈ s, h i z) x = ∑ i ∈ s, order ℂ (h i) x := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact order_eq_zero_of_ne (fun _ => (1 : ℂ)) x one_ne_zero
  | @insert a s ha ih =>
    have ha_an : AnalyticAt ℂ (h a) x := h_an a (Finset.mem_insert_self a s)
    have hs_an : ∀ i ∈ s, AnalyticAt ℂ (h i) x := fun i hi => h_an i (Finset.mem_insert_of_mem hi)
    have hprod_an : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) x :=
      Finset.analyticAt_fun_prod _ (fun i hi => hs_an i hi)
    rw [show (fun z => ∏ i ∈ insert a s, h i z) = fun z => h a z * ∏ i ∈ s, h i z from by
        funext z; rw [Finset.prod_insert ha],
      order_mul_analytic _ _ x ha_an hprod_an, ih hs_an, Finset.sum_insert ha]

/-- **Order of the family evaluation decomposes over an analytic factorization.** If `h = ∏ⱼ facⱼ`
near `w₀`, the multivariate order of `wt ↦ (h wt.1).eval wt.2` at `(w₀, x₀)` is the sum of the orders
of the factor evaluations. -/
theorem order_eval_eq_sum_factors {s e : ℕ} {h : CParam s e → Polynomial ℂ}
    {k : ℕ} {fac : Fin k → (CParam s e → Polynomial ℂ)} {w₀ : CParam s e} {x₀ : ℂ}
    (hfac_eq : ∀ᶠ w in 𝓝 w₀, h w = ∏ j, fac j w)
    (hfac_an : ∀ j, AnalyticAt ℂ (fun wt : CParam s e × ℂ => (fac j wt.1).eval wt.2) (w₀, x₀)) :
    order ℂ (fun wt : CParam s e × ℂ => (h wt.1).eval wt.2) (w₀, x₀)
      = ∑ j, order ℂ (fun wt : CParam s e × ℂ => (fac j wt.1).eval wt.2) (w₀, x₀) := by
  have heq : (fun wt : CParam s e × ℂ => (h wt.1).eval wt.2)
      =ᶠ[𝓝 (w₀, x₀)] fun wt => ∏ j, (fac j wt.1).eval wt.2 := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds hfac_eq] with wt hwt
    have hwt' : h wt.1 = ∏ j, fac j wt.1 := hwt
    show (h wt.1).eval wt.2 = ∏ j, (fac j wt.1).eval wt.2
    rw [hwt', eval_prod]
  rw [order_congr_of_eventuallyEq_C heq,
    order_finset_prod_analytic Finset.univ _ _ (fun j _ => hfac_an j)]

/-- **Eventual analyticity of a factor evaluation along the section.** The coefficients of a Weierstrass
family are analytic at `0`, hence analytic at `(y,0)` for `y` near `0`; the evaluation is a finite sum
of `coeffₖ · xᵏ`, so it is analytic at every section point `((y,0), ψ y)` for `y` near `0`. -/
theorem eval_analyticAt_section_eventually {s e : ℕ} {fac : CParam s e → Polynomial ℂ} {d : ℕ}
    (hfam : IsWeierstrassFamily fac d) (ψ : (Fin s → ℂ) → ℂ) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      AnalyticAt ℂ (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s e), ψ y) := by
  have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
    simpa using hc.tendsto' 0 0 (by simp)
  have hall : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ k ∈ Finset.range (d + 1),
      AnalyticAt ℂ (fun w => (fac w).coeff k) ((y, 0) : CParam s e) :=
    (eventually_all_finset _).mpr
      (fun k _ => hι.eventually (hfam.coeff_analyticAt k).eventually_analyticAt)
  filter_upwards [hall] with y hy
  rw [show (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2)
      = fun wt => ∑ k ∈ Finset.range (d + 1), (fac wt.1).coeff k * wt.2 ^ k from by
    funext wt; exact eval_eq_sum_range' (by rw [hfam.degree_eq]; omega) wt.2]
  exact Finset.analyticAt_fun_sum _ (fun k hk =>
    (AnalyticAt.comp (g := fun w => (fac w).coeff k) (f := fun wt : CParam s e × ℂ => wt.1)
      (hy k hk) analyticAt_fst).mul (analyticAt_snd.pow k))

open Polynomial in
/-- **Degree-one factor: the evaluation has order exactly `1` at its section root.** For a monic
degree-1 factor, the `x`-axis line restriction is the identity `t ↦ t` (order `1`), and the function
vanishes at the root, so the multivariate order is `1` (independent of the point — hence constant). -/
theorem order_eval_deg1 {s e : ℕ} {fac : CParam s e → Polynomial ℂ} {w₀ : CParam s e} {x₀ : ℂ}
    (hmonic : (fac w₀).Monic) (hdeg : (fac w₀).natDegree = 1) (hroot : (fac w₀).eval x₀ = 0)
    (han : AnalyticAt ℂ (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2) (w₀, x₀)) :
    order ℂ (fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2) (w₀, x₀) = 1 := by
  set g := fun wt : CParam s e × ℂ => (fac wt.1).eval wt.2 with hgdef
  have hlc : (fac w₀).coeff 1 = 1 := by have := hmonic.coeff_natDegree; rwa [hdeg] at this
  have hge : (1 : ℕ∞) ≤ order ℂ g (w₀, x₀) :=
    ENat.one_le_iff_ne_zero.mpr (order_ne_zero_of_eq_zero g (w₀, x₀) hroot)
  have hle : order ℂ g (w₀, x₀) ≤ 1 := by
    refine le_trans (order_le_line g (w₀, x₀) ((0 : CParam s e), (1 : ℂ)) han) (le_of_eq ?_)
    have hc0 : (fac w₀).coeff 0 + x₀ = 0 := by
      have hev : (fac w₀).eval x₀ = (fac w₀).coeff 0 + x₀ := by
        rw [eval_eq_sum_range' (n := 2) (by rw [hdeg]; omega), Finset.sum_range_succ,
          Finset.sum_range_one, hlc]; ring
      rw [hev] at hroot; exact hroot
    have hline : (fun t : ℂ => g ((w₀, x₀) + t • ((0 : CParam s e), (1 : ℂ)))) = fun t => t := by
      funext t
      simp only [hgdef, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, smul_eq_mul, mul_one]
      rw [eval_eq_sum_range' (n := 2) (by rw [hdeg]; omega), Finset.sum_range_succ,
        Finset.sum_range_one, hlc, pow_zero, pow_one, mul_one, one_mul]
      linear_combination hc0
    rw [hline]
    refine (analyticAt_id.analyticOrderAt_eq_natCast).mpr ⟨fun _ => 1, analyticAt_const,
      one_ne_zero, ?_⟩
    filter_upwards with t; simp
  exact le_antisymm hle hge

/-- **Thm 4.2.3 assembly — order constancy from per-factor constancy.** If `h = ∏ⱼ facⱼ` near `0`, the
factor evaluations are analytic at every section point, and each factor's evaluation order is constant
along the section, then so is `h`'s. (Sum of constants is constant.) -/
theorem order_eval_constant_of_factors {s e : ℕ} {h : CParam s e → Polynomial ℂ}
    {k : ℕ} {fac : Fin k → (CParam s e → Polynomial ℂ)} {ψ : (Fin s → ℂ) → ℂ}
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), h w = ∏ j, fac j w)
    (hfac_an : ∀ j, ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      AnalyticAt ℂ (fun wt : CParam s e × ℂ => (fac j wt.1).eval wt.2) (((y, 0) : CParam s e), ψ y))
    (hfac_const : ∀ j, ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s e × ℂ => (fac j wt.1).eval wt.2) (((y, 0) : CParam s e), ψ y)
        = order ℂ (fun wt : CParam s e × ℂ => (fac j wt.1).eval wt.2) (((0, 0) : CParam s e), ψ 0)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s e × ℂ => (h wt.1).eval wt.2) (((y, 0) : CParam s e), ψ y)
        = order ℂ (fun wt : CParam s e × ℂ => (h wt.1).eval wt.2) (((0, 0) : CParam s e), ψ 0) := by
  -- `h = ∏ facⱼ` propagates to a neighbourhood of each section point
  have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
    simpa using hc.tendsto' 0 0 (by simp)
  have hfac_eq_sec : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ᶠ w in 𝓝 ((y, 0) : CParam s e), h w = ∏ j, fac j w := hι.eventually hfac_eq.eventually_nhds
  -- the value at `0` decomposes
  have h0 : order ℂ (fun wt : CParam s e × ℂ => (h wt.1).eval wt.2) (((0, 0) : CParam s e), ψ 0)
      = ∑ j, order ℂ (fun wt : CParam s e × ℂ => (fac j wt.1).eval wt.2)
          (((0, 0) : CParam s e), ψ 0) :=
    order_eval_eq_sum_factors hfac_eq (fun j => (hfac_an j).self_of_nhds)
  filter_upwards [hfac_eq_sec, Filter.eventually_all.mpr hfac_an,
    Filter.eventually_all.mpr hfac_const] with y hy_eq hy_an hy_const
  rw [order_eval_eq_sum_factors hy_eq hy_an, h0]
  exact Finset.sum_congr rfl (fun j _ => hy_const j)

/-- **e = 0 degenerate case — vacuous.** For an irreducible Weierstrass factor of degree `d ≥ 2` over
`CParam s 0`, the discriminant hypotheses are contradictory: the transverse `Fin 0 → ℂ` is trivial, so
`hdisc_oi` makes `order D` constant on a full neighbourhood of `0`; since `D 0 = disc(Xᵈ) = 0` the order
is `≥ 1` everywhere, forcing `D ≡ 0` near `0` and `order D 0 = ⊤`, contradicting `hdisc_ne`. Mirrors
`irreducible_section_single_root_e0`. -/
theorem order_eval_value_e0 {s : ℕ} {fac : CParam s 0 → Polynomial ℂ} {d : ℕ} (hd : 2 ≤ d)
    (hfam : IsWeierstrassFamily fac d)
    (hdisc_ne : order ℂ (fun w => (fac w).discr) (0 : CParam s 0) ≠ ⊤)
    (hdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (fac w).discr) ((y, 0) : CParam s 0)
        = order ℂ (fun w => (fac w).discr) ((0, 0) : CParam s 0))
    (ψ : (Fin s → ℂ) → ℂ) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s 0 × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s 0), ψ y)
        = order ℂ (fun wt : CParam s 0 × ℂ => (fac wt.1).eval wt.2) (((0, 0) : CParam s 0), ψ 0) := by
  exfalso
  set D : CParam s 0 → ℂ := fun w => (fac w).discr with hD
  have hD0 : D 0 = 0 := by
    show (fac 0).discr = 0; rw [hfam.eval_zero]; exact discr_X_pow_eq_zero hd
  have hord_ne0 : order ℂ D 0 ≠ 0 := order_ne_zero_of_eq_zero D 0 hD0
  have hconst : ∀ᶠ w in 𝓝 (0 : CParam s 0), order ℂ D w = order ℂ D 0 := by
    have htend : Filter.Tendsto (fun w : CParam s 0 => w.1) (𝓝 0) (𝓝 (0 : Fin s → ℂ)) :=
      continuous_fst.tendsto 0
    filter_upwards [htend.eventually hdisc_oi] with w hw
    have hweq : ((w.1, (0 : Fin 0 → ℂ)) : CParam s 0) = w := by
      refine Prod.ext rfl ?_; exact Subsingleton.elim _ _
    rwa [hweq] at hw
  have hDvanish : ∀ᶠ w in 𝓝 (0 : CParam s 0), D w = 0 := by
    filter_upwards [hconst] with w hw
    by_contra hDw
    exact hord_ne0 (hw.symm.trans (order_eq_zero_of_ne D w hDw))
  have htop : order ℂ D 0 = ⊤ := by
    rw [order_congr_of_eventuallyEq' (hDvanish : D =ᶠ[𝓝 (0 : CParam s 0)] (fun _ => 0))]
    exact order_eq_top_iff.mpr (fun n => by simp [iteratedFDeriv_zero_fun])
  exact hdisc_ne htop

/-- **Per-factor order constancy (e = 1).** For a single irreducible Weierstrass factor over
`CParam s 1` (degree `d ≥ 1`) with finite, section-constant discriminant order and single section root
`ψ`, the evaluation order is constant along the section. Dispatches `d = 1` (order `1`, `order_eval_deg1`)
and `d ≥ 2` (`order_eval_value_e1_weierstrass`). -/
theorem order_eval_constant_factor_e1 {s : ℕ} {fac : CParam s 1 → Polynomial ℂ} {d : ℕ} (hd : 1 ≤ d)
    (hfam : IsWeierstrassFamily fac d) (hirr : WeierstrassIrreducible fac d)
    (hdisc_ne : order ℂ (fun w => (fac w).discr) (0 : CParam s 1) ≠ ⊤)
    (hdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (fac w).discr) ((y, 0) : CParam s 1)
        = order ℂ (fun w => (fac w).discr) ((0, 0) : CParam s 1))
    {ψ : (Fin s → ℂ) → ℂ} (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (fac ((y, 0) : CParam s 1)).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s 1 × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s 1), ψ y)
        = order ℂ (fun wt : CParam s 1 × ℂ => (fac wt.1).eval wt.2) (((0, 0) : CParam s 1), ψ 0) := by
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have hd1' : d = 1 := by omega
    have h1 : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun wt : CParam s 1 × ℂ => (fac wt.1).eval wt.2) (((y, 0) : CParam s 1), ψ y) = 1 := by
      filter_upwards [hψ_root, eval_analyticAt_section_eventually hfam ψ] with y hsy han
      refine order_eval_deg1 (hfam.monic _) (by rw [hfam.degree_eq]; exact hd1') ?_ han
      exact Polynomial.IsRoot.def.mp ((hsy (ψ y)).mpr rfl)
    filter_upwards [h1] with y hy; rw [hy, h1.self_of_nhds]
  · exact order_eval_value_e1_weierstrass fac d hd2 hfam hirr hdisc_ne hdisc_oi ψ hψ_an hψ_root

/-- **Each irreducible factor inherits the single section root `ψ`.** If `weierstrassPoly = ∏ⱼ facⱼ`
near `0` and the product's section polynomial has unique root `ψ y`, then so does each factor: a root of
`facⱼ` is a root of the product (hence `= ψ y`), and `facⱼ(y,0)` (monic, degree `≥ 1`, over `ℂ`) has at
least one root, which must be `ψ y`. -/
theorem factor_single_root_of_prod {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    {k : ℕ} {deg : Fin k → ℕ} {fac : Fin k → (CParam s e → Polynomial ℂ)}
    (hdeg1 : ∀ j, 1 ≤ deg j) (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j, fac j w)
    {ψ : (Fin s → ℂ) → ℂ}
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) (j : Fin k) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (fac j ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y := by
  have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
    simpa using hc.tendsto' 0 0 (by simp)
  filter_upwards [hψ_root, hι.eventually hfac_eq] with y hsy hprod α
  have hroot_prod : ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β →
      (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot β := by
    intro β hβ
    rw [Polynomial.IsRoot.def, hprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hβ
  constructor
  · intro hαj; exact (hsy α).mp (hroot_prod α hαj)
  · intro hα; subst hα
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (p := fac j ((y, 0) : CParam s e)) (by
      rw [Polynomial.degree_eq_natDegree ((hfac_fam j).monic _).ne_zero, (hfac_fam j).degree_eq]
      exact_mod_cast Nat.one_le_iff_ne_zero.mp (hdeg1 j))
    have hβψ : β = ψ y := (hsy β).mp (hroot_prod β hβ)
    rwa [← hβψ]

/-- **Zariski 4.1.1 Conclusion (2), codimension 1 — order-invariance in the graph, FULLY DISCHARGED
for `e = 1`.** The axiom-shaped order constancy for `weierstrassPoly m a` over `CParam s 1`: factor into
irreducible Weierstrass polynomials (`weierstrass_irreducible_factorization`), each with the common
single section root `ψ` (`factor_single_root_of_prod`) and section-constant discriminant order
(`factor_disc_order_inv`, or germ equality for a single factor); each factor's evaluation order is
constant (`order_eval_constant_factor_e1`); then `order_eval_constant_of_factors` sums them. -/
theorem order_invariant_in_graph_e1 {s : ℕ} (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s 1 → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s 1) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s 1)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s 1))
    (ψ : (Fin s → ℂ) → ℂ) (hψ_an : AnalyticAt ℂ ψ 0)
    (hψ_root : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (weierstrassPoly m a ((y, 0) : CParam s 1)).IsRoot α ↔ α = ψ y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun wt : CParam s 1 × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
          (((y, 0) : CParam s 1), ψ y)
        = order ℂ (fun wt : CParam s 1 × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
          (((0, 0) : CParam s 1), ψ 0) := by
  obtain ⟨k, deg, fac, hk, hdeg1, hfac_fam, hfac_irr, hfac_eq⟩ :=
    weierstrass_irreducible_factorization (weierstrassPoly m a) m
      (weierstrassPoly_isWeierstrassFamily m a ha_an ha0) hm_pos
  refine order_eval_constant_of_factors hfac_eq
    (fun j => eval_analyticAt_section_eventually (hfac_fam j) ψ) ?_
  intro j
  have hDj : order ℂ (fun w => (fac j w).discr) (0 : CParam s 1) ≠ ⊤ ∧
      ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s 1)
          = order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s 1) := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hk1' : k = 1 := by omega
      subst hk1'
      have hj0 : j = 0 := Subsingleton.elim j 0
      have hfe : ∀ᶠ w in 𝓝 (0 : CParam s 1), weierstrassPoly m a w = fac j w := by
        filter_upwards [hfac_eq] with w hw; rw [hw, hj0, Fin.prod_univ_one]
      have hgerm_base : order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s 1)
          = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s 1) :=
        order_congr_of_eventuallyEq' (by
          filter_upwards [hfe] with w hw
          show (fac j w).discr = (weierstrassPoly m a w).discr; rw [hw])
      refine ⟨?_, ?_⟩
      · rw [show ((0 : CParam s 1)) = ((0, 0) : CParam s 1) from rfl, hgerm_base]; exact hdisc_ne
      · have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s 1)) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s 1)) := by fun_prop
          simpa using hc.tendsto' 0 0 (by simp)
        have hsec_germ : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
            ∀ᶠ w' in 𝓝 ((y, 0) : CParam s 1), weierstrassPoly m a w' = fac j w' :=
          hι.eventually hfe.eventually_nhds
        filter_upwards [hdisc, hsec_germ] with y hy_disc hy_germ
        have e1 : order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s 1)
            = order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s 1) :=
          order_congr_of_eventuallyEq' (by
            filter_upwards [hy_germ] with w' hw'
            show (fac j w').discr = (weierstrassPoly m a w').discr; rw [hw'])
        rw [e1, hy_disc]; exact hgerm_base.symm
    · exact factor_disc_order_inv m a hdisc_ne hdisc k deg fac hfac_fam hdeg1 hfac_eq j hk2
  exact order_eval_constant_factor_e1 (hdeg1 j) (hfac_fam j) (hfac_irr j) hDj.1 hDj.2 hψ_an
    (factor_single_root_of_prod m a hdeg1 hfac_fam hfac_eq hψ_root j)

end Puiseux
