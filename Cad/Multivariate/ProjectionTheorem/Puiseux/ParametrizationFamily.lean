import Cad.Multivariate.ProjectionTheorem.Puiseux.Parametrization
import Cad.Multivariate.ProjectionTheorem.Generalized.MonodromyGen

/-!
# Lemma 4.2.6 (Newton–Puiseux parametrization) — the `s ≥ 1` family case

We extend the `s = 0` construction (`Cad.Multivariate.ProjectionTheorem.Puiseux.Parametrization`) to a section parameter `z`.
The base is `Fin (n+1) → ℂ` with the **transverse** coordinate at index `0` (matching
`rootCover_pathConnected_gen`) and the **section** at indices `1 … n`. The universal-cover domain is the
*product* `(z-ball) × (half-plane)`; over a product punctured region `U` the fundamental group is `ℤ`
(only the transverse loop survives), so the global path-connectedness of the cover already gives the
per-slice orbit-covers-fibre needed for the period.

This file begins with the product domain and the parametrized base map `ptOfF (z,τ) = cons (exp τ) z`.
-/

noncomputable section

open Filter Topology Complex Polynomial
open scoped Real

namespace Puiseux

variable {n : ℕ}

/-- The universal-cover domain for the family: `(z-ball of radius δz) × (half-plane {Re τ < c})`,
a product of convex sets, hence contractible and simply connected. -/
def prodDom (n : ℕ) (δz c : ℝ) : Set ((Fin n → ℂ) × ℂ) :=
  Metric.ball (0 : Fin n → ℂ) δz ×ˢ halfPlane c

lemma isOpen_prodDom (δz c : ℝ) : IsOpen (prodDom n δz c) :=
  Metric.isOpen_ball.prod (isOpen_halfPlane c)

lemma convex_prodDom (δz c : ℝ) : Convex ℝ (prodDom n δz c) :=
  (convex_ball _ _).prod (convex_halfPlane c)

lemma prodDom_nonempty {δz : ℝ} (hδz : 0 < δz) (c : ℝ) : (prodDom n δz c).Nonempty :=
  ⟨(0, ((c - 1 : ℝ) : ℂ)), Set.mk_mem_prod (Metric.mem_ball_self hδz)
    (by simp only [halfPlane, Set.mem_setOf_eq, Complex.ofReal_re]; linarith)⟩

instance instLocPathConnected_prodDom (δz c : ℝ) :
    LocPathConnectedSpace (prodDom n δz c) :=
  (isOpen_prodDom δz c).locPathConnectedSpace

lemma simplyConnected_prodDom {δz : ℝ} (hδz : 0 < δz) (c : ℝ) :
    SimplyConnectedSpace (prodDom n δz c) :=
  haveI : ContractibleSpace (prodDom n δz c) :=
    (convex_prodDom δz c).contractibleSpace (prodDom_nonempty hδz c)
  SimplyConnectedSpace.ofContractible _

/-- The base point of `Fin (n+1) → ℂ` from a domain point `(z, τ)`: transverse `exp τ` at index `0`,
section `z` at indices `1 … n`. -/
def ptOfF (n : ℕ) (p : (Fin n → ℂ) × ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons (Complex.exp p.2) p.1

@[simp] lemma ptOfF_zero (p : (Fin n → ℂ) × ℂ) : ptOfF n p 0 = Complex.exp p.2 :=
  Fin.cons_zero _ _

@[simp] lemma ptOfF_succ (p : (Fin n → ℂ) × ℂ) (i : Fin n) : ptOfF n p i.succ = p.1 i :=
  Fin.cons_succ _ _ _

lemma continuous_ptOfF : Continuous (ptOfF n) := by
  refine continuous_pi (fun j => ?_)
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [ptOfF_zero]; exact Complex.continuous_exp.comp continuous_snd
  · simp only [ptOfF_succ]; exact (continuous_apply i).comp continuous_fst

lemma analyticAt_ptOfF (p : (Fin n → ℂ) × ℂ) : AnalyticAt ℂ (ptOfF n) p := by
  rw [analyticAt_pi_iff]
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · have h : (fun p : (Fin n → ℂ) × ℂ => ptOfF n p 0) = fun p => Complex.exp p.2 := by
      funext p; exact ptOfF_zero p
    rw [h]
    exact analyticAt_cexp.comp ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt p)
  · have h : (fun p : (Fin n → ℂ) × ℂ => ptOfF n p i.succ) = fun p => p.1 i := by
      funext p; exact ptOfF_succ p i
    rw [h]
    exact ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).analyticAt p

/-- `exp` of the transverse coordinate is nonzero and small for domain points. -/
lemma ptOfF_zero_mem {δz c : ℝ} {p : (Fin n → ℂ) × ℂ} (hp : p ∈ prodDom n δz c) :
    ptOfF n p 0 ≠ 0 ∧ ‖ptOfF n p 0‖ < Real.exp c := by
  rw [ptOfF_zero]
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.mpr hp.2

/-- The section coordinates of a domain point stay in the `z`-ball. -/
lemma ptOfF_section_norm {δz c : ℝ} {p : (Fin n → ℂ) × ℂ} (hp : p ∈ prodDom n δz c) :
    ‖p.1‖ < δz := by
  have := hp.1; rwa [Metric.mem_ball, dist_zero_right] at this

/-- The product punctured base region: transverse (coord `0`) in the punctured disc, section bounded. -/
def baseU (n : ℕ) (δz c : ℝ) : Set (Fin (n + 1) → ℂ) :=
  {y | 0 < ‖y 0‖ ∧ ‖y 0‖ < Real.exp c ∧ ‖Fin.tail y‖ < δz}

lemma ptOfF_mem_baseU {δz c : ℝ} {p : (Fin n → ℂ) × ℂ} (hp : p ∈ prodDom n δz c) :
    ptOfF n p ∈ baseU n δz c := by
  refine ⟨?_, (ptOfF_zero_mem hp).2, ?_⟩
  · rw [ptOfF_zero]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  · rw [show Fin.tail (ptOfF n p) = p.1 from Fin.tail_cons _ _]
    exact ptOfF_section_norm hp

/-- **Joint analyticity of the family root section.** A continuous root section over the product domain
is jointly analytic in `(z, τ)` (via the `W`-general `analyticAt_continuous_root` with `W = (Fin n→ℂ)×ℂ`,
`g = ptOfF`). -/
theorem analyticOn_root_family (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {δz c : ℝ}
    (hanaU : ∀ i, ∀ y ∈ baseU n δz c, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hsep : ∀ y ∈ baseU n δz c, (q y).Separable)
    {ρ : (Fin n → ℂ) × ℂ → ℂ} (hcont : ContinuousOn ρ (prodDom n δz c))
    (hroot : ∀ p ∈ prodDom n δz c, (q (ptOfF n p)).eval (ρ p) = 0) :
    ∀ p ∈ prodDom n δz c, AnalyticAt ℂ ρ p := by
  intro p hp
  refine analyticAt_continuous_root q m hmonic hdeg (analyticAt_ptOfF p)
    (fun i => hanaU i _ (ptOfF_mem_baseU hp))
    (hsep (ptOfF n p) (ptOfF_mem_baseU hp))
    (hcont.continuousAt ((isOpen_prodDom δz c).mem_nhds hp)) ?_
  filter_upwards [(isOpen_prodDom δz c).mem_nhds hp] with p' hp'
  exact hroot p' hp'

/-- The homeomorphism `(Fin (n+1) → ℂ) ≃ₜ ℂ × (Fin n → ℂ)` splitting off coordinate `0`. -/
def consHomeo (n : ℕ) : (Fin (n + 1) → ℂ) ≃ₜ ℂ × (Fin n → ℂ) where
  toFun y := (y 0, Fin.tail y)
  invFun p := Fin.cons p.1 p.2
  left_inv y := Fin.cons_self_tail y
  right_inv p := by simp only [Fin.cons_zero, Fin.tail_cons]
  continuous_toFun := by
    refine Continuous.prodMk (continuous_apply 0) (continuous_pi fun i => ?_)
    exact continuous_apply i.succ
  continuous_invFun := by
    refine continuous_pi fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; exact continuous_fst
    · simp only [Fin.cons_succ]; exact (continuous_apply i).comp continuous_snd

@[simp] lemma consHomeo_apply (y : Fin (n + 1) → ℂ) : consHomeo n y = (y 0, Fin.tail y) := rfl

lemma baseU_eq_preimage (δz c : ℝ) :
    baseU n δz c = consHomeo n ⁻¹' ((Metric.ball (0 : ℂ) (Real.exp c) \ {0}) ×ˢ
      Metric.ball (0 : Fin n → ℂ) δz) := by
  ext y
  simp only [baseU, Set.mem_setOf_eq, consHomeo_apply,
    Set.mem_preimage, Set.mem_prod, Set.mem_diff, Metric.mem_ball, dist_zero_right,
    Set.mem_singleton_iff, norm_pos_iff]
  tauto

lemma isOpen_baseU (δz c : ℝ) : IsOpen (baseU n δz c) := by
  rw [baseU_eq_preimage]
  exact (consHomeo n).continuous.isOpen_preimage _
    ((Metric.isOpen_ball.sdiff isClosed_singleton).prod Metric.isOpen_ball)

lemma isPreconnected_baseU {δz : ℝ} (c : ℝ) : IsPreconnected (baseU n δz c) := by
  rw [baseU_eq_preimage, (consHomeo n).isPreconnected_preimage]
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two
  exact (isPathConnected_ball_diff_singleton hrank (Real.exp_pos c)).isConnected.isPreconnected.prod
    (convex_ball _ _).isPreconnected

lemma baseU_mem_nhdsWithin {δz : ℝ} (hδz : 0 < δz) (c : ℝ) :
    baseU n δz c ∈ 𝓝[{x : Fin (n + 1) → ℂ | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ) := by
  have ht : {y : Fin (n + 1) → ℂ | ‖y 0‖ < Real.exp c ∧ ‖Fin.tail y‖ < δz} ∈
      𝓝 (0 : Fin (n + 1) → ℂ) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt ((continuous_apply 0).norm) continuous_const).inter
        (isOpen_lt (continuous_pi (fun i => (continuous_apply i.succ))).norm continuous_const)
    · refine ⟨?_, ?_⟩
      · show ‖(0 : Fin (n + 1) → ℂ) 0‖ < Real.exp c
        simp only [Pi.zero_apply, norm_zero]; exact Real.exp_pos c
      · show ‖Fin.tail (0 : Fin (n + 1) → ℂ)‖ < δz
        rw [show Fin.tail (0 : Fin (n + 1) → ℂ) = 0 from by funext i; rfl, norm_zero]; exact hδz
  have := inter_mem_nhdsWithin {x : Fin (n + 1) → ℂ | x 0 ≠ 0} ht
  refine Filter.mem_of_superset this ?_
  intro y hy
  exact ⟨norm_pos_iff.mpr hy.1, hy.2.1, hy.2.2⟩

/-- The `τ`-shift on the product domain (section fixed, transverse shifted by an imaginary `T`). -/
def shiftHPF (δz c : ℝ) (T : ℂ) (hT : T.re = 0) :
    C(↥(prodDom n δz c), ↥(prodDom n δz c)) where
  toFun p := ⟨(p.val.1, p.val.2 + T), ⟨p.property.1, by
    show (p.val.2 + T).re < c
    rw [Complex.add_re, hT, add_zero]; exact p.property.2⟩⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).add continuous_const)).subtype_mk _

/-- **Orbit covers the fibre (family transitivity).** With a product punctured base `U`, the loop's
transverse coordinate lifts via `exp` (staying in the half-plane) while the section `Fin.tail ℓ` is
carried in the `z`-ball; `cons_self_tail` recombines them, so every fibre point over `p (F a₀)` is a
*transverse* shift `F (z₀, τ₀ + k·2πi)`. -/
theorem family_lift_orbit {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    {δz c : ℝ} {p : E → ↥(baseU n δz c)} (cov : IsCoveringMap p)
    (F : C(↥(prodDom n δz c), E))
    (hF : ∀ pt : ↥(prodDom n δz c), ((p (F pt)).val : Fin (n + 1) → ℂ) = ptOfF n pt.val)
    (a₀ : ↥(prodDom n δz c)) {e' : E} (he' : p e' = p (F a₀)) :
    ∃ k : ℤ, ∃ h : (a₀.val.1, a₀.val.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I)) ∈ prodDom n δz c,
      F ⟨(a₀.val.1, a₀.val.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I)), h⟩ = e' := by
  classical
  set baseC : ↥(baseU n δz c) → {z : ℂ // z ≠ 0} :=
    fun y => ⟨y.val 0, norm_pos_iff.mp y.property.1⟩ with hbaseC
  have hbaseC_cont : Continuous baseC :=
    ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _
  let δp : Path (F a₀) e' := PathConnectedSpace.somePath (F a₀) e'
  let bℓ : C(unitInterval, ↥(baseU n δz c)) :=
    (⟨p, cov.continuous⟩ : C(E, _)).comp δp.toContinuousMap
  let ℓ : C(unitInterval, {z : ℂ // z ≠ 0}) := (⟨baseC, hbaseC_cont⟩ : C(_, _)).comp bℓ
  have hℓ0 : ℓ 0 = Complex.expNeZero a₀.val.2 := by
    apply Subtype.ext
    show (p (δp 0)).val 0 = Complex.exp a₀.val.2
    rw [δp.source, hF a₀, ptOfF_zero]
  let η : C(unitInterval, ℂ) := Complex.isCoveringMap_exp.liftPath ℓ a₀.val.2 hℓ0
  have hη_lifts : Complex.expNeZero ∘ η = ℓ :=
    Complex.isCoveringMap_exp.liftPath_lifts ℓ a₀.val.2 hℓ0
  have hη0 : η 0 = a₀.val.2 := Complex.isCoveringMap_exp.liftPath_zero ℓ a₀.val.2 hℓ0
  have hexp_η : ∀ s, Complex.exp (η s) = (p (δp s)).val 0 :=
    fun s => congrArg Subtype.val (congrFun hη_lifts s)
  have hηH : ∀ s, (η s).re < c := by
    intro s
    have hb : ‖Complex.exp (η s)‖ < Real.exp c := by
      rw [hexp_η s]; exact (bℓ s).property.2.1
    rw [Complex.norm_exp] at hb; exact Real.exp_lt_exp.mp hb
  have hσball : ∀ s, ‖Fin.tail (p (δp s)).val‖ < δz := fun s => (bℓ s).property.2.2
  have hγcont : Continuous fun s => ((Fin.tail (p (δp s)).val, η s) : (Fin n → ℂ) × ℂ) := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) η.continuous
    exact (continuous_apply i.succ).comp
      (continuous_subtype_val.comp (cov.continuous.comp δp.continuous))
  let γ : C(unitInterval, ↥(prodDom n δz c)) :=
    ⟨fun s => ⟨(Fin.tail (p (δp s)).val, η s),
      ⟨by rw [Metric.mem_ball, dist_zero_right]; exact hσball s, hηH s⟩⟩, hγcont.subtype_mk _⟩
  have hsrc : bℓ 0 = p (F a₀) := by show p (δp 0) = p (F a₀); rw [δp.source]
  have hbasept : ∀ s, ptOfF n (γ s).val = (p (δp s)).val := by
    intro s
    show ptOfF n (Fin.tail (p (δp s)).val, η s) = (p (δp s)).val
    rw [ptOfF, show Complex.exp (η s) = (p (δp s)).val 0 from hexp_η s]
    exact Fin.cons_self_tail _
  have hFγ_lifts : (p : E → ↥(baseU n δz c)) ∘ (F.comp γ) = bℓ := by
    funext s
    show p (F (γ s)) = p (δp s)
    apply Subtype.ext
    rw [hF (γ s), hbasept s]
  have hFγ0 : (F.comp γ) 0 = F a₀ := by
    show F (γ 0) = F a₀
    congr 1
    apply Subtype.ext
    show (Fin.tail (p (δp 0)).val, η 0) = a₀.val
    rw [δp.source, hη0, hF a₀,
      show Fin.tail (ptOfF n a₀.val) = a₀.val.1 from Fin.tail_cons _ _]
  have heq : F.comp γ = δp.toContinuousMap := by
    rw [(cov.eq_liftPath_iff' (Γ := F.comp γ) hsrc).mpr ⟨hFγ_lifts, hFγ0⟩,
      (cov.eq_liftPath_iff' (Γ := δp.toContinuousMap) hsrc).mpr ⟨rfl, δp.source⟩]
  have hexp1 : Complex.exp (η 1) = Complex.exp a₀.val.2 := by
    rw [hexp_η 1, δp.target, he', hF a₀, ptOfF_zero]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp
    (show Complex.exp (η 1 - a₀.val.2) = 1 by
      rw [Complex.exp_sub, hexp1, div_self (Complex.exp_ne_zero _)])
  have hη1_eq : η 1 = a₀.val.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by linear_combination hk
  have htail1 : Fin.tail (p (δp 1)).val = a₀.val.1 := by
    rw [δp.target, he', hF a₀, show Fin.tail (ptOfF n a₀.val) = a₀.val.1 from Fin.tail_cons _ _]
  have hmem1 : (a₀.val.1, a₀.val.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I)) ∈ prodDom n δz c := by
    rw [← hη1_eq, ← htail1]; exact (γ 1).property
  refine ⟨k, hmem1, ?_⟩
  have hg1 : (⟨(a₀.val.1, a₀.val.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I)), hmem1⟩ :
      ↥(prodDom n δz c)) = γ 1 := by
    apply Subtype.ext
    show (a₀.val.1, a₀.val.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I)) = (Fin.tail (p (δp 1)).val, η 1)
    rw [htail1, hη1_eq]
  rw [hg1]
  have hc1 : (F.comp γ) 1 = δp.toContinuousMap 1 := DFunLike.congr_fun heq 1
  exact hc1.trans δp.target

/-- **The `m`-sheet period (family).** Family analogue of `halfplane_lift_period`: `F` is invariant
under the transverse shift by `m·2πi`. -/
theorem family_lift_period {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    {δz c : ℝ} {p : E → ↥(baseU n δz c)} (cov : IsCoveringMap p)
    (F : C(↥(prodDom n δz c), E))
    (hF : ∀ pt : ↥(prodDom n δz c), ((p (F pt)).val : Fin (n + 1) → ℂ) = ptOfF n pt.val)
    (a₀ : ↥(prodDom n δz c)) (m : ℕ) [Fintype {e // p e = p (F a₀)}]
    (hcard : Fintype.card {e // p e = p (F a₀)} = m)
    (x : ↥(prodDom n δz c)) :
    ∃ h : (x.val.1, x.val.2 + (m : ℂ) * (2 * (π : ℂ) * Complex.I)) ∈ prodDom n δz c,
      F ⟨(x.val.1, x.val.2 + (m : ℂ) * (2 * (π : ℂ) * Complex.I)), h⟩ = F x := by
  classical
  have hδz : 0 < δz := lt_of_le_of_lt (norm_nonneg a₀.val.1)
    (by have := a₀.property.1; rwa [Metric.mem_ball, dist_zero_right] at this)
  haveI : SimplyConnectedSpace ↥(prodDom n δz c) := simplyConnected_prodDom hδz c
  set T₀ : ℂ := 2 * (π : ℂ) * Complex.I with hT₀
  let f : C(↥(prodDom n δz c), ↥(baseU n δz c)) := ⟨fun pt => p (F pt), cov.continuous.comp F.continuous⟩
  have hpF : (p ∘ (F : ↥(prodDom n δz c) → E) : ↥(prodDom n δz c) → ↥(baseU n δz c)) = f := rfl
  have hexpkT : ∀ k : ℤ, Complex.exp ((k : ℂ) * T₀) = 1 :=
    fun k => Complex.exp_int_mul_two_pi_mul_I k
  have hmemHP : ∀ (pt : ↥(prodDom n δz c)) (k : ℤ),
      (pt.val.1, pt.val.2 + (k : ℂ) * T₀) ∈ prodDom n δz c := by
    intro pt k
    refine ⟨pt.property.1, ?_⟩
    show (pt.val.2 + (k : ℂ) * T₀).re < c
    rw [Complex.add_re, hT₀, intMul_two_pi_I_re, add_zero]; exact pt.property.2
  let shiftPt : ℤ → ↥(prodDom n δz c) :=
    fun k => ⟨(a₀.val.1, a₀.val.2 + (k : ℂ) * T₀), hmemHP a₀ k⟩
  have hbase_inv : ∀ (pt : ↥(prodDom n δz c)) (k : ℤ),
      p (F ⟨(pt.val.1, pt.val.2 + (k : ℂ) * T₀), hmemHP pt k⟩) = p (F pt) := by
    intro pt k
    apply Subtype.ext
    rw [hF ⟨(pt.val.1, pt.val.2 + (k : ℂ) * T₀), hmemHP pt k⟩, hF pt]
    show ptOfF n (pt.val.1, pt.val.2 + (k : ℂ) * T₀) = ptOfF n pt.val
    rw [ptOfF, ptOfF, show Complex.exp (pt.val.2 + (k : ℂ) * T₀) = Complex.exp pt.val.2 from by
      rw [Complex.exp_add, hexpkT k, mul_one]]
  have hmem : ∀ k : ℤ, p (F (shiftPt k)) = p (F a₀) := fun k => hbase_inv a₀ k
  let orbZ : ℤ → {e // p e = p (F a₀)} := fun k => ⟨F (shiftPt k), hmem k⟩
  have hshiftPt_add : ∀ (k d : ℤ),
      shiftPt (k + d)
        = shiftHPF δz c ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]) (shiftPt k) := by
    intro k d
    apply Subtype.ext
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    show a₀.val.2 + ((k + d : ℤ) : ℂ) * T₀ = a₀.val.2 + (k : ℂ) * T₀ + (d : ℂ) * T₀
    push_cast; ring
  have key : ∀ d : ℤ, F (shiftPt d) = F a₀ → ∀ k : ℤ, F (shiftPt (k + d)) = F (shiftPt k) := by
    intro d hd
    have hshift_inv : (f ∘ (shiftHPF δz c ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]))
        : ↥(prodDom n δz c) → ↥(baseU n δz c)) = f := by
      funext pt; exact hbase_inv pt d
    have h0 : F (shiftHPF δz c ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]) a₀) = F a₀ := hd
    have hall := lift_periodic cov hpF (shiftHPF δz c ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]))
      hshift_inv a₀ h0
    intro k; rw [hshiftPt_add k d]; exact hall (shiftPt k)
  have keyZ : ∀ d : ℤ, F (shiftPt d) = F a₀ → ∀ (nn k : ℤ), orbZ (k + nn * d) = orbZ k := by
    intro d hd nn
    induction nn using Int.induction_on with
    | zero => intro k; simp
    | succ j ih =>
        intro k
        apply Subtype.ext
        show F (shiftPt (k + (j + 1) * d)) = F (shiftPt k)
        have e1 : k + (j + 1) * d = (k + j * d) + d := by ring
        rw [e1, key d hd (k + j * d)]
        exact congrArg Subtype.val (ih k)
    | pred j ih =>
        intro k
        apply Subtype.ext
        show F (shiftPt (k + (-j - 1) * d)) = F (shiftPt k)
        have e2 : (k + (-(j + 1)) * d) + d = k + (-j) * d := by ring
        have hkey := key d hd (k + (-(j + 1)) * d)
        rw [e2] at hkey
        rw [show k + (-j - 1) * d = (k + (-(j + 1)) * d) from by ring, ← hkey]
        exact congrArg Subtype.val (ih k)
  suffices hsuff : ∃ d : ℤ, 1 ≤ d ∧ d ≤ (m : ℤ) ∧ F (shiftPt d) = F a₀ by
    obtain ⟨d, hd1, hdm, hd⟩ := hsuff
    have hd0 : (0 : ℤ) < d := by omega
    have hsurj : Function.Surjective (fun a : Fin d.toNat => orbZ (a.val : ℤ)) := by
      intro y
      obtain ⟨k, _, hk⟩ := family_lift_orbit cov F hF a₀ y.2
      have hyk : y = orbZ k := Subtype.ext hk.symm
      have hk0nonneg : 0 ≤ k % d := Int.emod_nonneg k hd0.ne'
      have hk0lt : k % d < d := Int.emod_lt_of_pos k hd0
      have hsplit : k = (k % d) + (k / d) * d := by
        have h := Int.emod_add_mul_ediv k d
        rw [mul_comm (k / d) d]; omega
      have hkk0 : orbZ k = orbZ (k % d) := by
        conv_lhs => rw [hsplit]
        exact keyZ d hd (k / d) (k % d)
      exact ⟨⟨(k % d).toNat, by omega⟩, by
        show orbZ (((k % d).toNat : ℤ)) = y
        rw [Int.toNat_of_nonneg hk0nonneg, ← hkk0, ← hyk]⟩
    have hcard_le := Fintype.card_le_of_surjective _ hsurj
    rw [Fintype.card_fin, hcard] at hcard_le
    have hdeq : d = (m : ℤ) := by omega
    have hmemM : ∀ pt : ↥(prodDom n δz c), (pt.val.1, pt.val.2 + (m : ℂ) * T₀) ∈ prodDom n δz c := by
      intro pt
      refine ⟨pt.property.1, ?_⟩
      show (pt.val.2 + (m : ℂ) * T₀).re < c
      rw [Complex.add_re, hT₀, natMul_two_pi_I_re, add_zero]; exact pt.property.2
    have hexpM : Complex.exp ((m : ℂ) * T₀) = 1 := by
      rw [hT₀, show (m : ℂ) = ((m : ℤ) : ℂ) from (Int.cast_natCast m).symm]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have hbaseM : ∀ pt : ↥(prodDom n δz c),
        p (F ⟨(pt.val.1, pt.val.2 + (m : ℂ) * T₀), hmemM pt⟩) = p (F pt) := by
      intro pt
      apply Subtype.ext
      rw [hF ⟨(pt.val.1, pt.val.2 + (m : ℂ) * T₀), hmemM pt⟩, hF pt]
      show ptOfF n (pt.val.1, pt.val.2 + (m : ℂ) * T₀) = ptOfF n pt.val
      rw [ptOfF, ptOfF, show Complex.exp (pt.val.2 + (m : ℂ) * T₀) = Complex.exp pt.val.2 from by
        rw [Complex.exp_add, hexpM, mul_one]]
    refine ⟨hmemM x, ?_⟩
    set sm : C(↥(prodDom n δz c), ↥(prodDom n δz c)) :=
      shiftHPF δz c ((m : ℂ) * T₀) (by rw [hT₀]; exact natMul_two_pi_I_re m) with hsm
    have hshift_inv : (f ∘ sm : ↥(prodDom n δz c) → ↥(baseU n δz c)) = f := by
      funext pt; exact hbaseM pt
    have h0 : F (sm a₀) = F a₀ := by
      show F ⟨(a₀.val.1, a₀.val.2 + (m : ℂ) * T₀), _⟩ = F a₀
      have hd' : F (shiftPt d) = F a₀ := hd
      rwa [show shiftPt d = (⟨(a₀.val.1, a₀.val.2 + (m : ℂ) * T₀), hmemM a₀⟩ :
          ↥(prodDom n δz c)) from Subtype.ext (Prod.ext_iff.mpr ⟨rfl, by
            show a₀.val.2 + (d : ℂ) * T₀ = a₀.val.2 + (m : ℂ) * T₀
            rw [hdeq]; push_cast; ring⟩)] at hd'
    exact lift_periodic cov hpF sm hshift_inv a₀ h0 x
  obtain ⟨i, j, hij, heqij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (m + 1) => orbZ ((i : ℕ) : ℤ))
    (by rw [Fintype.card_fin, hcard]; exact Nat.lt_succ_self _)
  have hijval : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
  have hkey : ∀ a b : ℤ, a < b → orbZ a = orbZ b → F (shiftPt (b - a)) = F a₀ := by
    intro a b hab horb
    have hva : F (shiftPt a) = F (shiftPt b) := congrArg Subtype.val horb
    set s := shiftHPF δz c ((↑(b - a) : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]) with hs
    have hshift_inv : (f ∘ s : ↥(prodDom n δz c) → ↥(baseU n δz c)) = f := by
      funext pt; exact hbase_inv pt (b - a)
    have hanchor : F (s (shiftPt a)) = F (shiftPt a) := by
      show F ⟨((shiftPt a).val.1, (shiftPt a).val.2 + (↑(b - a) : ℂ) * T₀), _⟩ = F (shiftPt a)
      rw [show (⟨((shiftPt a).val.1, (shiftPt a).val.2 + (↑(b - a) : ℂ) * T₀),
          hmemHP (shiftPt a) (b - a)⟩ : ↥(prodDom n δz c)) = shiftPt b from
        Subtype.ext (Prod.ext_iff.mpr ⟨rfl, by
          show a₀.val.2 + ((a : ℤ) : ℂ) * T₀ + ((b - a : ℤ) : ℂ) * T₀ = a₀.val.2 + ((b : ℤ) : ℂ) * T₀
          push_cast; ring⟩)]
      exact hva.symm
    exact lift_periodic cov hpF s hshift_inv (shiftPt a) hanchor a₀
  rcases lt_or_gt_of_ne hijval with hlt | hgt
  · exact ⟨(j : ℕ) - (i : ℕ), by omega, by omega, hkey _ _ (by exact_mod_cast hlt) heqij⟩
  · exact ⟨(i : ℕ) - (j : ℕ), by omega, by omega, hkey _ _ (by exact_mod_cast hgt) heqij.symm⟩

/-- **The analytic root lift over the family universal cover (Lemma 4.2.6, s≥1, step 1).** Lifts the
root cover along `(z,τ) ↦ cons (exp τ) z` from the simply-connected product domain to a continuous root
section `ρ(z,τ)` with `(q (ptOfF (z,τ))).eval (ρ (z,τ)) = 0`. -/
theorem exists_root_lift_family (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    {δz c : ℝ}
    (hanaU : ∀ i, ∀ y ∈ baseU n δz c, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hsep : ∀ y ∈ baseU n δz c, (q y).Separable)
    (hpc : PathConnectedSpace ↥(rootProj q ⁻¹' baseU n δz c))
    {p₀ : (Fin n → ℂ) × ℂ} (hp₀ : p₀ ∈ prodDom n δz c)
    {t₀ : ℂ} (ht₀ : (q (ptOfF n p₀)).eval t₀ = 0) :
    ∃ ρ : (Fin n → ℂ) × ℂ → ℂ, ρ p₀ = t₀ ∧
      ContinuousOn ρ (prodDom n δz c) ∧
      (∀ p ∈ prodDom n δz c, (q (ptOfF n p)).eval (ρ p) = 0) ∧
      (∀ p ∈ prodDom n δz c,
        ρ (p.1, p.2 + (m : ℂ) * (2 * (π : ℂ) * Complex.I)) = ρ p) ∧
      (∀ p ∈ prodDom n δz c, ∀ t : ℂ, (q (ptOfF n p)).eval t = 0 →
        ∃ τ' : ℂ, (p.1, τ') ∈ prodDom n δz c ∧
          Complex.exp τ' = Complex.exp p.2 ∧ ρ (p.1, τ') = t) := by
  classical
  have hδz : 0 < δz := lt_of_le_of_lt (norm_nonneg _) (ptOfF_section_norm hp₀)
  haveI : SimplyConnectedSpace (prodDom n δz c) := simplyConnected_prodDom hδz c
  have cov : IsCoveringMap ((baseU n δz c).restrictPreimage (rootProj q)) :=
    rootCover_isCoveringMap_gen q hmonic hdeg hcont (fun i y hy => hanaU i y hy) hsep
  let f : C(↥(prodDom n δz c), ↥(baseU n δz c)) :=
    ⟨fun p => ⟨ptOfF n p.val, ptOfF_mem_baseU p.property⟩,
      (continuous_ptOfF.comp continuous_subtype_val).subtype_mk _⟩
  let a₀ : ↥(prodDom n δz c) := ⟨p₀, hp₀⟩
  let e₀ : ↥(rootProj q ⁻¹' baseU n δz c) := ⟨⟨(ptOfF n p₀, t₀), ht₀⟩, ptOfF_mem_baseU hp₀⟩
  have he : (baseU n δz c).restrictPreimage (rootProj q) e₀ = f a₀ := rfl
  obtain ⟨F, ⟨hF0, hFlift⟩, _⟩ := cov.existsUnique_continuousMap_lifts f a₀ e₀ he
  set ρ : (Fin n → ℂ) × ℂ → ℂ :=
    fun p => if h : p ∈ prodDom n δz c then ((F ⟨p, h⟩).val.val.2) else 0 with hρdef
  haveI : PathConnectedSpace ↥(rootProj q ⁻¹' baseU n δz c) := hpc
  have hF_lift : ∀ pt : ↥(prodDom n δz c),
      (((baseU n δz c).restrictPreimage (rootProj q) (F pt)).val : Fin (n + 1) → ℂ) = ptOfF n pt.val :=
    fun pt => congrArg Subtype.val (congrFun hFlift pt)
  have hbU : (F a₀).val.val.1 ∈ baseU n δz c := (F a₀).property
  haveI : Fintype {e // (baseU n δz c).restrictPreimage (rootProj q) e
      = (baseU n δz c).restrictPreimage (rootProj q) (F a₀)} :=
    Fintype.ofEquiv _ (rootCover_fiberEquiv q (F a₀) (hmonic _).ne_zero).symm
  have hcardm : Fintype.card {e // (baseU n δz c).restrictPreimage (rootProj q) e
      = (baseU n δz c).restrictPreimage (rootProj q) (F a₀)} = m := by
    rw [Fintype.card_congr (rootCover_fiberEquiv q (F a₀) (hmonic _).ne_zero), Fintype.card_coe,
      Multiset.toFinset_card_of_nodup (nodup_roots (hsep _ hbU)),
      splits_iff_card_roots.mp (IsAlgClosed.splits _), hdeg _]
  refine ⟨ρ, ?_, ?_, ?_, ?_, ?_⟩
  · show (if h : p₀ ∈ prodDom n δz c then ((F ⟨p₀, h⟩).val.val.2) else 0) = t₀
    rw [dif_pos hp₀]; show (F a₀).val.val.2 = t₀; rw [hF0]
  · rw [continuousOn_iff_continuous_restrict]
    refine Continuous.congr (f := fun p : ↥(prodDom n δz c) => ((F p).val.val.2)) ?_ ?_
    · exact continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp F.continuous))
    · intro p
      rw [Set.restrict_apply]
      show (F p).val.val.2
        = if h : (p : (Fin n → ℂ) × ℂ) ∈ prodDom n δz c then ((F ⟨p.val, h⟩).val.val.2) else 0
      rw [dif_pos p.property]
  · intro p hp
    show (q (ptOfF n p)).eval (if h : p ∈ prodDom n δz c then ((F ⟨p, h⟩).val.val.2) else 0) = 0
    rw [dif_pos hp]
    have hbase : (F ⟨p, hp⟩).val.val.1 = ptOfF n p :=
      congrArg Subtype.val (congrFun hFlift ⟨p, hp⟩)
    have hr : (q (F ⟨p, hp⟩).val.val.1).eval (F ⟨p, hp⟩).val.val.2 = 0 :=
      (F ⟨p, hp⟩).val.property
    rw [hbase] at hr; exact hr
  · -- periodicity via `family_lift_period`
    intro p hp
    obtain ⟨hmemτ, hper⟩ := family_lift_period cov F hF_lift a₀ m hcardm ⟨p, hp⟩
    simp only [hρdef]
    rw [dif_pos hmemτ, dif_pos hp, hper]
  · -- surjectivity onto the fibre via `family_lift_orbit`
    intro p hp t hroott
    have he' : (baseU n δz c).restrictPreimage (rootProj q)
        (⟨⟨(ptOfF n p, t), hroott⟩, ptOfF_mem_baseU hp⟩ : ↥(rootProj q ⁻¹' baseU n δz c))
        = (baseU n δz c).restrictPreimage (rootProj q) (F ⟨p, hp⟩) :=
      Subtype.ext (hF_lift ⟨p, hp⟩).symm
    obtain ⟨k, hk_mem, hk_eq⟩ := family_lift_orbit cov F hF_lift ⟨p, hp⟩ he'
    refine ⟨p.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I), hk_mem, ?_, ?_⟩
    · rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · simp only [hρdef]
      rw [dif_pos hk_mem, hk_eq]

/-- **Family descent (Lemma 4.2.6, s≥1, step 3).** `φ(z,u) := ρ(z, m·log u)` is single-valued (period),
jointly analytic on the punctured `u`-disc, with `(q (cons uᵐ z)).eval (φ (z,u)) = 0` and the
root-bijection. The log branch cut is invisible because the `±2πi` jump is a period of `ρ(z,·)`. -/
theorem descend_phi_family {ρ : (Fin n → ℂ) × ℂ → ℂ} {δz c : ℝ} {m : ℕ} (hm : 0 < m)
    {q : (Fin (n + 1) → ℂ) → Polynomial ℂ}
    (hρ_root : ∀ p ∈ prodDom n δz c, (q (ptOfF n p)).eval (ρ p) = 0)
    (hρ_an : ∀ p ∈ prodDom n δz c, AnalyticAt ℂ ρ p)
    (hρ_period : ∀ p ∈ prodDom n δz c,
      ρ (p.1, p.2 + (m : ℂ) * (2 * (π : ℂ) * Complex.I)) = ρ p)
    (hρ_surj : ∀ p ∈ prodDom n δz c, ∀ t : ℂ, (q (ptOfF n p)).eval t = 0 →
      ∃ τ' : ℂ, (p.1, τ') ∈ prodDom n δz c ∧
        Complex.exp τ' = Complex.exp p.2 ∧ ρ (p.1, τ') = t) :
    ∃ φ : (Fin n → ℂ) × ℂ → ℂ,
      (∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
        (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0) ∧
      (∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u)) ∧
      (∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
        ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t)) := by
  set T₀ : ℂ := (m : ℂ) * (2 * (π : ℂ) * Complex.I) with hT₀
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  -- domain membership of `(z, m·log u)`
  have hmemτ : ∀ (z : Fin n → ℂ) (u : ℂ), ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
      (z, (m : ℂ) * Complex.log u) ∈ prodDom n δz c := by
    intro z u hz hu hud
    refine ⟨by rwa [Metric.mem_ball, dist_zero_right], ?_⟩
    show ((m : ℂ) * Complex.log u).re < c
    rw [Complex.mul_re, Complex.log_re, Complex.natCast_im, Complex.natCast_re]
    simp only [zero_mul, sub_zero]
    rw [← Real.log_pow]
    calc Real.log (‖u‖ ^ m) < Real.log (Real.exp c) := Real.log_lt_log (by positivity) hud
      _ = c := Real.log_exp c
  -- ℤ-multiple period (in the transverse component)
  have hshiftmem : ∀ (z : Fin n → ℂ) (τ : ℂ) (k : ℤ), (z, τ) ∈ prodDom n δz c →
      (z, τ + (k : ℂ) * T₀) ∈ prodDom n δz c := by
    intro z τ k hzτ
    refine ⟨hzτ.1, ?_⟩
    show (τ + (k : ℂ) * T₀).re < c
    rw [Complex.add_re, hT₀, show ((k : ℂ) * ((m : ℂ) * (2 * (π : ℂ) * Complex.I))).re = 0 from by
      simp [Complex.mul_re, Complex.mul_im], add_zero]
    exact hzτ.2
  have hperiodZ : ∀ (k : ℤ) (z : Fin n → ℂ) (τ : ℂ), (z, τ) ∈ prodDom n δz c →
      ρ (z, τ + (k : ℂ) * T₀) = ρ (z, τ) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro z τ _; simp
    | succ j ih =>
        intro z τ hzτ
        have hstep := hρ_period (z, τ + ((j : ℤ) : ℂ) * T₀) (hshiftmem z τ (j : ℤ) hzτ)
        rw [show τ + (((j : ℤ) + 1 : ℤ) : ℂ) * T₀ = τ + ((j : ℤ) : ℂ) * T₀ + T₀ from by
          push_cast; ring, hstep, ih z τ hzτ]
    | pred j ih =>
        intro z τ hzτ
        have hstep := hρ_period (z, τ + ((-(j : ℤ) - 1 : ℤ) : ℂ) * T₀)
          (hshiftmem z τ (-(j : ℤ) - 1) hzτ)
        rw [show τ + ((-(j : ℤ) - 1 : ℤ) : ℂ) * T₀ + T₀ = τ + ((-(j : ℤ) : ℤ) : ℂ) * T₀ from by
          push_cast; ring] at hstep
        rw [← hstep, ih z τ hzτ]
  refine ⟨fun p => ρ (p.1, (m : ℂ) * Complex.log p.2), ?_, ?_, ?_⟩
  · -- root equation
    intro z u hz hu hud
    have hr := hρ_root _ (hmemτ z u hz hu hud)
    rwa [show ptOfF n (z, (m : ℂ) * Complex.log u) = Fin.cons (u ^ m) z from by
      rw [ptOfF, show Complex.exp ((m : ℂ) * Complex.log u) = u ^ m from by
        rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu)]]] at hr
  · -- joint analyticity (branch-cut-invisible)
    intro z₀ u₀ hz₀ hu₀ hud₀
    obtain ⟨L, hL_an, hL_exp⟩ := exists_local_log_branch (norm_pos_iff.mp hu₀)
    have hexp0 : Complex.exp (L u₀) = u₀ := hL_exp.self_of_nhds
    have hLre : (L u₀).re = Real.log ‖u₀‖ := by
      have hh : Real.exp (L u₀).re = ‖u₀‖ := by rw [← Complex.norm_exp, hexp0]
      rw [← hh, Real.log_exp]
    have hLmem : (z₀, (m : ℂ) * L u₀) ∈ prodDom n δz c := by
      refine ⟨by rwa [Metric.mem_ball, dist_zero_right], ?_⟩
      show ((m : ℂ) * L u₀).re < c
      rw [Complex.mul_re, hLre, Complex.natCast_im, Complex.natCast_re]
      simp only [zero_mul, sub_zero]; rw [← Real.log_pow]
      calc Real.log (‖u₀‖ ^ m) < Real.log (Real.exp c) := Real.log_lt_log (by positivity) hud₀
        _ = c := Real.log_exp c
    have hφeq : (fun p : (Fin n → ℂ) × ℂ => ρ (p.1, (m : ℂ) * Complex.log p.2))
        =ᶠ[𝓝 (z₀, u₀)] fun p => ρ (p.1, (m : ℂ) * L p.2) := by
      rw [nhds_prod_eq]
      have hune : ∀ᶠ p : (Fin n → ℂ) × ℂ in 𝓝 z₀ ×ˢ 𝓝 u₀, p.2 ≠ 0 :=
        tendsto_snd.eventually (isOpen_ne.mem_nhds (norm_pos_iff.mp hu₀))
      have hexpL : ∀ᶠ p : (Fin n → ℂ) × ℂ in 𝓝 z₀ ×ˢ 𝓝 u₀, Complex.exp (L p.2) = p.2 :=
        tendsto_snd.eventually hL_exp
      have hzd : ∀ᶠ p : (Fin n → ℂ) × ℂ in 𝓝 z₀ ×ˢ 𝓝 u₀, ‖p.1‖ < δz :=
        tendsto_fst.eventually
          ((isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖z₀‖ < δz from hz₀))
      have hud' : ∀ᶠ p : (Fin n → ℂ) × ℂ in 𝓝 z₀ ×ˢ 𝓝 u₀, ‖p.2‖ ^ m < Real.exp c :=
        tendsto_snd.eventually
          ((isOpen_lt (continuous_norm.pow m) continuous_const).mem_nhds
            (show ‖u₀‖ ^ m < Real.exp c from hud₀))
      filter_upwards [hune, hexpL, hzd, hud'] with p hpne hpexp hpz hpud
      have hpu : 0 < ‖p.2‖ := norm_pos_iff.mpr hpne
      have hdiff : Complex.exp (L p.2 - Complex.log p.2) = 1 := by
        rw [Complex.exp_sub, hpexp, Complex.exp_log hpne, div_self hpne]
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hdiff
      have hmL : (m : ℂ) * L p.2 = (m : ℂ) * Complex.log p.2 + (k : ℂ) * T₀ := by
        rw [hT₀]
        have hLu : L p.2 = Complex.log p.2 + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
          linear_combination hk
        rw [hLu]; ring
      show ρ (p.1, (m : ℂ) * Complex.log p.2) = ρ (p.1, (m : ℂ) * L p.2)
      rw [hmL, hperiodZ k p.1 _ (hmemτ p.1 p.2 hpz hpu hpud)]
    have hinner : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => (p.1, (m : ℂ) * L p.2)) (z₀, u₀) :=
      ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt (z₀, u₀)).prod
        (analyticAt_const.mul (hL_an.comp ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt (z₀, u₀))))
    have hcomp : AnalyticAt ℂ (ρ ∘ fun p : (Fin n → ℂ) × ℂ => (p.1, (m : ℂ) * L p.2)) (z₀, u₀) :=
      AnalyticAt.comp (g := ρ) (f := fun p : (Fin n → ℂ) × ℂ => (p.1, (m : ℂ) * L p.2))
        (hρ_an _ hLmem) hinner
    exact hcomp.congr hφeq.symm
  · -- the iff
    intro z u t hz hu hud
    have hbase : ptOfF n (z, (m : ℂ) * Complex.log u) = Fin.cons (u ^ m) z := by
      rw [ptOfF, show Complex.exp ((m : ℂ) * Complex.log u) = u ^ m from by
        rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu)]]
    constructor
    · intro hroott
      have hroot' : (q (ptOfF n (z, (m : ℂ) * Complex.log u))).eval t = 0 := by rw [hbase]; exact hroott
      obtain ⟨τ', hτ'mem, hexpτ', hρτ'⟩ := hρ_surj _ (hmemτ z u hz hu hud) t hroot'
      dsimp only at hτ'mem hexpτ' hρτ'
      refine ⟨Complex.exp (τ' / (m : ℂ)), ?_, ?_⟩
      · have hmul : (m : ℂ) * (τ' / (m : ℂ)) = τ' := by field_simp
        have hpow : (Complex.exp (τ' / (m : ℂ))) ^ m = Complex.exp τ' := by
          rw [← Complex.exp_nat_mul, hmul]
        rw [hpow, hexpτ']
        show Complex.exp ((m : ℂ) * Complex.log u) = u ^ m
        rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu)]
      · show ρ (z, (m : ℂ) * Complex.log (Complex.exp (τ' / (m : ℂ)))) = t
        obtain ⟨k₀, hk₀⟩ := Complex.exp_eq_one_iff.mp
          (show Complex.exp (Complex.log (Complex.exp (τ' / (m : ℂ))) - τ' / (m : ℂ)) = 1 by
            rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero _),
              div_self (Complex.exp_ne_zero _)])
        have hml : (m : ℂ) * Complex.log (Complex.exp (τ' / (m : ℂ))) = τ' + (k₀ : ℂ) * T₀ := by
          have hlog : Complex.log (Complex.exp (τ' / (m : ℂ)))
              = τ' / (m : ℂ) + (k₀ : ℂ) * (2 * (π : ℂ) * Complex.I) := by linear_combination hk₀
          rw [hlog, hT₀]; field_simp
        rw [hml, hperiodZ k₀ z τ' hτ'mem, hρτ']
    · rintro ⟨u', hu'm, hφu'⟩
      have h2 : ‖u'‖ ^ m = ‖u‖ ^ m := by rw [← norm_pow, ← norm_pow, hu'm]
      have hu'pos : 0 < ‖u'‖ := by
        have h1 : (0 : ℝ) < ‖u‖ ^ m := pow_pos hu m
        have hne : ‖u'‖ ≠ 0 := fun h => by
          rw [h, zero_pow hm.ne'] at h2; exact absurd h2.symm (ne_of_gt h1)
        exact (norm_nonneg u').lt_of_ne (Ne.symm hne)
      have hr := hρ_root _ (hmemτ z u' hz hu'pos (by rw [h2]; exact hud))
      rw [show ptOfF n (z, (m : ℂ) * Complex.log u') = Fin.cons (u' ^ m) z from by
        rw [ptOfF, show Complex.exp ((m : ℂ) * Complex.log u') = u' ^ m from by
          rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu'pos)]], hu'm] at hr
      have hval : ρ (z, (m : ℂ) * Complex.log u') = t := hφu'
      rwa [hval] at hr

/-- The sup-norm on `Fin (n+1) → ℂ` is bounded by the max of the coordinate-`0` norm and the tail. -/
lemma norm_le_max_zero_tail (y : Fin (n + 1) → ℂ) : ‖y‖ ≤ max (‖y 0‖) (‖Fin.tail y‖) := by
  refine (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact le_max_left _ _
  · calc ‖y j.succ‖ = ‖Fin.tail y j‖ := rfl
      _ ≤ ‖Fin.tail y‖ := norm_le_pi_norm _ _
      _ ≤ _ := le_max_right _ _

/-- **Lemma 4.2.6, `s ≥ 1` family (punctured), for an irreducible Weierstrass family.** Discharges the
root-bound and path-connectedness prerequisites (`roots_eventually_bounded`, `rootCover_pathConnected_gen`
with `baseU` preconnected), then assembles the lift, joint analyticity, and descent into the family
parametrization `φ(z,u)`: jointly analytic on the punctured `u`-disc, with the root equation and the
root-bijection. Only separability off `0` (the discriminant condition) remains a hypothesis. -/
theorem exists_param_family (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) (m : ℕ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcont : ∀ i, Continuous (fun y => (q y).coeff i))
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducibleGen q)
    {δz c : ℝ} (hδz : 0 < δz)
    (hanaU : ∀ i, ∀ y ∈ baseU n δz c, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hsep : ∀ y ∈ baseU n δz c, (q y).Separable) :
    ∃ φ : (Fin n → ℂ) × ℂ → ℂ,
      (∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
        (q (Fin.cons (u ^ m) z)).eval (φ (z, u)) = 0) ∧
      (∀ z u, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c → AnalyticAt ℂ φ (z, u)) ∧
      (∀ z u t, ‖z‖ < δz → 0 < ‖u‖ → ‖u‖ ^ m < Real.exp c →
        ((q (Fin.cons (u ^ m) z)).eval t = 0 ↔ ∃ u', u' ^ m = u ^ m ∧ φ (z, u') = t)) := by
  have hbdd := roots_eventually_bounded q m hm hmonic hdeg hcont hq0 (R := 1) one_pos
  have hpc : PathConnectedSpace ↥(rootProj q ⁻¹' baseU n δz c) :=
    rootCover_pathConnected_gen q hm hmonic hdeg hcont hana0 hq0 hirr
      (isOpen_baseU δz c) (isPreconnected_baseU c) hsep (baseU_mem_nhdsWithin hδz c)
      (fun i y hy => hanaU i y hy) zero_le_one hbdd
  have hp₀ : ((0 : Fin n → ℂ), ((c - 1 : ℝ) : ℂ)) ∈ prodDom n δz c :=
    Set.mk_mem_prod (Metric.mem_ball_self hδz)
      (by simp only [halfPlane, Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root
    (q (ptOfF n ((0 : Fin n → ℂ), ((c - 1 : ℝ) : ℂ)))) (by
      rw [Polynomial.degree_eq_natDegree (hmonic _).ne_zero, hdeg]; exact_mod_cast hm.ne')
  obtain ⟨ρ, _, hcont_ρ, hroot_ρ, hper_ρ, hsurj_ρ⟩ :=
    exists_root_lift_family q m hmonic hdeg hcont hanaU hsep hpc hp₀ ht₀
  have han_ρ := analyticOn_root_family q m hmonic hdeg hanaU hsep hcont_ρ hroot_ρ
  exact descend_phi_family hm hroot_ρ han_ρ hper_ρ hsurj_ρ

end Puiseux
