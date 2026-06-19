import Cad.Multivariate.ProjectionTheorem.Puiseux.RootCover
import Cad.Multivariate.ProjectionTheorem.Generalized.HyperplaneExtension

/-!
# G2b/c — the connectedness kernel over a general base `Fin (n+1) → ℂ`

The `Fin 1 → ℂ` connectedness kernel (`Cad.Multivariate.ProjectionTheorem.Puiseux.RootCover`) extends factor coefficients across
the *isolated* discriminant point `0`. This file lifts the kernel to the base `Fin (n+1) → ℂ`, where the
discriminant locus is (in the normal form) the **coordinate hyperplane** `{x 0 = 0}` and the separable
locus is `{x 0 ≠ 0}`. The one-variable removable singularity is replaced by the multivariable
hyperplane extension `exists_analyticAt_extend_funCoord0` (G2a, `HyperplaneExtension`).

The downstream `=ᶠ[𝓝[≠]0]` propagation becomes "agree off the **dense** hyperplane `{x 0 ≠ 0}` +
continuous ⇒ agree near `0`". The leaf lemmas (`factor_coeff_analyticAt`, `aRootCount_eventually_*`, …)
and `ComplexCovering` are already general-`n`, so they are reused verbatim. `Fin 1 = Fin (0+1)`, so the
committed `n = 0` results (`Cad.Multivariate.ProjectionTheorem.Generalized.Monodromy`) remain valid instances.
-/

noncomputable section

open Polynomial Filter Set
open scoped Topology

variable {n : ℕ}

open Classical in
/-- **G2b — the factor coefficient extends across the hyperplane `{x 0 = 0}`.** For a clopen component
`A` over the separable locus `{x 0 ≠ 0}`, the partial-product coefficient — analytic off the hyperplane
(`factor_coeff_analyticAt`) and bounded near `0` (`norm_coeff_factor_le`) — extends to a function
analytic *at* `0` agreeing with it off `{x 0 = 0}`. The `Fin (n+1)` analogue of `factor_coeff_extends`,
using the multivariable hyperplane extension `exists_analyticAt_extend_funCoord0` (G2a). -/
theorem factor_coeff_extends_gen {d : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    (hsep : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → (q x).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U)
    (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (A : Set ↥(rootVariety q)) (hA : IsClopenOverBase q U A) (j : ℕ) :
    ∃ F : (Fin (n + 1) → ℂ) → ℂ, AnalyticAt ℂ F (0 : Fin (n + 1) → ℂ) ∧
      (∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 →
        F x = (((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).prod
          (fun t => X - C t)).coeff j) := by
  refine exists_analyticAt_extend_funCoord0 (rfl : (0 : Fin (n + 1) → ℂ) 0 = 0) ?_
    (M := (1 + ε) ^ d) ?_
  · filter_upwards [hsep, eventually_nhdsWithin_iff.mp hU0] with x hxsep hxU hx0
    exact factor_coeff_analyticAt q hmonic hdeg (fun i => hanaU i x (hxU hx0)) (hxsep hx0)
      hUopen (hxU hx0) A hA j
  · filter_upwards [hbdd] with x hx
    have hb := norm_coeff_factor_le hε (fun t => (x, t) ∈ (Subtype.val '' A)) hx j
    rwa [hdeg x] at hb

open Classical in
/-- **G2c — the Weierstrass factor `H_A` over the general base.** `Fin (n+1)` analogue of
`exists_factor_weierstrass`: from the hyperplane extension (`factor_coeff_extends_gen`) and the constant
degree `d_A`, build a monic family `H_A` with analytic coefficients at `0` agreeing with the partial
product off the hyperplane `{x 0 = 0}`. -/
theorem exists_factor_weierstrass_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hsep : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → (q x).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U)
    (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) {dA : ℕ} (hdA : 1 ≤ dA)
    (hdA_eq : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).card = dA) :
    ∃ HA : (Fin (n + 1) → ℂ) → Polynomial ℂ,
      (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
      (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧
      HA =ᶠ[𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ)]
        (fun y => ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).prod
          (fun t => X - C t)) := by
  set hpA : (Fin (n + 1) → ℂ) → Polynomial ℂ :=
    fun y => ((q y).roots.toFinset.filter (fun t => (y, t) ∈ (Subtype.val '' A))).prod
      (fun t => X - C t) with hhpA
  choose Fj hFj_an hFj_eq using fun j =>
    factor_coeff_extends_gen q hmonic hdeg hsep hε hbdd hUopen hU0 hanaU A hA j
  set HA : (Fin (n + 1) → ℂ) → Polynomial ℂ :=
    fun y => X ^ dA + ∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j with hHA
  have hlower_deg : ∀ y, (∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j).natDegree < dA := by
    intro y
    rcases eq_or_ne (∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j) 0 with h0 | hne
    · rw [h0, Polynomial.natDegree_zero]; omega
    · rw [Polynomial.natDegree_lt_iff_degree_lt hne]; exact degree_sum_C_mul_X_pow_lt _
  have hmono : ∀ y, (HA y).Monic := by
    intro y; simp only [hHA]; exact (monic_natDegree_X_pow_add (hlower_deg y)).1
  have hdeg_HA : ∀ y, (HA y).natDegree = dA := by
    intro y; simp only [hHA]; exact (monic_natDegree_X_pow_add (hlower_deg y)).2
  have hHA_coeff : ∀ y i, (HA y).coeff i
      = (if i = dA then 1 else 0) + (if i < dA then Fj i y else 0) := by
    intro y i
    rw [hHA]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range dA) i (fun j => Fj j y)]
    simp only [Finset.mem_range]
  have han : ∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0 := by
    intro i
    have heqf : (fun y => (HA y).coeff i)
        = (fun y => (if i = dA then 1 else 0) + (if i < dA then Fj i y else 0)) := by
      funext y; exact hHA_coeff y i
    rw [heqf]
    apply AnalyticAt.add analyticAt_const
    by_cases hi : i < dA
    · simp only [if_pos hi]; exact hFj_an i
    · simp only [if_neg hi]; exact analyticAt_const
  refine ⟨HA, hmono, hdeg_HA, han, ?_⟩
  have hall : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ∀ j ∈ Finset.range dA, Fj j x = (hpA x).coeff j :=
    (Finset.eventually_all (Finset.range dA)).mpr
      (fun j _ => eventually_nhdsWithin_iff.mpr (hFj_eq j))
  filter_upwards [hall, hdA_eq] with y hyall hycount
  show X ^ dA + ∑ j ∈ Finset.range dA, C (Fj j y) * X ^ j = hpA y
  rw [Finset.sum_congr rfl (fun j hj => by rw [hyall j hj])]
  have hmono_hpA : (hpA y).Monic := by rw [hhpA]; exact monic_prod_X_sub_C _
  have hdeg_hpA : (hpA y).natDegree = dA := by
    rw [hhpA, natDegree_prod_X_sub_C]; exact hycount
  exact (monic_eq_X_pow_add_lower hmono_hpA hdeg_hpA).symm

open Topology in
/-- `0` is in the closure of the separable locus `{x 0 ≠ 0}`, so the deleted-hyperplane neighbourhood
filter is nontrivial. (Approach `0` along the `0`-th coordinate axis `t ↦ Pi.single 0 t`, `t ≠ 0`.) -/
instance nhdsWithin_coord0_ne_neBot :
    (𝓝[{x : Fin (n + 1) → ℂ | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  set g : ℂ → (Fin (n + 1) → ℂ) := fun t => Pi.single 0 t with hg
  have hc : Continuous g := by
    rw [hg]; refine continuous_pi (fun i => ?_)
    by_cases hi : i = 0
    · subst hi; simp only [Pi.single_eq_same]; exact continuous_id
    · simp only [Pi.single_eq_of_ne hi]; exact continuous_const
  have hg0 : g 0 = 0 := by rw [hg]; simp
  have htend : Filter.Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (0 : Fin (n + 1) → ℂ)) :=
    (hg0 ▸ hc.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  show g t 0 ≠ 0
  simp only [hg, Pi.single_eq_same]; exact ht

/-- **General-filter polynomial agreement.** If `F = G` along a nontrivial filter `l ≤ 𝓝 x` and each
coefficient of `F`, `G` is continuous at `x`, then `F x = G x`. (Generalizes
`polynomial_eq_of_eventuallyEq_punctured` from the punctured-point filter to the deleted-hyperplane
filter.) -/
theorem polynomial_eq_of_eventuallyEq_filter {α : Type*} [TopologicalSpace α]
    {F G : α → Polynomial ℂ} {x : α} {l : Filter α} [l.NeBot] (hl : l ≤ 𝓝 x)
    (heq : F =ᶠ[l] G) (hF : ∀ j, ContinuousAt (fun y => (F y).coeff j) x)
    (hG : ∀ j, ContinuousAt (fun y => (G y).coeff j) x) :
    F x = G x := by
  ext j
  have hFt : Filter.Tendsto (fun y => (F y).coeff j) l (𝓝 ((F x).coeff j)) :=
    ((hF j).tendsto).mono_left hl
  have hGt : Filter.Tendsto (fun y => (G y).coeff j) l (𝓝 ((G x).coeff j)) :=
    ((hG j).tendsto).mono_left hl
  have hcoeff_eq : (fun y => (F y).coeff j) =ᶠ[l] (fun y => (G y).coeff j) := by
    filter_upwards [heq] with y hy; rw [hy]
  exact tendsto_nhds_unique (hFt.congr' hcoeff_eq) hGt

open Classical in
/-- **G2c — clopen split ⟹ Weierstrass factorisation `q = H_A · H_B` over the general base.** Given a
clopen `A` over the separable locus `{x 0 ≠ 0}` with both `A`, `Aᶜ` of positive degree, `q` factors as a
product of two monic analytic-coefficient families, each `X`-power at `0`, agreeing with `q` off the
hyperplane. `Fin (n+1)` analogue of `clopen_split_factorization` (`hval0` via the general-filter
agreement `polynomial_eq_of_eventuallyEq_filter`; the factorisation is recorded off the dense locus). -/
theorem clopen_split_factorization_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m) (hq0 : q 0 = X ^ m)
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hsep : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → (q x).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U)
    (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) {dA dB : ℕ}
    (hdA : 1 ≤ dA) (hdB : 1 ≤ dB)
    (hdA_eq : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).card = dA)
    (hdB_eq : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' Aᶜ))).card = dB) :
    ∃ HA HB : (Fin (n + 1) → ℂ) → Polynomial ℂ,
      (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
        (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧ HA 0 = X ^ dA ∧
      (∀ y, (HB y).Monic) ∧ (∀ y, (HB y).natDegree = dB) ∧
        (∀ i, AnalyticAt ℂ (fun y => (HB y).coeff i) 0) ∧ HB 0 = X ^ dB ∧
      (∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ), q x = HA x * HB x) := by
  obtain ⟨HA, hHA_mono, hHA_deg, hHA_an, hHA_eq⟩ :=
    exists_factor_weierstrass_gen q hmonic hdeg hsep hε hbdd hUopen hU0 hanaU hA hdA hdA_eq
  obtain ⟨HB, hHB_mono, hHB_deg, hHB_an, hHB_eq⟩ :=
    exists_factor_weierstrass_gen q hmonic hdeg hsep hε hbdd hUopen hU0 hanaU hA.compl hdB hdB_eq
  have hoff : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ), q x = HA x * HB x := by
    have hsepS : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ), (q x).Separable :=
      eventually_nhdsWithin_iff.mpr hsep
    filter_upwards [hsepS, hHA_eq, hHB_eq] with x hxsep hxHA hxHB
    rw [hxHA, hxHB, factor_compl_eq q hmonic x]
    exact family_eq_factor_mul q hmonic hxsep (fun t => (x, t) ∈ (Subtype.val '' A))
  have hprod_an : ∀ k, AnalyticAt ℂ (fun y => (HA y * HB y).coeff k) 0 := by
    intro k
    have hform : (fun y => (HA y * HB y).coeff k)
        = fun y => ∑ p ∈ Finset.antidiagonal k, (HA y).coeff p.1 * (HB y).coeff p.2 := by
      funext y; rw [Polynomial.coeff_mul]
    rw [hform]
    exact Finset.analyticAt_fun_sum _ fun p _ => (hHA_an p.1).mul (hHB_an p.2)
  have hval0 : q 0 = HA 0 * HB 0 :=
    polynomial_eq_of_eventuallyEq_filter nhdsWithin_le_nhds hoff
      (fun j => (hana0 j).continuousAt) (fun j => (hprod_an j).continuousAt)
  have hHA0 : HA 0 = X ^ dA := by
    have hdvd : HA 0 ∣ X ^ m := by rw [← hq0, hval0]; exact Dvd.intro _ rfl
    have hp := eq_X_pow_of_monic_dvd_X_pow (hHA_mono 0) hdvd
    rwa [hHA_deg 0] at hp
  have hHB0 : HB 0 = X ^ dB := by
    have hdvd : HB 0 ∣ X ^ m := by rw [← hq0, hval0]; exact Dvd.intro_left _ rfl
    have hp := eq_X_pow_of_monic_dvd_X_pow (hHB_mono 0) hdvd
    rwa [hHB_deg 0] at hp
  exact ⟨HA, HB, hHA_mono, hHA_deg, hHA_an, hHA0, hHB_mono, hHB_deg, hHB_an, hHB0, hoff⟩

/-- **Univariate-style irreducibility over the general base.** No germ factorisation of `q` at `0` into
two monic positive-degree `X`-power-at-`0` analytic families, even *off the hyperplane* `{x 0 = 0}`.
(Strict generalisation of `UnivIrreducible`; germ-irreducibility implies this via continuity/density.) -/
def UnivIrreducibleGen (q : (Fin (n + 1) → ℂ) → Polynomial ℂ) : Prop :=
  ¬ ∃ (dA dB : ℕ) (HA HB : (Fin (n + 1) → ℂ) → Polynomial ℂ),
    1 ≤ dA ∧ 1 ≤ dB ∧
    (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
      (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧ HA 0 = X ^ dA ∧
    (∀ y, (HB y).Monic) ∧ (∀ y, (HB y).natDegree = dB) ∧
      (∀ i, AnalyticAt ℂ (fun y => (HB y).coeff i) 0) ∧ HB 0 = X ^ dB ∧
    (∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ), q x = HA x * HB x)

open Classical in
/-- **G2c — irreducible ⟹ no nontrivial clopen split (general base).** For an irreducible Weierstrass
family over `Fin (n+1) → ℂ`, no clopen `A` over the separable locus `{x 0 ≠ 0}` has both `A` and `Aᶜ`
contributing positively, since that yields a factorisation contradicting irreducibility. -/
theorem clopen_split_contradiction_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m) (hq0 : q 0 = X ^ m)
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hsep : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → (q x).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    (hirr : UnivIrreducibleGen q)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U)
    (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) {dA dB : ℕ}
    (hdA : 1 ≤ dA) (hdB : 1 ≤ dB)
    (hdA_eq : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).card = dA)
    (hdB_eq : ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' Aᶜ))).card = dB) :
    False := by
  obtain ⟨HA, HB, hHA_mono, hHA_deg, hHA_an, hHA0, hHB_mono, hHB_deg, hHB_an, hHB0, hnear⟩ :=
    clopen_split_factorization_gen q hmonic hdeg hq0 hana0 hsep hε hbdd hUopen hU0 hanaU hA hdA hdB
      hdA_eq hdB_eq
  exact hirr ⟨dA, dB, HA, HB, hdA, hdB, hHA_mono, hHA_deg, hHA_an, hHA0,
    hHB_mono, hHB_deg, hHB_an, hHB0, hnear⟩

open Classical in
/-- **The `A`-root count is constant along the deleted-hyperplane neighbourhood.** `Fin (n+1)` analogue
of `aRootCount_eventually_const`: on a preconnected separable `U ∈ 𝓝[{x 0 ≠ 0}] 0`, the count is
locally constant (`aRootCount_eventually_eq`) hence globally constant on `U`. -/
theorem aRootCount_eventually_const_gen {d : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = d)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A) :
    ∃ dA : ℕ, ∀ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).card = dA := by
  set cnt : (Fin (n + 1) → ℂ) → ℕ := fun x =>
    ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).card with hcnt
  haveI : PreconnectedSpace (↥U) := Subtype.preconnectedSpace hUconn
  have hlc : IsLocallyConstant (fun v : ↥U => cnt v.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hev := aRootCount_eventually_eq q hmonic hdeg (fun i => hanaU i v.1 v.2) (hUsep v.1 v.2)
      hUopen v.2 (A := A) hA
    exact (continuous_subtype_val.continuousAt).eventually hev
  obtain ⟨y₁, hy₁⟩ := Filter.nonempty_of_mem hU0
  refine ⟨cnt y₁, ?_⟩
  filter_upwards [hU0] with y hy
  exact hlc.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨y₁, hy₁⟩

open Classical in
/-- **G2c — irreducible ⟹ no clopen split (count-discharge form).** `Fin (n+1)` analogue of
`clopen_split_contradiction'`: the positive-degree requirement is reduced to the honest nontriviality
`∃ᶠ ... 1 ≤ card` of both `A` and `Aᶜ` over the deleted-hyperplane neighbourhood. -/
theorem clopen_split_contradiction'_gen {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m) (hq0 : q 0 = X ^ m)
    (hana0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (n + 1) → ℂ))
    (hsep : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → (q x).Separable)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdd : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ t ∈ (q x).roots.toFinset, ‖t‖ ≤ ε)
    (hirr : UnivIrreducibleGen q)
    {U : Set (Fin (n + 1) → ℂ)} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsep : ∀ y ∈ U, (q y).Separable) (hU0 : U ∈ 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ))
    (hanaU : ∀ i, ∀ y ∈ U, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {A : Set ↥(rootVariety q)} (hA : IsClopenOverBase q U A)
    (hAne : ∃ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      1 ≤ ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' A))).card)
    (hBne : ∃ᶠ x in 𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ),
      1 ≤ ((q x).roots.toFinset.filter (fun t => (x, t) ∈ (Subtype.val '' Aᶜ))).card) :
    False := by
  obtain ⟨dA, hdA_eq⟩ :=
    aRootCount_eventually_const_gen q hmonic hdeg hUopen hUconn hUsep hU0 hanaU hA
  obtain ⟨dB, hdB_eq⟩ :=
    aRootCount_eventually_const_gen q hmonic hdeg hUopen hUconn hUsep hU0 hanaU hA.compl
  have hdA : 1 ≤ dA := by obtain ⟨y, h1, h2⟩ := (hAne.and_eventually hdA_eq).exists; omega
  have hdB : 1 ≤ dB := by obtain ⟨y, h1, h2⟩ := (hBne.and_eventually hdB_eq).exists; omega
  exact clopen_split_contradiction_gen q hmonic hdeg hq0 hana0 hsep hε hbdd hirr hUopen hU0 hanaU hA
    hdA hdB hdA_eq hdB_eq
