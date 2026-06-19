import Cad.Multivariate.ProjectionTheorem.Generalized.ConnectednessGen

/-!
# M5 (CParam wiring, part 1) — the density extension `germ-irreducible ⟹ UnivIrreducibleGen`

`UnivIrreducibleGen q` forbids a factorisation of `q` *only off the hyperplane* `{x 0 = 0}`
(`∀ᶠ x in 𝓝[{x 0 ≠ 0}] 0`), whereas germ-irreducibility (`WeierstrassIrreducible`) forbids a
factorisation on a *full* neighbourhood (`∀ᶠ x in 𝓝 0`). The hyperplane `{x 0 = 0}` is nowhere dense,
so the two coincide: an off-hyperplane polynomial-family identity between analytic families extends, by
continuity across the dense locus `{x 0 ≠ 0}`, to a full-neighbourhood identity. This file proves that
extension (`polyFamily_eventuallyEq_of_coord0`) and packages it as `univIrreducibleGen_of_germ`
— the previously *deferred* connective tissue between M4's `UnivIrreducibleGen` hypothesis and the
germ-irreducibility supplied by the Zariski axiom.
-/

noncomputable section

open Polynomial Filter Set
open scoped Topology

namespace CParamWiring

variable {n : ℕ}

/-- The separable locus `{x | x 0 ≠ 0}` is **dense** (its complement is a coordinate hyperplane). -/
lemma dense_coord0_ne : Dense {x : Fin (n + 1) → ℂ | x 0 ≠ 0} := by
  have hd : Dense ((Function.eval (0 : Fin (n + 1)) : (Fin (n + 1) → ℂ) → ℂ) ⁻¹' {(0 : ℂ)}ᶜ) :=
    (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval (0 : Fin (n + 1)))
  have hset : {x : Fin (n + 1) → ℂ | x 0 ≠ 0}
      = (Function.eval (0 : Fin (n + 1)) : (Fin (n + 1) → ℂ) → ℂ) ⁻¹' {(0 : ℂ)}ᶜ := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      Function.eval]
  rw [hset]; exact hd

/-- **Density extension for polynomial families.** Two families `F, G` with analytic coefficients and
locally bounded degree that agree *off the hyperplane* `{x 0 = 0}` near `0` agree on a full
neighbourhood of `0`. (Each coefficient is continuous and the agreement set is dense.) -/
lemma polyFamily_eventuallyEq_of_coord0 {F G : (Fin (n + 1) → ℂ) → Polynomial ℂ} {N : ℕ}
    (hFan : ∀ i, AnalyticAt ℂ (fun y => (F y).coeff i) (0 : Fin (n + 1) → ℂ))
    (hGan : ∀ i, AnalyticAt ℂ (fun y => (G y).coeff i) (0 : Fin (n + 1) → ℂ))
    (hFdeg : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), (F y).natDegree ≤ N)
    (hGdeg : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ), (G y).natDegree ≤ N)
    (heq : F =ᶠ[𝓝[{x | x 0 ≠ 0}] (0 : Fin (n + 1) → ℂ)] G) :
    F =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] G := by
  classical
  -- pull the off-hyperplane agreement into the full neighbourhood filter
  have heq' : ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), x 0 ≠ 0 → F x = G x :=
    eventually_nhdsWithin_iff.mp heq
  -- a neighbourhood `V` on which: agreement holds off the hyperplane, the degrees are `≤ N`, and the
  -- finitely many low coefficients of `F`, `G` are analytic
  have hcoeff_ev : ∀ᶠ y in 𝓝 (0 : Fin (n + 1) → ℂ),
      ∀ i ∈ Finset.range (N + 1), AnalyticAt ℂ (fun z => (F z).coeff i) y
        ∧ AnalyticAt ℂ (fun z => (G z).coeff i) y := by
    refine (Filter.eventually_all_finset _).mpr fun i _ => ?_
    exact ((hFan i).eventually_analyticAt).and ((hGan i).eventually_analyticAt)
  obtain ⟨V, hVsub, hVopen, hV0⟩ :=
    eventually_nhds_iff.mp (heq'.and (hFdeg.and (hGdeg.and hcoeff_ev)))
  refine eventually_nhds_iff.mpr ⟨V, fun z hz => ?_, hVopen, hV0⟩
  obtain ⟨hz_eq, hz_Fdeg, hz_Gdeg, hz_coeff⟩ := hVsub z hz
  -- degrees stay `≤ N` near `z`
  have hFdeg_z : ∀ᶠ y in 𝓝 z, (F y).natDegree ≤ N := by
    filter_upwards [hVopen.mem_nhds hz] with y hy using (hVsub y hy).2.1
  have hGdeg_z : ∀ᶠ y in 𝓝 z, (G y).natDegree ≤ N := by
    filter_upwards [hVopen.mem_nhds hz] with y hy using (hVsub y hy).2.2.1
  -- continuity of every coefficient at `z`
  have hcont : ∀ (H : (Fin (n + 1) → ℂ) → Polynomial ℂ),
      (∀ i ∈ Finset.range (N + 1), AnalyticAt ℂ (fun y => (H y).coeff i) z) →
      (∀ᶠ y in 𝓝 z, (H y).natDegree ≤ N) → ∀ j, ContinuousAt (fun y => (H y).coeff j) z := by
    intro H hHan hHdeg j
    rcases Nat.lt_or_ge N j with hjN | hjN
    · have hzero : (fun y => (H y).coeff j) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [hHdeg] with y hy
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hy hjN)
      exact continuousAt_const.congr hzero.symm
    · exact (hHan j (Finset.mem_range.mpr (by omega))).continuousAt
  have hFcont := hcont F (fun i hi => (hz_coeff i hi).1) hFdeg_z
  have hGcont := hcont G (fun i hi => (hz_coeff i hi).2) hGdeg_z
  -- agreement at `z` via the dense separable locus
  haveI : (𝓝[{x : Fin (n + 1) → ℂ | x 0 ≠ 0}] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (dense_coord0_ne z)
  refine polynomial_eq_of_eventuallyEq_filter
    (l := 𝓝[{x : Fin (n + 1) → ℂ | x 0 ≠ 0}] z) nhdsWithin_le_nhds ?_ hFcont hGcont
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [hVopen.mem_nhds hz] with y hy hy0
  exact (hVsub y hy).1 hy0

/-- **Germ-irreducibility ⟹ `UnivIrreducibleGen`.** If `q` admits no factorisation into two
positive-degree monic `X`-power-at-`0` analytic families on a *full* neighbourhood of `0`, then it
admits none even *off the hyperplane* `{x 0 ≠ 0}` — because an off-hyperplane factorisation extends, by
the density extension, to a full-neighbourhood one. This is the M5 wiring discharging M4's
`UnivIrreducibleGen` hypothesis from the germ-irreducibility supplied by the Zariski axiom. -/
theorem univIrreducibleGen_of_germ {m : ℕ} (q : (Fin (n + 1) → ℂ) → Polynomial ℂ)
    (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun y => (q y).coeff i) (0 : Fin (n + 1) → ℂ))
    (hgerm : ¬ ∃ (dA dB : ℕ) (HA HB : (Fin (n + 1) → ℂ) → Polynomial ℂ),
      1 ≤ dA ∧ 1 ≤ dB ∧
      (∀ y, (HA y).Monic) ∧ (∀ y, (HA y).natDegree = dA) ∧
        (∀ i, AnalyticAt ℂ (fun y => (HA y).coeff i) 0) ∧ HA 0 = X ^ dA ∧
      (∀ y, (HB y).Monic) ∧ (∀ y, (HB y).natDegree = dB) ∧
        (∀ i, AnalyticAt ℂ (fun y => (HB y).coeff i) 0) ∧ HB 0 = X ^ dB ∧
      (∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℂ), q x = HA x * HB x)) :
    UnivIrreducibleGen q := by
  rintro ⟨dA, dB, HA, HB, hdA, hdB, hHAm, hHAd, hHAc, hHA0, hHBm, hHBd, hHBc, hHB0, heq_off⟩
  apply hgerm
  refine ⟨dA, dB, HA, HB, hdA, hdB, hHAm, hHAd, hHAc, hHA0, hHBm, hHBd, hHBc, hHB0, ?_⟩
  have hGan : ∀ i, AnalyticAt ℂ (fun y => (HA y * HB y).coeff i) (0 : Fin (n + 1) → ℂ) := fun i => by
    have hform : (fun y => (HA y * HB y).coeff i)
        = fun y => ∑ p ∈ Finset.antidiagonal i, (HA y).coeff p.1 * (HB y).coeff p.2 := by
      funext y; rw [Polynomial.coeff_mul]
    rw [hform]
    exact Finset.analyticAt_fun_sum _ fun p _ => (hHAc p.1).mul (hHBc p.2)
  exact polyFamily_eventuallyEq_of_coord0 (N := m + (dA + dB)) hcoeff hGan
    (Filter.Eventually.of_forall fun y => by rw [hdeg]; omega)
    (Filter.Eventually.of_forall fun y =>
      le_trans Polynomial.natDegree_mul_le (by rw [hHAd, hHBd]; omega))
    heq_off

/-- **`card ≤ 1` ⟹ single distinct root** (the M5 conclusion translation). A monic complex polynomial
of positive degree with at most one distinct root has exactly one: `∃ α, ∀ β, IsRoot β ↔ β = α`. This
turns `section_card_le_one` (M4) into the form of the Zariski axiom's conclusion. -/
theorem single_root_of_card_le_one {p : Polynomial ℂ} (hp : p.Monic) (hpos : 0 < p.natDegree)
    (hcard : p.roots.toFinset.card ≤ 1) : ∃ α : ℂ, ∀ β : ℂ, p.IsRoot β ↔ β = α := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root p
    (by rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hpos.ne')
  have hαmem : α ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hp.ne_zero).mpr hα)
  refine ⟨α, fun β => ⟨fun hβ => ?_, fun hβ => by rw [hβ]; exact hα⟩⟩
  exact Finset.card_le_one.mp hcard β
    (Multiset.mem_toFinset.mpr ((mem_roots hp.ne_zero).mpr hβ)) α hαmem

end CParamWiring
