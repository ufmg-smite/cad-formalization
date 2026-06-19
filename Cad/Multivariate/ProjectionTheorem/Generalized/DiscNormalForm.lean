import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticDivCoord
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic
import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticGerm

/-!
# M5a — discriminant normal form ⟹ separability off the hyperplane

From an analytic `D` (the discriminant) that vanishes on the hyperplane `{z 0 = 0}` near `0` and whose
order along the section is constant, `D ≠ 0` off the hyperplane near `0`. The proof is an induction on
`r = order D 0`, each step one analytic division by the coordinate (`analytic_div_coord0`), tracking the
order via `order_mul_analytic` and `order_coord0_eq_one`.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace DiscNormalForm

variable {n : ℕ}

/-- The coordinate functional `z ↦ z 0` vanishes to order exactly `1` at any point of the hyperplane. -/
lemma order_coord0_eq_one {x : Fin (n + 1) → ℂ} (hx : x 0 = 0) :
    order ℂ (fun z : Fin (n + 1) → ℂ => z 0) x = 1 := by
  have h1 : (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := by norm_cast
  rw [h1, order_eq_natCast_iff]
  refine ⟨fun m hm => ?_, ?_⟩
  · interval_cases m
    ext v
    simp [iteratedFDeriv_zero_apply, hx]
  · intro hcon
    have hap : iteratedFDeriv ℂ 1 (fun z : Fin (n + 1) → ℂ => z 0) x (fun _ => Pi.single 0 1) = 0 := by
      rw [hcon]; rfl
    rw [iteratedFDeriv_one_apply] at hap
    have hfd : fderiv ℂ (fun z : Fin (n + 1) → ℂ => z 0) x
        = ContinuousLinearMap.proj (0 : Fin (n + 1)) :=
      (ContinuousLinearMap.proj (0 : Fin (n + 1)) : (Fin (n + 1) → ℂ) →L[ℂ] ℂ).fderiv
    rw [hfd] at hap
    simp only [ContinuousLinearMap.proj_apply, Pi.single_eq_same] at hap
    exact one_ne_zero hap

/-- `order = 0` forces a nonzero value. -/
lemma value_ne_zero_of_order_eq_zero {D : (Fin (n + 1) → ℂ) → ℂ} {x : Fin (n + 1) → ℂ}
    (h : order ℂ D x = 0) : D x ≠ 0 := by
  intro hD
  have hz : iteratedFDeriv ℂ 0 D x = 0 := by ext v; simp [iteratedFDeriv_zero_apply, hD]
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) by norm_cast, order_eq_natCast_iff] at h
  exact h.2 hz

/-- `fun z => z 0` is analytic everywhere. -/
lemma analyticAt_coord0 (p : Fin (n + 1) → ℂ) :
    AnalyticAt ℂ (fun z : Fin (n + 1) → ℂ => z 0) p :=
  (ContinuousLinearMap.proj (0 : Fin (n + 1)) : (Fin (n + 1) → ℂ) →L[ℂ] ℂ).analyticAt p

/-- **The order arithmetic step.** If `D = z₀·G` near a hyperplane point `w` (with `G` analytic),
`order D w = order G w + 1`. -/
lemma order_div_step {D G : (Fin (n + 1) → ℂ) → ℂ} {w : Fin (n + 1) → ℂ} (hw0 : w 0 = 0)
    (hGw : AnalyticAt ℂ G w) (heq : D =ᶠ[𝓝 w] fun z => z 0 * G z) :
    order ℂ D w = order ℂ G w + 1 := by
  rw [order_congr_of_eventuallyEq' heq,
    order_mul_analytic (fun z => z 0) G w (analyticAt_coord0 w) hGw, order_coord0_eq_one hw0,
    add_comm]

/-- **M5a core (separability off the hyperplane).** An analytic `D` vanishing on `{z 0 = 0}` near `0`
with finite, section-constant order is nonzero off the hyperplane near `0`. Induction on
`(order D 0).toNat`, each step one analytic division by the coordinate. -/
lemma sep_aux (r : ℕ) : ∀ (D : (Fin (n + 1) → ℂ) → ℂ),
    AnalyticAt ℂ D 0 → (∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 = 0 → D z = 0) →
    (order ℂ D 0).toNat = r → order ℂ D 0 ≠ ⊤ →
    (∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
      order ℂ D w = order ℂ D 0) →
    ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 ≠ 0 → D z ≠ 0 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro D hDan hvanish hrtoNat hrne hconst
    -- one division `D = z₀ · G`
    obtain ⟨G, hGan, hGeq⟩ := AnalyticDivCoord.analytic_div_coord0 (x₀ := (0 : Fin (n + 1) → ℂ)) rfl hDan hvanish
    have hGeq0 : D =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] fun z => z 0 * G z := hGeq
    have hordD0 : order ℂ D 0 = order ℂ G 0 + 1 := order_div_step rfl hGan hGeq0
    rcases eq_or_ne (order ℂ G 0) 0 with hGo | hGo
    · -- base case: `G 0 ≠ 0`, so `G ≠ 0` near `0`, hence `D = z₀ G ≠ 0` off the hyperplane
      have hGne0 : G 0 ≠ 0 := value_ne_zero_of_order_eq_zero hGo
      have hGne : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), G z ≠ 0 :=
        hGan.continuousAt.eventually_ne hGne0
      filter_upwards [hGeq, hGne] with z hDz hGz hz0
      rw [hDz]; exact mul_ne_zero hz0 hGz
    · -- inductive case: peel `z₀` and recurse on `G`
      have hGne_top : order ℂ G 0 ≠ ⊤ := by
        intro h; apply hrne; rw [hordD0, h]; simp
      set r' := (order ℂ G 0).toNat with hr'def
      have hGcoe : order ℂ G 0 = (r' : ℕ∞) := (ENat.coe_toNat hGne_top).symm
      have hrr' : r = r' + 1 := by
        have hDcoe : order ℂ D 0 = ((r' + 1 : ℕ) : ℕ∞) := by rw [hordD0, hGcoe]; push_cast; ring
        rw [← hrtoNat, hDcoe]; simp
      -- the factorization holds on an open neighbourhood `V`
      obtain ⟨V, hVeq, hVopen, hV0⟩ := _root_.eventually_nhds_iff.mp hGeq
      have hGan_ev : ∀ᶠ w in 𝓝 (0 : Fin (n + 1) → ℂ), AnalyticAt ℂ G w := hGan.eventually_analyticAt
      -- order constancy for `G` along the section
      have hGconst : ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
          order ℂ G w = order ℂ G 0 := by
        filter_upwards [hconst, hGan_ev.filter_mono nhdsWithin_le_nhds,
          (nhdsWithin_le_nhds (hVopen.mem_nhds hV0) : V ∈ 𝓝[_] (0 : Fin (n + 1) → ℂ)),
          (eventually_mem_nhdsWithin :
            ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
              w ∈ {z : Fin (n + 1) → ℂ | z 0 = 0})] with w hDw hGw_an hwV hw_mem
        have hw0 : w 0 = 0 := hw_mem
        have heqw : D =ᶠ[𝓝 w] fun z => z 0 * G z :=
          Filter.eventually_of_mem (hVopen.mem_nhds hwV) (fun z hz => hVeq z hz)
        have hstep : order ℂ D w = order ℂ G w + 1 := order_div_step hw0 hGw_an heqw
        rw [hstep] at hDw; rw [hordD0] at hDw
        exact WithTop.add_right_cancel (by simp) hDw
      -- `G` vanishes on the section (order `≥ 1` there)
      have hGvanish : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 = 0 → G z = 0 := by
        rw [eventually_nhdsWithin_iff] at hGconst
        filter_upwards [hGconst] with z hzord hz0
        by_contra hGz
        exact hGo ((hzord hz0).symm.trans (order_eq_zero_of_ne G z hGz))
      -- recurse on `G`, then `D = z₀ G ≠ 0` off the hyperplane
      have hGsep := ih r' (by omega) G hGan hGvanish rfl hGne_top hGconst
      filter_upwards [hGsep, hGeq] with z hGz hDz hz0
      rw [hDz]; exact mul_ne_zero hz0 (hGz hz0)

/-- **Discriminant normal form (explicit coordinate-`0` factorization).** Same hypotheses as `sep_aux`,
but returning the explicit witness of the normal form: an analytic `G` with `G 0 ≠ 0` and
`D = (z 0)ʳ · G` near `0` (where `r = order D 0`). Same induction as `sep_aux`, accumulating the peeled
coordinate factors into a single power. This is the form consumed by the Puiseux branch-order analysis
(transverse-slice order `= r`). -/
lemma exists_coord0_pow_factor (r : ℕ) : ∀ (D : (Fin (n + 1) → ℂ) → ℂ),
    AnalyticAt ℂ D 0 → (∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 = 0 → D z = 0) →
    (order ℂ D 0).toNat = r → order ℂ D 0 ≠ ⊤ →
    (∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
      order ℂ D w = order ℂ D 0) →
    ∃ G : (Fin (n + 1) → ℂ) → ℂ, AnalyticAt ℂ G 0 ∧ G 0 ≠ 0 ∧
      D =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] fun z => (z 0) ^ r * G z := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro D hDan hvanish hrtoNat hrne hconst
    obtain ⟨G, hGan, hGeq⟩ := AnalyticDivCoord.analytic_div_coord0
      (x₀ := (0 : Fin (n + 1) → ℂ)) rfl hDan hvanish
    have hordD0 : order ℂ D 0 = order ℂ G 0 + 1 := order_div_step rfl hGan hGeq
    rcases eq_or_ne (order ℂ G 0) 0 with hGo | hGo
    · -- base case: `r = 1`, `D = z₀ · G` with `G 0 ≠ 0`
      have hGne0 : G 0 ≠ 0 := value_ne_zero_of_order_eq_zero hGo
      have hr1 : r = 1 := by
        have hD1 : order ℂ D 0 = ((1 : ℕ) : ℕ∞) := by rw [hordD0, hGo]; norm_num
        rw [← hrtoNat, hD1]; simp
      refine ⟨G, hGan, hGne0, ?_⟩
      filter_upwards [hGeq] with z hz
      rw [hz, hr1, pow_one]
    · -- inductive case: peel `z₀`, recurse on `G`, accumulate the power
      have hGne_top : order ℂ G 0 ≠ ⊤ := by intro h; apply hrne; rw [hordD0, h]; simp
      set r' := (order ℂ G 0).toNat with hr'def
      have hGcoe : order ℂ G 0 = (r' : ℕ∞) := (ENat.coe_toNat hGne_top).symm
      have hrr' : r = r' + 1 := by
        have hDcoe : order ℂ D 0 = ((r' + 1 : ℕ) : ℕ∞) := by rw [hordD0, hGcoe]; push_cast; ring
        rw [← hrtoNat, hDcoe]; simp
      obtain ⟨V, hVeq, hVopen, hV0⟩ := _root_.eventually_nhds_iff.mp hGeq
      have hGan_ev : ∀ᶠ w in 𝓝 (0 : Fin (n + 1) → ℂ), AnalyticAt ℂ G w := hGan.eventually_analyticAt
      have hGconst : ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
          order ℂ G w = order ℂ G 0 := by
        filter_upwards [hconst, hGan_ev.filter_mono nhdsWithin_le_nhds,
          (nhdsWithin_le_nhds (hVopen.mem_nhds hV0) : V ∈ 𝓝[_] (0 : Fin (n + 1) → ℂ)),
          (eventually_mem_nhdsWithin :
            ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
              w ∈ {z : Fin (n + 1) → ℂ | z 0 = 0})] with w hDw hGw_an hwV hw_mem
        have hw0 : w 0 = 0 := hw_mem
        have heqw : D =ᶠ[𝓝 w] fun z => z 0 * G z :=
          Filter.eventually_of_mem (hVopen.mem_nhds hwV) (fun z hz => hVeq z hz)
        have hstep : order ℂ D w = order ℂ G w + 1 := order_div_step hw0 hGw_an heqw
        rw [hstep] at hDw; rw [hordD0] at hDw
        exact WithTop.add_right_cancel (by simp) hDw
      have hGvanish : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 = 0 → G z = 0 := by
        rw [eventually_nhdsWithin_iff] at hGconst
        filter_upwards [hGconst] with z hzord hz0
        by_contra hGz
        exact hGo ((hzord hz0).symm.trans (order_eq_zero_of_ne G z hGz))
      obtain ⟨G', hG'an, hG'ne, hG'eq⟩ := ih r' (by omega) G hGan hGvanish rfl hGne_top hGconst
      refine ⟨G', hG'an, hG'ne, ?_⟩
      filter_upwards [hGeq, hG'eq] with z hz hz'
      rw [hz, hz', hrr']
      ring

/-- **M5a (separability off the hyperplane).** An analytic `D` with `D 0 = 0`, finite order at `0`, and
order constant along the section `{z 0 = 0}` is **nonzero off the hyperplane** near `0`. (`D` vanishes
on the section — order `≥ 1` there — and the induction `sep_aux` peels coordinate factors.) -/
theorem sep_off_hyperplane (D : (Fin (n + 1) → ℂ) → ℂ) (hDan : AnalyticAt ℂ D 0)
    (hD0 : D 0 = 0) (hrne : order ℂ D 0 ≠ ⊤)
    (hconst : ∀ᶠ w in 𝓝[{z : Fin (n + 1) → ℂ | z 0 = 0}] (0 : Fin (n + 1) → ℂ),
      order ℂ D w = order ℂ D 0) :
    ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 ≠ 0 → D z ≠ 0 := by
  have hord0_ne : order ℂ D 0 ≠ 0 := fun h => value_ne_zero_of_order_eq_zero h hD0
  have hconst' := eventually_nhdsWithin_iff.mp hconst
  have hvanish : ∀ᶠ z in 𝓝 (0 : Fin (n + 1) → ℂ), z 0 = 0 → D z = 0 := by
    filter_upwards [hconst'] with z hzord hz0
    by_contra hDz
    exact hord0_ne ((hzord hz0).symm.trans (order_eq_zero_of_ne D z hDz))
  exact sep_aux (order ℂ D 0).toNat D hDan hvanish rfl hrne hconst

end DiscNormalForm
