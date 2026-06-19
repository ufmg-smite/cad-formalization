import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic

/-!
# M5 (e=1, sub-lemma C) — a uniform root bound near a base point

For a monic family `P` of constant degree `m` with coefficients continuous at `x₀`, all the roots of
`P w` are uniformly bounded for `w` near `x₀` (Cauchy's root bound `‖t‖ < cauchyBound (P w)`, with
`cauchyBound (P w)` continuous in the coefficients). This is the multivariate-base version of the
`h_bound` step inside `RoucheSeparation.roots_confined`, supplying M4's `hbdd` hypothesis.
-/

noncomputable section

open Polynomial Filter Metric
open scoped Topology NNReal

/-- **(C) Uniform root bound near a base point.** -/
theorem roots_bound_eventually {E : Type*} [TopologicalSpace E] (P : E → Polynomial ℂ) (m : ℕ)
    (x₀ : E) (hmonic : ∀ w, (P w).Monic) (hdeg : ∀ w, (P w).natDegree = m)
    (hcoeff : ∀ i, ContinuousAt (fun w => (P w).coeff i) x₀) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ∀ᶠ w in 𝓝 x₀, ∀ t ∈ (P w).roots.toFinset, ‖t‖ ≤ ε := by
  classical
  have hcoeff_m_one : ∀ w, (P w).coeff m = 1 := fun w => by
    have := (hmonic w).coeff_natDegree; rwa [hdeg w] at this
  set coeffSum : ℝ := ∑ i ∈ Finset.range m, ‖(P x₀).coeff i‖ with hcoeffSum
  set R : ℝ := coeffSum + 2 with hR_def
  have hcoeffSum_nn : 0 ≤ coeffSum := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨R, by positivity, ?_⟩
  set gbnd : E → ℝ := fun w => (∑ i ∈ Finset.range m, ‖(P w).coeff i‖) + 1 with hgbnd
  have hg_cont : ContinuousAt gbnd x₀ :=
    (tendsto_finset_sum _ fun i _ => (hcoeff i).norm).add continuousAt_const
  have hg_val : gbnd x₀ = coeffSum + 1 := rfl
  have hg_lt_R : coeffSum + 1 < R := by rw [hR_def]; linarith
  have hg_ev : ∀ᶠ w in 𝓝 x₀, gbnd w < R := hg_cont.eventually (gt_mem_nhds (hg_val ▸ hg_lt_R))
  filter_upwards [hg_ev] with w hgw t htmem
  have hroot : (P w).IsRoot t := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmonic w).ne_zero] at htmem; exact htmem
  have hfw_ne : P w ≠ 0 := (hmonic w).ne_zero
  have hcb := hroot.norm_lt_cauchyBound hfw_ne
  have hcb_le : (Polynomial.cauchyBound (P w) : ℝ) ≤ gbnd w := by
    have hlc : ‖(P w).leadingCoeff‖₊ = 1 := by
      rw [Polynomial.leadingCoeff, hdeg w, hcoeff_m_one w]; simp
    have hsup_le : Finset.sup (Finset.range m) (‖(P w).coeff ·‖₊)
        ≤ ∑ i ∈ Finset.range m, ‖(P w).coeff i‖₊ :=
      Finset.sup_le fun i hi => Finset.single_le_sum (f := fun i => ‖(P w).coeff i‖₊)
        (fun _ _ => zero_le _) hi
    calc (Polynomial.cauchyBound (P w) : ℝ)
        = ↑(Finset.sup (Finset.range m) (‖(P w).coeff ·‖₊)) + 1 := by
          rw [Polynomial.cauchyBound, hdeg w, hlc]; push_cast; ring
      _ ≤ ↑(∑ i ∈ Finset.range m, ‖(P w).coeff i‖₊) + 1 := by
          have := NNReal.coe_le_coe.mpr hsup_le; linarith
      _ = gbnd w := by simp only [hgbnd, NNReal.coe_sum, coe_nnnorm]
  have hlt : (‖t‖₊ : ℝ) < gbnd w := lt_of_lt_of_le (by exact_mod_cast hcb) hcb_le
  have hlt' : ‖t‖ < gbnd w := by rw [← coe_nnnorm]; exact hlt
  exact le_of_lt (lt_trans hlt' hgw)

end
