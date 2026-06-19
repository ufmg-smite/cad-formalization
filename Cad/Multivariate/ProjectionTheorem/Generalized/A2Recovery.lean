import Cad.Multivariate.ProjectionTheorem.Generalized.RealRecovery

/-!
# A2 recovery core — single-branch real delineation (PROVEN, no new axioms)

This is the genuine real-analytic content behind the A2 axiom, proved here as a theorem.

`real_delineation_of_single_branch`: given a real-analytic family `fam` and **one** holomorphic
cluster section `ψ : ℂˢ → ℂ` (analytic, `ψ 0 = 0`) that parametrizes the **unique** complex root of
the complexified family `(fam y).map (ℝ→ℂ)` within a cluster radius `δ₀` (for real `y` near `0`), with
that root having constant multiplicity `m`, the **real** root of `fam y` near `0` is a single real-
analytic function `η` with `η 0 = 0` and multiplicity `m`.

The crux is real-valuedness: a real polynomial's complex roots are conjugate-closed, so the *unique*
root in the cluster ball is fixed by conjugation, hence real. Schwarz reflection
(`real_root_function`, already proven) then recovers `η = Re ∘ ψ ∘ realEmbedding`.

This is the single-branch (`r = 1`) specialization of the A2 axiom
`real_delineation_of_complex_sections`; `r = 1` is the faithful picture under order-preservation
(a multiplicity-`m` root that does not split is one analytic branch of multiplicity `m`).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s : ℕ}

/-- A real polynomial's complexification has conjugate-closed roots. -/
private theorem isRoot_conj_of_real (p : Polynomial ℝ) (z : ℂ)
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) :
    (p.map (algebraMap ℝ ℂ)).IsRoot (starRingEnd ℂ z) := by
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ := by
    ext r; simp [Complex.coe_algebraMap]
  have key : (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((p.map (algebraMap ℝ ℂ)).eval z) := by
    rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp]
  rw [Polynomial.IsRoot.def, key]
  rw [Polynomial.IsRoot.def] at hz
  rw [hz, map_zero]

/-- Real-root membership transfers across the complexification `ℝ → ℂ`. -/
private theorem isRoot_map_ofReal (p : Polynomial ℝ) (α : ℝ) :
    p.IsRoot α ↔ (p.map (algebraMap ℝ ℂ)).IsRoot ((α : ℂ)) := by
  have heval : (p.map (algebraMap ℝ ℂ)).eval ((α : ℂ)) = ((p.eval α : ℝ) : ℂ) := by
    rw [Polynomial.eval_map,
        show ((α : ℂ)) = algebraMap ℝ ℂ α by rw [Complex.coe_algebraMap],
        Polynomial.eval₂_at_apply, Complex.coe_algebraMap]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, heval, Complex.ofReal_eq_zero]

/-- **A2 recovery core (single branch).** One real-valued branch ⟹ one real-analytic root
function with the full delineation. -/
theorem real_delineation_of_single_branch
    (fam : (Fin s → ℝ) → Polynomial ℝ)
    (m : ℕ)
    (ψ : (Fin s → ℂ) → ℂ) (hψ_an : AnalyticAt ℂ ψ 0) (hψ0 : ψ 0 = 0)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hcover : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ α : ℂ, ‖α‖ < δ₀ →
      (((fam y).map (algebraMap ℝ ℂ)).IsRoot α ↔ α = ψ (realEmbedding s y)))
    (hmult : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      ((fam y).map (algebraMap ℝ ℂ)).rootMultiplicity (ψ (realEmbedding s y)) = m) :
    ∃ (V : Set (Fin s → ℝ)) (δ : ℝ), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧ 0 < δ ∧
      ∃ (η : (Fin s → ℝ) → ℝ),
        AnalyticOn ℝ η V ∧ η 0 = 0 ∧
        (∀ y ∈ V, |η y| < δ) ∧
        (∀ y ∈ V, ∀ α : ℝ, (|α| < δ ∧ (fam y).IsRoot α) ↔ α = η y) ∧
        (∀ y ∈ V, (fam y).rootMultiplicity (η y) = m) ∧
        (∀ y ∈ V, (↑(η y) : ℂ) = ψ (realEmbedding s y)) := by
  have hemb0 : realEmbedding s (0 : Fin s → ℝ) = 0 := map_zero _
  -- `y ↦ ψ (realEmbedding s y)` is continuous at `0` with value `0`
  have hψr0 : ψ (realEmbedding s (0 : Fin s → ℝ)) = 0 := by rw [hemb0, hψ0]
  have hψr_cont : ContinuousAt (fun y : Fin s → ℝ => ψ (realEmbedding s y)) 0 := by
    have h1 : ContinuousAt ψ (realEmbedding s (0 : Fin s → ℝ)) := by
      rw [hemb0]; exact hψ_an.continuousAt
    exact h1.comp (realEmbedding s).continuous.continuousAt
  -- the branch stays inside the cluster ball near `0`
  have hsmall : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ‖ψ (realEmbedding s y)‖ < δ₀ := by
    have hmem : (fun y : Fin s → ℝ => ψ (realEmbedding s y)) ⁻¹' Metric.ball 0 δ₀
        ∈ 𝓝 (0 : Fin s → ℝ) :=
      hψr_cont.preimage_mem_nhds (by
        show Metric.ball 0 δ₀ ∈ 𝓝 (ψ (realEmbedding s (0 : Fin s → ℝ)))
        rw [hψr0]; exact Metric.ball_mem_nhds 0 hδ₀)
    filter_upwards [hmem] with y hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  -- KEY: the unique cluster root is conjugation-fixed, hence real
  have hreal : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (ψ (realEmbedding s y)).im = 0 := by
    filter_upwards [hcover, hsmall] with y hcov hsm
    have hroot : ((fam y).map (algebraMap ℝ ℂ)).IsRoot (ψ (realEmbedding s y)) :=
      (hcov (ψ (realEmbedding s y)) hsm).mpr rfl
    have hcroot : ((fam y).map (algebraMap ℝ ℂ)).IsRoot
        (starRingEnd ℂ (ψ (realEmbedding s y))) := isRoot_conj_of_real _ _ hroot
    have hcsm : ‖starRingEnd ℂ (ψ (realEmbedding s y))‖ < δ₀ := by
      rw [RCLike.norm_conj]; exact hsm
    have heq : starRingEnd ℂ (ψ (realEmbedding s y)) = ψ (realEmbedding s y) :=
      (hcov _ hcsm).mp hcroot
    exact Complex.conj_eq_iff_im.mp heq
  -- Schwarz reflection: real-analytic recovery `η = Re ∘ ψ ∘ realEmbedding`
  obtain ⟨hη_an, hη0, hη_recover⟩ := real_root_function ψ hψ_an hψ0 hreal
  -- continuity of `η` at `0` for the ball bound
  have hη_cont : ContinuousAt (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) 0 :=
    hη_an.continuousAt
  have hηsmall : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), |(ψ (realEmbedding s y)).re| < δ₀ := by
    have hmem : (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) ⁻¹' Metric.ball 0 δ₀
        ∈ 𝓝 (0 : Fin s → ℝ) :=
      hη_cont.preimage_mem_nhds (by
        show Metric.ball 0 δ₀ ∈ 𝓝 ((ψ (realEmbedding s (0 : Fin s → ℝ))).re)
        rw [hψr0]; simpa using Metric.ball_mem_nhds (0 : ℝ) hδ₀)
    filter_upwards [hmem] with y hy
    simpa [Metric.mem_ball, Real.dist_eq] using hy
  -- bundle everything into one eventual neighborhood and extract an open `V`
  have hcomb : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      AnalyticAt ℝ (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) y ∧
      ‖ψ (realEmbedding s y)‖ < δ₀ ∧
      (∀ α : ℂ, ‖α‖ < δ₀ →
        (((fam y).map (algebraMap ℝ ℂ)).IsRoot α ↔ α = ψ (realEmbedding s y))) ∧
      (((ψ (realEmbedding s y)).re : ℂ) = ψ (realEmbedding s y)) ∧
      (((fam y).map (algebraMap ℝ ℂ)).rootMultiplicity (ψ (realEmbedding s y)) = m) ∧
      |(ψ (realEmbedding s y)).re| < δ₀ := by
    filter_upwards [hη_an.eventually_analyticAt, hsmall, hcover, hη_recover, hmult, hηsmall]
      with y h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨V, hVsub, hVopen, hV0⟩ := eventually_nhds_iff.mp hcomb
  refine ⟨V, δ₀, hVopen, hV0, hδ₀, fun x => (ψ (realEmbedding s x)).re, ?_, hη0, ?_, ?_, ?_, ?_⟩
  · -- AnalyticOn ℝ η V
    exact fun y hy => ((hVsub y hy).1).analyticWithinAt
  · -- |η y| < δ
    exact fun y hy => (hVsub y hy).2.2.2.2.2
  · -- real-root iff
    intro y hy α
    obtain ⟨-, hsm, hcov, hrec, -, -⟩ := hVsub y hy
    constructor
    · rintro ⟨hα_lt, hα_root⟩
      have hmap : ((fam y).map (algebraMap ℝ ℂ)).IsRoot ((α : ℂ)) :=
        (isRoot_map_ofReal (fam y) α).mp hα_root
      have hnorm : ‖(α : ℂ)‖ < δ₀ := by simpa [Complex.norm_real] using hα_lt
      have hαψ : ((α : ℂ)) = ψ (realEmbedding s y) := (hcov _ hnorm).mp hmap
      have : ((α : ℂ)) = ((ψ (realEmbedding s y)).re : ℂ) := by rw [hαψ, hrec]
      exact Complex.ofReal_inj.mp this
    · rintro rfl
      refine ⟨(hVsub y hy).2.2.2.2.2, ?_⟩
      rw [isRoot_map_ofReal, hrec]
      exact (hcov _ hsm).mpr rfl
  · -- multiplicity
    intro y hy
    obtain ⟨-, -, -, hrec, hmlt, -⟩ := hVsub y hy
    rw [eq_rootMultiplicity_map (f := algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective,
        Complex.coe_algebraMap, hrec]
    exact hmlt
  · -- branch reality: `↑(η y) = ψ (realEmbedding s y)`
    intro y hy
    exact (hVsub y hy).2.2.2.1

end
