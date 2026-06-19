import Cad.Multivariate.ProjectionTheorem.Generalized.Lifting

/-!
# Phase F1 wiring — per-section real recovery

`real_root_function` packages the proven Schwarz-recovery lemma `real_section_of_real_valued`: a
complex root section `ψ : ℂˢ → ℂ` that is analytic at `0`, vanishes at `0`, and is real-valued on the
real slice gives a real-analytic root function `η := Re ∘ ψ ∘ realEmbedding : ℝˢ → ℝ` with `η 0 = 0`
and the recovery `(η x : ℂ) = ψ (realEmbedding x)` near `0`. This is the per-section building block
used to turn the complex Zariski sections (`single_cluster_complex`) into the real root functions of
the delineability conclusion.
-/

noncomputable section

open Filter
open scoped Topology

/-- **F1 per section.** A complex section real-valued on the real slice yields a real-analytic root
function `η` with `η 0 = 0` and the recovery relation. -/
theorem real_root_function {s : ℕ} (ψ : (Fin s → ℂ) → ℂ)
    (hψ_an : AnalyticAt ℂ ψ 0) (hψ0 : ψ 0 = 0)
    (hreal : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ), (ψ (realEmbedding s x)).im = 0) :
    AnalyticAt ℝ (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) 0 ∧
    (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) (0 : Fin s → ℝ) = 0 ∧
    (∀ᶠ x in 𝓝 (0 : Fin s → ℝ),
      ((ψ (realEmbedding s x)).re : ℂ) = ψ (realEmbedding s x)) := by
  have hemb0 : realEmbedding s (0 : Fin s → ℝ) = 0 := map_zero _
  have hψ_emb : AnalyticAt ℂ ψ (realEmbedding s (0 : Fin s → ℝ)) := by rw [hemb0]; exact hψ_an
  obtain ⟨hη_an, hrecover⟩ := real_section_of_real_valued ψ 0 hψ_emb hreal
  refine ⟨hη_an, ?_, hrecover⟩
  show (ψ (realEmbedding s (0 : Fin s → ℝ))).re = 0
  rw [hemb0, hψ0]; simp

end
