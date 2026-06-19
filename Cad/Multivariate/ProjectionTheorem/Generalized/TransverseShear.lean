import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-!
# A transverse shear sending a basis vector to a prescribed nonzero direction

For the M5b blow-up genericity we need, given a nonzero `ξ : Fin n → ℂ`, a continuous linear
*automorphism* `M` of `Fin n → ℂ` sending a coordinate basis vector to `ξ`. We build the elementary
shear `w ↦ w + (w i) • (ξ - eᵢ)` (invertible when `ξ i ≠ 0`, since `eᵢ ↦ ξ`) and compose with a
coordinate swap to move the active coordinate to any target index.
-/

noncomputable section

open scoped Topology

namespace TransverseShear

variable {n : ℕ}

/-- The shear linear map `w ↦ w + (w i) • (ξ - eᵢ)`. -/
def shearₗ (i : Fin n) (ξ : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id + (LinearMap.proj i).smulRight (ξ - Pi.single i 1)

/-- The shear, as a linear equivalence (invertible since `ξ i ≠ 0`). -/
def shearEquivₗ (i : Fin n) (ξ : Fin n → ℂ) (hξ : ξ i ≠ 0) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofLinear (shearₗ i ξ)
    (LinearMap.id - (ξ i)⁻¹ • (LinearMap.proj i).smulRight (ξ - Pi.single i 1))
    (by
      refine LinearMap.ext fun w => funext fun j => ?_
      simp only [LinearMap.comp_apply, shearₗ, LinearMap.add_apply, LinearMap.id_coe, id_eq,
        LinearMap.smulRight_apply, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne j i with hji | hji
      · subst hji; simp only [Pi.single_eq_same]; field_simp; ring
      · simp only [Pi.single_eq_of_ne hji, Pi.single_eq_same]; field_simp; ring)
    (by
      refine LinearMap.ext fun w => funext fun j => ?_
      simp only [LinearMap.comp_apply, shearₗ, LinearMap.add_apply, LinearMap.id_coe, id_eq,
        LinearMap.smulRight_apply, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne j i with hji | hji
      · subst hji; simp only [Pi.single_eq_same]; field_simp; ring
      · simp only [Pi.single_eq_of_ne hji, Pi.single_eq_same]; field_simp; ring)

lemma shearEquivₗ_apply (i : Fin n) (ξ : Fin n → ℂ) (hξ : ξ i ≠ 0) (w : Fin n → ℂ) :
    shearEquivₗ i ξ hξ w = w + (w i) • (ξ - Pi.single i 1) := rfl

/-- The shear sends `eᵢ` to `ξ`. -/
lemma shearEquivₗ_single (i : Fin n) (ξ : Fin n → ℂ) (hξ : ξ i ≠ 0) :
    shearEquivₗ i ξ hξ (Pi.single i 1) = ξ := by
  rw [shearEquivₗ_apply]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
  rcases eq_or_ne j i with hji | hji
  · subst hji; simp
  · simp [if_neg hji]

/-- The shear as a continuous linear equivalence (finite-dimensional). -/
def shearCLE (i : Fin n) (ξ : Fin n → ℂ) (hξ : ξ i ≠ 0) :
    (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  (shearEquivₗ i ξ hξ).toContinuousLinearEquiv

lemma shearCLE_single (i : Fin n) (ξ : Fin n → ℂ) (hξ : ξ i ≠ 0) :
    shearCLE i ξ hξ (Pi.single i 1) = ξ := shearEquivₗ_single i ξ hξ

/-- The coordinate-swap continuous linear equivalence (`w ↦ w ∘ swap i j`). -/
def swapCLE (i j : Fin n) : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap i j)).toContinuousLinearEquiv

lemma swapCLE_single (i j : Fin n) :
    swapCLE i j (Pi.single j 1) = Pi.single i 1 := by
  show (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap i j)) (Pi.single j 1) = Pi.single i 1
  rw [LinearEquiv.funCongrLeft_apply]
  funext a
  rw [LinearMap.funLeft_apply]
  rcases eq_or_ne a i with h | h
  · subst h; rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne
      (show Equiv.swap i j a ≠ j by
        rw [ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact h)]

/-- **A transverse automorphism sending `e_last` to a prescribed nonzero direction.** -/
lemma exists_transverseCLE {m : ℕ} (ξ : Fin (m + 1) → ℂ) (hξ : ξ ≠ 0) :
    ∃ M : (Fin (m + 1) → ℂ) ≃L[ℂ] (Fin (m + 1) → ℂ),
      M (Pi.single (Fin.last m) 1) = ξ := by
  obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h; push_neg at h; exact hξ (funext h)
  refine ⟨(swapCLE i (Fin.last m)).trans (shearCLE i ξ hi), ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, swapCLE_single, shearCLE_single]

end TransverseShear
