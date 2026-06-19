import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# M5 (e=1, sub-lemma B-helper) — separability from a nonvanishing discriminant

Over `ℂ`, a monic polynomial of positive degree with nonzero discriminant is separable. (The project
already has the converse `discr_ne_zero_of_squarefree`; this is the direction the disc-normal-form route
needs: `disc ≠ 0 ⟹ Separable`, via the resultant criterion `resultant f f' = 0 ↔ ¬IsCoprime` and
`resultant f f' = ±lc·disc f`.)
-/

noncomputable section

open Polynomial

/-- `(derivative f).natDegree = f.natDegree - 1` over a characteristic-zero domain. -/
private lemma natDegree_derivative_eq' {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (f : Polynomial S) (hf : 0 < f.natDegree) :
    f.derivative.natDegree = f.natDegree - 1 := by
  have hf_ne : f ≠ 0 := ne_zero_of_natDegree_gt hf
  apply le_antisymm (natDegree_derivative_le f)
  have hlc : f.derivative.coeff (f.natDegree - 1) ≠ 0 := by
    rw [coeff_derivative]
    have hsub : f.natDegree - 1 + 1 = f.natDegree := Nat.succ_pred_eq_of_pos hf
    refine mul_ne_zero ?_ ?_
    · rw [hsub]; exact leadingCoeff_ne_zero.mpr hf_ne
    · suffices h : (↑(f.natDegree - 1 + 1) : S) ≠ 0 by
        simpa [Nat.cast_add, Nat.cast_one] using h
      rw [hsub]; exact Nat.cast_ne_zero.mpr (by omega)
  exact Polynomial.le_natDegree_of_ne_zero hlc

/-- **Separability from a nonvanishing discriminant (over `ℂ`).** A monic complex polynomial of positive
degree with `discr ≠ 0` is separable. -/
theorem separable_of_discr_ne_zero {f : ℂ[X]} (hmonic : f.Monic) (hpos : 0 < f.natDegree)
    (hdisc : f.discr ≠ 0) : f.Separable := by
  by_contra hns
  rw [Polynomial.separable_def] at hns
  have hf_ne : f ≠ 0 := hmonic.ne_zero
  have hdeg_pos : 0 < f.degree := by rw [degree_eq_natDegree hf_ne]; exact_mod_cast hpos
  have hres0 : Polynomial.resultant f (derivative f) = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hf_ne, hns⟩
  have hdeg_der : (derivative f).natDegree = f.natDegree - 1 := natDegree_derivative_eq' f hpos
  have hres_eq : Polynomial.resultant f (derivative f) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr := by
    change Polynomial.resultant f (derivative f) f.natDegree (derivative f).natDegree = _
    rw [hdeg_der]; exact Polynomial.resultant_deriv hdeg_pos
  rw [hres_eq, hmonic.leadingCoeff, mul_one] at hres0
  rcases mul_eq_zero.mp hres0 with h | h
  · exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h
  · exact hdisc h

/-- **The discriminant of `X^d` vanishes for `d ≥ 2`** (`0` is a repeated root). -/
theorem discr_X_pow_eq_zero {d : ℕ} (hd : 2 ≤ d) : (X ^ d : ℂ[X]).discr = 0 := by
  by_contra h
  have hsep : (X ^ d : ℂ[X]).Separable :=
    separable_of_discr_ne_zero (monic_X_pow d) (by rw [natDegree_X_pow]; omega) h
  rw [Polynomial.separable_def] at hsep
  have hXd : (X : ℂ[X]) ∣ X ^ d := dvd_pow_self X (by omega : d ≠ 0)
  have hder : (X : ℂ[X]) ∣ derivative (X ^ d) := by
    rw [derivative_X_pow]
    exact Dvd.dvd.mul_left (dvd_pow_self X (by omega : d - 1 ≠ 0)) _
  exact Polynomial.not_isUnit_X (hsep.isUnit_of_dvd' hXd hder)

end
