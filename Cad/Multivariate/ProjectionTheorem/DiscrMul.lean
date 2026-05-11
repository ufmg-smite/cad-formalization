import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Discriminant product formula: `discr(f * g) = discr(f) * res(f, g)² * discr(g)`

Helper lemmas for proving the discriminant product formula.
-/

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-! ### Leading coefficient helper -/

omit [IsDomain R] [CharZero R] in
private lemma natDegree_pos_leadingCoeff_ne_zero {f : R[X]} (hf : 0 < f.natDegree) :
    f.leadingCoeff ≠ 0 :=
  leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hf)

/-! ### Derivative degree in CharZero -/

/-- In characteristic zero, if `0 < natDegree f`, then `natDegree(f') = natDegree(f) - 1`. -/
lemma natDegree_derivative_charZero {f : R[X]} (hf : 0 < f.natDegree) :
    f.derivative.natDegree = f.natDegree - 1 :=
  natDegree_eq_of_degree_eq_some (degree_derivative_eq f hf)

/-! ### Resultant of fg with (fg)' -/

omit [IsDomain R] [CharZero R] in
/-- `res(f, f'g + fg') = res(f, f'g)` because `fg'` is a multiple of `f`. -/
lemma resultant_fg_deriv_left (f g : R[X]) (hg : 0 < g.natDegree) :
    resultant f (f.derivative * g + f * g.derivative) f.natDegree
      (f.natDegree + g.natDegree - 1) =
    resultant f (f.derivative * g) f.natDegree (f.natDegree + g.natDegree - 1) := by
  apply Polynomial.resultant_add_mul_right
  · exact le_tsub_of_add_le_left (by
      linarith [Polynomial.natDegree_derivative_le g, Nat.sub_add_cancel hg])
  · rfl

omit [IsDomain R] [CharZero R] in
/-- `res(g, f'g + fg') = res(g, fg')` because `f'g` is a multiple of `g`. -/
lemma resultant_fg_deriv_right (f g : R[X]) (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    resultant g (f.derivative * g + f * g.derivative) g.natDegree
      (f.natDegree + g.natDegree - 1) =
    resultant g (f * g.derivative) g.natDegree (f.natDegree + g.natDegree - 1) := by
  rw [show f.derivative * g + f * g.derivative
        = f * g.derivative + g * f.derivative by ring]
  have hdf : f.derivative.natDegree + g.natDegree ≤ f.natDegree + g.natDegree - 1 := by
    have := Polynomial.natDegree_derivative_le f
    omega
  exact Polynomial.resultant_add_mul_right g (f * g.derivative) f.derivative
    g.natDegree (f.natDegree + g.natDegree - 1) hdf le_rfl

/-- Split `res(f, f'·g)` into `res(f, f') * res(f, g)` using `resultant_mul_right`. -/
lemma resultant_split_fg_left (f g : R[X]) (hf : 0 < f.natDegree) :
    resultant f (f.derivative * g) f.natDegree (f.natDegree + g.natDegree - 1) =
    resultant f f.derivative * resultant f g := by
  rw [← Polynomial.resultant_mul_right]
  · rw [natDegree_derivative_charZero hf, tsub_add_eq_add_tsub hf]
  · rfl

/-- Split `res(g, f·g')` into `res(g, f) * res(g, g')` using `resultant_mul_right`. -/
lemma resultant_split_fg_right (f g : R[X]) (hg : 0 < g.natDegree) :
    resultant g (f * g.derivative) g.natDegree (f.natDegree + g.natDegree - 1) =
    resultant g f * resultant g g.derivative := by
  convert Polynomial.resultant_mul_right g f (derivative g) g.natDegree _ using 2
  · rw [natDegree_derivative_charZero hg, Nat.add_sub_assoc (Nat.succ_le_of_lt hg)]
  · rfl

/-! ### Sign arithmetic -/

/-- The sign identity: `n(n-1)/2 + nm + m(m-1)/2 = (n+m)(n+m-1)/2`. -/
lemma sign_exponent_identity (n m : ℕ) :
    n * (n - 1) / 2 + n * m + m * (m - 1) / 2 = (n + m) * (n + m - 1) / 2 := by
  rcases n with _ | n <;> rcases m with _ | m <;> simp
  exact (Nat.div_eq_of_eq_mul_left zero_lt_two (by
    linarith [Nat.div_mul_cancel
        (show 2 ∣ (n + 1) * n from Nat.dvd_of_mod_eq_zero (by
          norm_num [Nat.add_mod, Nat.mod_two_of_bodd])),
      Nat.div_mul_cancel
        (show 2 ∣ (m + 1) * m from Nat.dvd_of_mod_eq_zero (by
          norm_num [Nat.add_mod, Nat.mod_two_of_bodd]))])).symm

/-
**Theorem 2.3.3** (McCallum PhD, p.12).
For non-constant polynomials `f, g` over an integral domain of characteristic zero:
`discr(f · g) = discr(f) · res(f, g)² · discr(g)`.
-/
theorem discr_mul_eq
    (f g : R[X]) (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    discr (f * g) = discr f * resultant f g ^ 2 * discr g := by
  have h_fg := Polynomial.resultant_deriv (show 0 < (f * g).degree by
    rw [Polynomial.degree_mul]
    exact add_pos_of_pos_of_nonneg
      (Polynomial.natDegree_pos_iff_degree_pos.mp hf)
      (Polynomial.natDegree_pos_iff_degree_pos.mp hg).le)
  have hdf := Polynomial.natDegree_derivative_le f
  have hdg := Polynomial.natDegree_derivative_le g
  have h_resultant_def : resultant (f * g) (f.derivative * g + f * g.derivative)
        (f.natDegree + g.natDegree) (f.natDegree + g.natDegree - 1) =
      resultant f (f.derivative * g + f * g.derivative) f.natDegree
          (f.natDegree + g.natDegree - 1) *
      resultant g (f.derivative * g + f * g.derivative) g.natDegree
          (f.natDegree + g.natDegree - 1) := by
    rw [← Polynomial.resultant_mul_left]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by omega)
    · exact Polynomial.natDegree_mul_le.trans (by omega)
  have h_resultant_comm : resultant g f g.natDegree f.natDegree =
      (-1) ^ (f.natDegree * g.natDegree) * resultant f g f.natDegree g.natDegree := by
    rw [Polynomial.resultant_comm]; ring
  -- Substitute the expressions for the resultants into the equation.
  have hlc_ne : f.leadingCoeff * g.leadingCoeff ≠ 0 :=
    mul_ne_zero (natDegree_pos_leadingCoeff_ne_zero hf)
      (natDegree_pos_leadingCoeff_ne_zero hg)
  have h_subst : (-1) ^ ((f.natDegree + g.natDegree) * ((f.natDegree + g.natDegree) - 1) / 2) * (f * g).leadingCoeff * (f * g).discr =
    ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr) * (resultant f g f.natDegree g.natDegree) *
    ((-1) ^ (f.natDegree * g.natDegree) * (resultant f g f.natDegree g.natDegree)) *
    ((-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.leadingCoeff * g.discr) := by
    convert h_resultant_def using 1
    · convert h_fg.symm using 2
      · rw [Polynomial.natDegree_mul' hlc_ne]
      · rw [Polynomial.derivative_mul]
      · rw [Polynomial.natDegree_mul' hlc_ne]
      · rw [Polynomial.natDegree_mul' hlc_ne]
    · rw [resultant_fg_deriv_left f g hg, resultant_fg_deriv_right f g hf hg,
          resultant_split_fg_left f g hf, resultant_split_fg_right f g hg,
          h_resultant_comm,
          show f.resultant (derivative f) =
              (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr from ?_,
          show g.resultant (derivative g) =
              (-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.leadingCoeff * g.discr from ?_]
      · ring
      · convert Polynomial.resultant_deriv _
        · exact natDegree_derivative_charZero hg
        · exact Polynomial.natDegree_pos_iff_degree_pos.mp hg
      · convert Polynomial.resultant_deriv _
        · exact natDegree_derivative_charZero hf
        · exact Polynomial.natDegree_pos_iff_degree_pos.mp hf
  have h_cancel : (-1) ^ ((f.natDegree + g.natDegree) * ((f.natDegree + g.natDegree) - 1) / 2) * (f * g).leadingCoeff =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff *
      ((-1) ^ (f.natDegree * g.natDegree)) *
      ((-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.leadingCoeff) := by
    rw [Polynomial.leadingCoeff_mul,
        show (f.natDegree + g.natDegree) * (f.natDegree + g.natDegree - 1) / 2 =
            f.natDegree * (f.natDegree - 1) / 2 + f.natDegree * g.natDegree +
              g.natDegree * (g.natDegree - 1) / 2
          from (sign_exponent_identity f.natDegree g.natDegree).symm]
    ring
  refine mul_left_cancel₀ (a := (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) *
    f.leadingCoeff * (-1) ^ (f.natDegree * g.natDegree) *
    ((-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.leadingCoeff)) ?_ ?_
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (natDegree_pos_leadingCoeff_ne_zero hf))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (natDegree_pos_leadingCoeff_ne_zero hg))
  · grind

end
