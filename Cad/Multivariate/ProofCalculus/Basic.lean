import Cad.Multivariate.ProofCalculus.Defs

namespace ProofCalculus

lemma eq_zero_of_sgn_eq_zero {r : ℝ} (h : sgn r = 0) : r = 0 := by
  unfold sgn at h
  split_ifs at h with hlt heq
  · exact heq
  · norm_num at h

lemma sgn_eq_zero_of_eq_zero {r : ℝ} (h : r = 0) : sgn r = 0 := by
  unfold sgn
  split_ifs
  · linarith
  · rfl

lemma specialize_eq_zero_iff {n : ℕ} (f : PolyR n) (a : Fin n → ℝ) :
    specialize f a = 0 ↔ ∀ k, (f.coeff k).eval a = 0 := by
  unfold specialize
  rw [Polynomial.ext_iff]
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, evalBase]

lemma sgn_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  unfold sgn; rw [if_pos h]

lemma sgn_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := by
  unfold sgn; rw [if_neg (not_lt.mpr h.le), if_neg h.ne']

/-- The sign function is multiplicative. -/
lemma sgn_mul (x y : ℝ) : sgn (x * y) = sgn x * sgn y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [sgn_pos (mul_pos_of_neg_of_neg hx hy), sgn_neg hx, sgn_neg hy]; ring
    · rw [sgn_eq_zero_of_eq_zero (show x * y = 0 by rw [hy, mul_zero]), sgn_eq_zero_of_eq_zero hy]; ring
    · rw [sgn_neg (mul_neg_of_neg_of_pos hx hy), sgn_neg hx, sgn_pos hy]; ring
  · rw [sgn_eq_zero_of_eq_zero hx, sgn_eq_zero_of_eq_zero (show x * y = 0 by rw [hx, zero_mul])]; ring
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [sgn_neg (mul_neg_of_pos_of_neg hx hy), sgn_pos hx, sgn_neg hy]; ring
    · rw [sgn_eq_zero_of_eq_zero (show x * y = 0 by rw [hy, mul_zero]), sgn_eq_zero_of_eq_zero hy]; ring
    · rw [sgn_pos (mul_pos hx hy), sgn_pos hx, sgn_pos hy]; ring

end ProofCalculus
