import Cad.Multivariate.ProofCalculus.Defs

namespace ProofCalculus

private lemma sgn_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  unfold sgn; rw [if_pos h]

private lemma sgn_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := by
  unfold sgn; rw [if_neg (not_lt.mpr h.le), if_neg h.ne']

private lemma sgn_zero {x : ℝ} (h : x = 0) : sgn x = 0 := by
  subst h; unfold sgn; simp

/-- The sign function is multiplicative. -/
private lemma sgn_mul (x y : ℝ) : sgn (x * y) = sgn x * sgn y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [sgn_pos (mul_pos_of_neg_of_neg hx hy), sgn_neg hx, sgn_neg hy]; ring
    · rw [sgn_zero (show x * y = 0 by rw [hy, mul_zero]), sgn_zero hy]; ring
    · rw [sgn_neg (mul_neg_of_neg_of_pos hx hy), sgn_neg hx, sgn_pos hy]; ring
  · rw [sgn_zero hx, sgn_zero (show x * y = 0 by rw [hx, zero_mul])]; ring
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [sgn_neg (mul_neg_of_pos_of_neg hx hy), sgn_pos hx, sgn_neg hy]; ring
    · rw [sgn_zero (show x * y = 0 by rw [hy, mul_zero]), sgn_zero hy]; ring
    · rw [sgn_pos (mul_pos hx hy), sgn_pos hx, sgn_pos hy]; ring

theorem nalbach_4_4_part1
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (p : MvPolynomial (Fin i) ℝ)
    (Q : List (MvPolynomial (Fin i) ℝ))
    (hQ : Q.prod = p) :
    (∀ q ∈ Q, ord_inv i R q) → ord_inv i R p := by
  subst hQ
  induction Q with
  | nil =>
    intro _ a _ b _
    simp only [List.prod_nil]
    rw [(polyOrder_zero_iff i 1 a).mpr (by simp), (polyOrder_zero_iff i 1 b).mpr (by simp)]
  | cons q qs ih =>
    intro hQinv a ha b hb
    rw [List.prod_cons]
    -- vanishing order is additive over products
    rw [polyOrder_mul_add, polyOrder_mul_add,
        hQinv q (List.mem_cons.mpr (Or.inl rfl)) a ha b hb,
        ih (fun r hr => hQinv r (List.mem_cons.mpr (Or.inr hr))) a ha b hb]

theorem nalbach_4_4_part2
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (p : MvPolynomial (Fin i) ℝ)
    (Q : List (MvPolynomial (Fin i) ℝ))
    (hQ : Q.prod = p) :
    (∀ q ∈ Q, sgn_inv i R q) → sgn_inv i R p := by
  subst hQ
  induction Q with
  | nil =>
    intro _ a _ b _
    simp only [List.prod_nil, map_one]
  | cons q qs ih =>
    intro hQinv a ha b hb
    rw [List.prod_cons]
    -- the sign of a product is the product of the signs
    simp only [map_mul, sgn_mul]
    rw [hQinv q (List.mem_cons.mpr (Or.inl rfl)) a ha b hb,
        ih (fun r hr => hQinv r (List.mem_cons.mpr (Or.inr hr))) a ha b hb]

end ProofCalculus
