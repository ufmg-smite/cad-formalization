import Cad.Multivariate.ProofCalculus.Basic

namespace ProofCalculus

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
