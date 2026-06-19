import Cad.Multivariate.ProofCalculus.Defs

private lemma eq_zero_of_sgn_eq_zero {r : ℝ} (h : sgn r = 0) : r = 0 := by
  unfold sgn at h
  split_ifs at h with hlt heq
  · exact heq
  · norm_num at h

private lemma sgn_eq_zero_of_eq_zero {r : ℝ} (h : r = 0) : sgn r = 0 := by
  unfold sgn
  split_ifs
  · linarith
  · rfl

theorem nalbach_4_5
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (s : Fin i → ℝ)
    (p : MvPolynomial (Fin i) ℝ)
    (Q : List (MvPolynomial (Fin i) ℝ))
    (hQ : Q.prod = p)
    (j : Fin Q.length) :
    sample i s R → (Q.get j).eval s = 0 → sgn_inv i R (Q.get j) → sgn_inv i R p
    := by
  intros h1 h2 h3
  have key : ∀ r : Fin i → ℝ, ∀ i : Fin Q.length, (Q.get i).eval r = 0 → p.eval r = 0 := by
    intros r i H
    subst hQ
    rw [map_list_prod (MvPolynomial.eval r) Q]
    simp_all only [List.get_eq_getElem, List.prod_eq_zero_iff, List.mem_map]
    apply Exists.intro
    apply And.intro
    on_goal 2 => { exact H }
    simp_all only [List.getElem_mem]
  intros a ha b hb
  -- `Q.get j` is sign-invariant on `R` and vanishes at `s ∈ R`, so it vanishes on all of `R`.
  have hja : (Q.get j).eval a = 0 := by
    apply eq_zero_of_sgn_eq_zero
    rw [h3 a ha s h1, h2]
    exact sgn_eq_zero_of_eq_zero rfl
  have hjb : (Q.get j).eval b = 0 := by
    apply eq_zero_of_sgn_eq_zero
    rw [h3 b hb s h1, h2]
    exact sgn_eq_zero_of_eq_zero rfl
  -- hence `p = Q.prod` vanishes at every point of `R`, so its sign is constantly `0`.
  rw [key a j hja, key b j hjb]
