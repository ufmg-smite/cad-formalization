import Cad.Multivariate.ProofCalculus.Basic

namespace ProofCalculus

theorem nalbach_4_2_part1_generalized
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (s : Fin i → ℝ)
    (p : PolyR i)
    (D : MvPolynomial (Fin i) ℝ)
    (h_D_mem : Polynomial.C D ∈ Ideal.span ({p, p.derivative} : Set (PolyR i))) :
    sample i s R →
    D.eval s ≠ 0 →
    sgn_inv i R D →
    non_null i R p := by
  intros h1 h2 h3
  rw [Ideal.mem_span_pair] at h_D_mem
  obtain ⟨A, B, h⟩ := h_D_mem
  unfold non_null
  intros a ha abs
  have h : specialize (A * p + B * Polynomial.derivative p) a = specialize (Polynomial.C D) a :=
    Polynomial.coeff_inj.mp (congrArg Polynomial.coeff (congrFun (congrArg specialize h) a))
  have : specialize (A * p + B * p.derivative) a =
         specialize A a * specialize p a + specialize B a * specialize p.derivative a := by
    unfold specialize
    norm_num
  rw [this, abs] at h
  have : specialize p.derivative a = (specialize p a).derivative := by
    unfold specialize
    exact Eq.symm (Polynomial.derivative_map p (evalBase a))
  rw [abs] at this
  simp only [Polynomial.derivative_zero] at this
  rw [this] at h
  simp at h
  have sgn_0 : sgn (MvPolynomial.eval a D) = 0 := by
    unfold sgn
    unfold specialize evalBase at h
    simp at h
    have : MvPolynomial.eval a D = 0 := Polynomial.C_eq_zero.mp (id (Eq.symm h))
    rw [this]
    simp only [lt_self_iff_false, ↓reduceIte]
  have := h3 s h1 a ha
  rw [sgn_0] at this
  have : MvPolynomial.eval s D = 0 := eq_zero_of_sgn_eq_zero this
  exact False.elim (h2 this)

theorem nalbach_4_2_part1
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (s : Fin i → ℝ)
    (p : PolyR i) :
    sample i s R →
    p.natDegree > 1 →
    p.discr.eval s ≠ 0 →
    sgn_inv i R p.discr →
    non_null i R p := by
  intros h1 h2 h3 h4

  have hunit : IsUnit (p.natDegree : MvPolynomial (Fin i) ℝ) := by
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial (Fin i) ℝ) p.natDegree]
    exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  have : Polynomial.C p.discr ∈ Ideal.span ({p, p.derivative} : Set (PolyR i)) := Brown.discr_mem_span p h2 hunit

  exact nalbach_4_2_part1_generalized i R s p p.discr this h1 h3 h4

theorem nalbach_4_2_part2
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (s : Fin i → ℝ)
    (p : PolyR i) :
    sample i s R →
    (∃ j : Nat, ((p.coeff j).eval s ≠ 0 ∧ sgn_inv i R (p.coeff j))) →
    non_null i R p := by
  intros h1 h2
  obtain ⟨j, hj1, hj2⟩ := h2
  unfold non_null
  intros a ha hpa
  have := (specialize_eq_zero_iff p a).mp hpa j
  have : sgn (MvPolynomial.eval a (Polynomial.coeff p j)) = 0 := sgn_eq_zero_of_eq_zero this
  have : sgn (MvPolynomial.eval s (Polynomial.coeff p j)) ≠ 0 := by
    intro h
    have := eq_zero_of_sgn_eq_zero h
    exact Ne.elim hj1 this
  have := hj2 a ha s h1
  simp_all only [ne_eq, not_true_eq_false]

end ProofCalculus
