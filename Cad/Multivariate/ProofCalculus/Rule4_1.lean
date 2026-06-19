import Cad.Multivariate.ProofCalculus.Basic

namespace ProofCalculus

theorem nalbach_4_1
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (f : PolyR i)
    (hf_sf : Squarefree f)
    (hf_i : f.natDegree > 1) :
    an_sub i R →
    connected i R →
    non_null i R f →
    ord_inv i R f.discr →
    ord_inv i R f.leadingCoeff →
    an_del i R f := by

  intros h_sub h_conn h_non_null h_ord_inv h_ord_lc_inv
  have hp_i0 : f.natDegree > 0 := by omega
  have discr_ne_zero : f.discr ≠ 0 := by apply discr_ne_zero_of_squarefree f hf_sf hp_i0
  have deg_inv := brown_original i f hp_i0 discr_ne_zero R h_sub h_conn h_ord_inv h_ord_lc_inv h_non_null
  have hunit : IsUnit (f.natDegree : MvPolynomial (Fin i) ℝ) := by
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial (Fin i) ℝ) f.natDegree]
    exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  have discr_in_elim := Brown.discr_mem_span f hf_i hunit
  have := lifting_theorem_generalized R f h_sub h_conn deg_inv h_non_null f.discr discr_ne_zero discr_in_elim h_ord_inv
  exact this

#print axioms nalbach_4_1

theorem nalbach_4_1_generalized
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (f : PolyR i)
    (P : MvPolynomial (Fin i) ℝ)
    (hP : P ≠ 0)
    (hP_mem₁ : Polynomial.C P ∈ Ideal.span ({ f, f.derivative } : Set (PolyR i)))
    (hf_deg : f.natDegree > 0) :
    an_sub i R →
    connected i R →
    non_null i R f →
    ord_inv i R P →
    ord_inv i R f.leadingCoeff →
    an_del i R f := by

  intros h_sub h_conn h_non_null h_ord_inv h_ord_lc_inv
  have h_deg_inv :=
    brown_generalized i f P hP hP_mem₁ hf_deg R h_sub h_conn h_ord_inv h_ord_lc_inv h_non_null
  have := lifting_theorem_generalized R f h_sub h_conn h_deg_inv h_non_null P hP hP_mem₁ h_ord_inv
  exact this

#print axioms nalbach_4_1_generalized

end ProofCalculus
