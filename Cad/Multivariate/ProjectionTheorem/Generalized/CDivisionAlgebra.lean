import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum

/-!
# Brick: the polynomial difference-quotient (division-by-`W` remainder structure)

For a polynomial `W`, `W(ζ) − W(t) = (ζ − t)·Q(ζ, t)` with an explicit `Q` that is, in the `t`
variable, a polynomial of degree `< deg W` whose coefficients are polynomials in `ζ`. This is the
algebraic heart of the "division by a Weierstrass polynomial" step of the Cauchy-integral proof of
`weierstrass_division`: it makes the remainder
`r(z,t) = (2πi)⁻¹ ∮ (F/G)·(W(ζ)−W(t))/(ζ−t) dζ` a degree-`<m` polynomial in `t` (integrate the finite
`Q`-sum term by term). Pure algebra — no analysis.
-/

noncomputable section

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **Difference-quotient factorization.** `W(ζ) − W(t) = (ζ − t)·∑_j W_j·∑_{i<j} ζ^i t^{j-1-i}`.
The inner double sum is `Q(ζ,t)`; in the `t`-variable every monomial `t^{j-1-i}` has degree
`≤ deg W − 1`. -/
theorem eval_sub_eval_eq_mul (W : Polynomial R) (ζ t : R) :
    W.eval ζ - W.eval t
      = (ζ - t) * ∑ j ∈ range (W.natDegree + 1),
          W.coeff j * ∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc W.coeff j * ζ ^ j - W.coeff j * t ^ j
      = W.coeff j * (ζ ^ j - t ^ j) := by ring
    _ = W.coeff j * ((∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i)) * (ζ - t)) := by
          rw [geom_sum₂_mul]
    _ = (ζ - t) * (W.coeff j * ∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i)) := by ring


/-- **Difference quotient as an explicit degree-`<m` polynomial in `t`** (the reindexing brick).
Collecting the double sum `∑_j W_j ∑_{i<j} ζ^i t^{j-1-i}` by the power `k` of `t` gives a genuine
`∑_{k < n} c_k(ζ)·t^k` with `n = natDegree W` and coefficients `c_k(ζ) = ∑_{k < j ≤ n} W_j·ζ^{j-1-k}`.
This is the form that makes the Cauchy remainder `r(z,t) = (2πi)⁻¹∮ (F/W)·Q dζ` visibly a degree-`<m`
polynomial in `t` with contour-integral coefficients `ρ_k(z) = (2πi)⁻¹∮ (F/W)·c_k dζ`. Pure algebra. -/
theorem diffQuotient_eq_poly (W : Polynomial R) (ζ t : R) :
    ∑ j ∈ range (W.natDegree + 1), W.coeff j * ∑ i ∈ range j, ζ ^ i * t ^ (j - 1 - i)
      = ∑ k ∈ range W.natDegree,
          (∑ j ∈ Finset.Ico (k + 1) (W.natDegree + 1), W.coeff j * ζ ^ (j - 1 - k)) * t ^ k := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij' (fun (x : Σ _ : ℕ, ℕ) _ => (⟨x.1 - 1 - x.2, x.1⟩ : Σ _ : ℕ, ℕ))
    (fun (y : Σ _ : ℕ, ℕ) _ => (⟨y.2, y.2 - 1 - y.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨j, i⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at h ⊢
    omega
  · rintro ⟨k, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at h ⊢
    omega
  · rintro ⟨j, i⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range] at h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    omega
  · rintro ⟨k, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true]
    omega
  · rintro ⟨j, i⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range] at h
    have hexp : j - 1 - (j - 1 - i) = i := by omega
    rw [hexp]; ring
