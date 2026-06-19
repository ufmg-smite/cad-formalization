import Mathlib

/-!
# Transfer of elimination-ideal membership to shifted reverses (pipeline form)

Algebraic core of the *pipeline form* of the generalized Brown theorem
(`thesis/brown_pipeline_direct.tex`, the "Witness transfer" Proposition 4.5).

Given `f ∈ R[X]` of degree `n ≥ 1` and `P ∈ R` with `C P ∈ ⟨f, f'⟩`, we produce
a power `M` and show

* `C (lc(f)^M · P) ∈ ⟨f*_γ, (f*_γ)'⟩`, where `f*_γ := reflect n (f(X + γ))`,

for every shift `γ ∈ R` (`witness_transfer_shifted`).  Two elementary,
cofactor-free steps:

1. **Reflection** (`reflect_span_transfer`, via the Euler-type identity
   `reflect_derivative_eq` — Lemma 4.2 of the notes): `P ∈ ⟨φ, φ'⟩` gives
   `X^M · C P ∈ ⟨rev φ, (rev φ)'⟩`.
2. **Clearing** (`clear_X_pow_factor`): working modulo `⟨ρ⟩`, the constant
   coefficient `c = ρ(0)` satisfies `X · divX ρ ≡ -c`, so `(X · divX ρ)^M ≡
   (-c)^M` and the spurious `X^M` can be cleared at the cost of a factor `c^M`.
   For `ρ = f*_γ` the constant coefficient is `lc f`.

Composed with the shift `taylor γ` (`taylor_span_transfer`).  This replaces the
bivariate homogenization / Möbius-saturation argument of the companion notes
(`thesis/brown_generalized.tex`, Lemma 5.1) entirely: only **one** elimination
ideal membership is needed, and no Bézout cofactors are constructed.

Everything is over an arbitrary commutative ring.
-/

noncomputable section

open Polynomial

namespace Brown

variable {R : Type*} [CommRing R]

/-! ### The Euler-type identity for `reflect` (Lemma 4.2) -/

/-- **Euler-type identity** relating reflection and differentiation:
`reflect N (φ') = (N+1) · reflect (N+1) φ - X · (reflect (N+1) φ)'`
for `deg φ ≤ N + 1`.  Both sides equal `∑ i·aᵢ·X^(N+1-i)` for `φ = ∑ aᵢ X^i`. -/
theorem reflect_derivative_eq (φ : R[X]) (N : ℕ) (hφ : φ.natDegree ≤ N + 1) :
    reflect N (derivative φ) =
      C ((N + 1 : ℕ) : R) * reflect (N + 1) φ - X * derivative (reflect (N + 1) φ) := by
  ext k
  rw [coeff_reflect, coeff_derivative, coeff_sub, coeff_C_mul, coeff_reflect]
  rcases k with _ | j
  · -- k = 0: the `X * _` term contributes nothing
    rw [revAt_zero, revAt_zero, mul_coeff_zero, coeff_X_zero, zero_mul, sub_zero]
    push_cast
    ring
  · -- k = j + 1
    rw [coeff_X_mul, coeff_derivative, coeff_reflect]
    rcases lt_trichotomy (j + 1) (N + 1) with hlt | heq | hgt
    · -- j + 1 ≤ N
      have hjN : j + 1 ≤ N := by omega
      rw [revAt_le hjN, revAt_le (by omega : j + 1 ≤ N + 1),
        show N - (j + 1) + 1 = N + 1 - (j + 1) from by omega,
        show N + 1 - (j + 1) = N - j from by omega]
      have hc : ((N - (j + 1) : ℕ) : R) = (N : R) - (j : R) - 1 := by
        rw [Nat.cast_sub hjN]; push_cast; ring
      rw [hc]
      push_cast
      ring
    · -- j + 1 = N + 1: both sides vanish
      have hz : φ.coeff (j + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [revAt_eq_self_of_lt (by omega : N < j + 1),
        revAt_le (by omega : j + 1 ≤ N + 1),
        show N + 1 - (j + 1) = 0 from by omega, hz, zero_mul, ← heq]
      push_cast
      ring
    · -- j + 1 > N + 1: both sides vanish
      have hz1 : φ.coeff (j + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      have hz2 : φ.coeff (j + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [revAt_eq_self_of_lt (by omega : N < j + 1),
        revAt_eq_self_of_lt (by omega : N + 1 < j + 1), hz1, hz2]
      ring

/-! ### Shift (`taylor`) commutes with differentiation -/

/-- The shift `taylor γ` commutes with `derivative` (the derivative of `X + C γ` is `1`). -/
theorem taylor_derivative (γ : R) (ψ : R[X]) :
    taylor γ (derivative ψ) = derivative (taylor γ ψ) := by
  rw [taylor_apply, taylor_apply, derivative_comp, derivative_X_add_C, one_mul]

/-! ### Transfer of span membership through shift and reflection -/

/-- Membership in `⟨φ, φ'⟩` transfers through the shift `taylor γ`. -/
theorem taylor_span_transfer (γ : R) (φ : R[X]) (P : R)
    (hP : C P ∈ Ideal.span ({φ, derivative φ} : Set R[X])) :
    C P ∈ Ideal.span ({taylor γ φ, derivative (taylor γ φ)} : Set R[X]) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
  refine Ideal.mem_span_pair.mpr ⟨taylor γ A, taylor γ B, ?_⟩
  rw [← taylor_derivative, ← taylor_mul, ← taylor_mul, ← map_add, hAB, taylor_C]

/-- Membership in `⟨φ, φ'⟩` transfers through `reflect (N+1)` at the cost of a
factor `X^M` (the "reflection" step, Lemma 4.3 of the notes). -/
theorem reflect_span_transfer (N : ℕ) (φ : R[X]) (hφ : φ.natDegree ≤ N + 1) (P : R)
    (hP : C P ∈ Ideal.span ({φ, derivative φ} : Set R[X])) :
    ∃ M : ℕ, X ^ M * C P ∈
      Ideal.span ({reflect (N + 1) φ, derivative (reflect (N + 1) φ)} : Set R[X]) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
  set M := max (A.natDegree + (N + 1)) (B.natDegree + N) with hM_def
  have hMN1 : N + 1 ≤ M := le_max_of_le_left (Nat.le_add_left _ _)
  have hA : A.natDegree ≤ M - (N + 1) := by
    have := le_max_left (A.natDegree + (N + 1)) (B.natDegree + N)
    omega
  have hB : B.natDegree ≤ M - N := by
    have := le_max_right (A.natDegree + (N + 1)) (B.natDegree + N)
    omega
  have haM : (M - (N + 1)) + (N + 1) = M := by omega
  have hbM : (M - N) + N = M := by omega
  have hφ' : (derivative φ).natDegree ≤ N := by
    have := natDegree_derivative_le φ
    omega
  have e1 : reflect M (A * φ) = reflect (M - (N + 1)) A * reflect (N + 1) φ := by
    conv_lhs => rw [← haM]
    exact reflect_mul A φ hA hφ
  have e2 : reflect M (B * derivative φ)
      = reflect (M - N) B * reflect N (derivative φ) := by
    conv_lhs => rw [← hbM]
    exact reflect_mul B (derivative φ) hB hφ'
  have key : C P * X ^ M
      = reflect (M - (N + 1)) A * reflect (N + 1) φ
        + reflect (M - N) B *
          (C ((N + 1 : ℕ) : R) * reflect (N + 1) φ - X * derivative (reflect (N + 1) φ)) := by
    rw [← reflect_derivative_eq φ N hφ, ← e1, ← e2, ← reflect_add, hAB, reflect_C]
  refine ⟨M, Ideal.mem_span_pair.mpr
    ⟨reflect (M - (N + 1)) A + C ((N + 1 : ℕ) : R) * reflect (M - N) B,
     -(X * reflect (M - N) B), ?_⟩⟩
  linear_combination key.symm

/-! ### Clearing a spurious power of `X` (the "clearing" step, Lemma 4.4) -/

/-- **Clearing lemma.**  If `X^M · C P` lies in `⟨ρ, ρ'⟩` and `c := ρ.coeff 0` is
the constant coefficient of `ρ`, then `C (c^M · P)` lies in `⟨ρ, ρ'⟩`.

Proof: in the quotient `R[X] ⧸ ⟨ρ, ρ'⟩`, the relation `ρ = X · divX ρ + C c`
becomes `X · divX ρ ≡ -C c`, so `(X · divX ρ)^M ≡ (-1)^M (C c)^M`.  The
hypothesis says `(image of X)^M · (image of C P) = 0`; multiplying by
`(image of divX ρ)^M` clears the `X^M`, leaving `(C c)^M · C P ≡ 0`.  No Bézout
cofactors (no binomial expansion of `(ρ - X·divX ρ)^M`) are needed. -/
theorem clear_X_pow_factor (ρ : R[X]) (P : R) (M : ℕ)
    (h : X ^ M * C P ∈ Ideal.span ({ρ, derivative ρ} : Set R[X])) :
    C (ρ.coeff 0 ^ M * P) ∈ Ideal.span ({ρ, derivative ρ} : Set R[X]) := by
  set I : Ideal R[X] := Ideal.span ({ρ, derivative ρ} : Set R[X]) with hI
  have hρI : ρ ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  have hρ0 : Ideal.Quotient.mk I ρ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hρI
  -- `image (C c) = - image X · image (divX ρ)`
  have hCc : Ideal.Quotient.mk I (C (ρ.coeff 0))
      = -(Ideal.Quotient.mk I X * Ideal.Quotient.mk I ρ.divX) := by
    have hh := congrArg (Ideal.Quotient.mk I) (X_mul_divX_add ρ)
    rw [map_add, map_mul, hρ0] at hh
    linear_combination hh
  -- the hypothesis, in the quotient
  have hX : Ideal.Quotient.mk I X ^ M * Ideal.Quotient.mk I (C P) = 0 := by
    have hh : Ideal.Quotient.mk I (X ^ M * C P) = 0 := h
    rwa [map_mul, map_pow] at hh
  -- `C (c^M · P) = (C c)^M · C P`
  have hCexp : C (ρ.coeff 0 ^ M * P) = C (ρ.coeff 0) ^ M * C P := by
    rw [map_mul, map_pow]
  -- in the quotient: `(C c)^M · C P = (-divX ρ)^M · (X^M · C P) = (-divX ρ)^M · 0 = 0`
  rw [hCexp, map_mul, map_pow, hCc,
    show -(Ideal.Quotient.mk I X * Ideal.Quotient.mk I ρ.divX)
        = -Ideal.Quotient.mk I ρ.divX * Ideal.Quotient.mk I X from by ring,
    mul_pow, mul_assoc, hX, mul_zero]

/-! ### The witness transfer (Proposition 4.5) -/

/-- **Witness transfer.**  From a single elimination-ideal membership
`C P ∈ ⟨f, f'⟩`, with `f` of positive degree `n`, we obtain a power `M` with
`C (lc(f)^M · P) ∈ ⟨f*_γ, (f*_γ)'⟩`, where `f*_γ = reflect n (taylor γ f)` is
the shifted reverse.  Shift (`taylor_span_transfer`), then reflect
(`reflect_span_transfer`, picking up `X^M`), then clear (`clear_X_pow_factor`,
trading `X^M` for `lc(f)^M`, since the constant coefficient of `f*_γ` is `lc f`). -/
theorem witness_transfer_shifted
    (f : R[X]) (hpos : 0 < f.natDegree) (γ : R) (P : R)
    (h₁ : C P ∈ Ideal.span ({f, derivative f} : Set R[X])) :
    ∃ M : ℕ, C (f.leadingCoeff ^ M * P) ∈ Ideal.span
      ({reflect f.natDegree (taylor γ f),
        derivative (reflect f.natDegree (taylor γ f))} : Set R[X]) := by
  obtain ⟨m, hm⟩ : ∃ m, f.natDegree = m + 1 := ⟨f.natDegree - 1, by omega⟩
  -- shift, then reflect, picking up a factor `X^M`
  have hshift : C P ∈ Ideal.span ({taylor γ f, derivative (taylor γ f)} : Set R[X]) :=
    taylor_span_transfer γ f P h₁
  obtain ⟨M, hM⟩ := reflect_span_transfer m (taylor γ f)
    (by rw [natDegree_taylor]; omega) P hshift
  -- the constant coefficient of `reflect (m+1) (taylor γ f)` is `lc f`
  have hc0 : (reflect (m + 1) (taylor γ f)).coeff 0 = f.leadingCoeff := by
    rw [coeff_reflect, revAt_zero]
    have hnd : (taylor γ f).natDegree = m + 1 := by rw [natDegree_taylor]; omega
    rw [← hnd, coeff_natDegree, leadingCoeff_taylor]
  -- clear the `X^M`, trading it for `lc(f)^M`
  have hclear := clear_X_pow_factor (reflect (m + 1) (taylor γ f)) P M hM
  rw [hc0] at hclear
  refine ⟨M, ?_⟩
  rw [hm]
  exact hclear

/-! ### Trailing degree of a reflection

Bookkeeping for step (2) of the main proof: the multiplicity of `0` as a root of
the reverse records the degree drop. -/

/-- For `ψ ≠ 0` with `deg ψ ≤ N`, the trailing degree of `reflect N ψ` is
`N - deg ψ`. -/
theorem natTrailingDegree_reflect {ψ : R[X]} {N : ℕ} (hψ : ψ ≠ 0)
    (hdeg : ψ.natDegree ≤ N) :
    (reflect N ψ).natTrailingDegree = N - ψ.natDegree := by
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_reflect, revAt_le (by omega : N - ψ.natDegree ≤ N),
      Nat.sub_sub_self hdeg]
    exact leadingCoeff_ne_zero.mpr hψ
  · apply le_natTrailingDegree (by rwa [Ne, reflect_eq_zero_iff])
    intro m hm
    rw [coeff_reflect]
    apply coeff_eq_zero_of_natDegree_lt
    rw [revAt_le (by omega : m ≤ N)]
    omega

end Brown
