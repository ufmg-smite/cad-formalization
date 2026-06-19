import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassCount
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Layer C, piece 4: Newton's identities and the Weierstrass coefficients

The slice `G(z,·)` has `m` zeros (with multiplicity) inside `|t| < R`, forming a multiset
`M(z)` of cardinality `m` (`zero_count_eventually`). The Weierstrass polynomial is the monic
polynomial with exactly those roots, `W(z,·) = ∏_{r ∈ M(z)} (X - r)`, whose coefficients are
(signed) **elementary symmetric functions** `eₖ(z) = (M z).esymm k` of the roots.

The roots themselves are *not* analytic in `z` (they may permute), but the symmetric functions are.
The classical reason is **Newton's identities**: `k·eₖ = ∑ ± e_{k-i}·pᵢ`, where the power sums
`pᵢ(z) = ∑_r rⁱ` *are* analytic (they are the contour integrals `powerSum_analyticAt`). Solving the
recursion for `eₖ` (dividing by `k`, valid in characteristic `0`) expresses each `eₖ` through the
analytic power sums and lower `e`'s, so by strong induction every `eₖ` is analytic.

This file builds that machinery:
* `multiset_newton` — Newton's identity for an arbitrary finite multiset of complex numbers, obtained
  from Mathlib's `MvPolynomial.mul_esymm_eq_sum` by evaluating at an enumeration of the multiset;
* (to come) analyticity of `z ↦ (M z).esymm k` and the resulting Weierstrass coefficients.
-/

noncomputable section

open Complex Metric Filter Finset MvPolynomial
open scoped Real Topology BigOperators

variable {s e : ℕ}

/-- Any multiset of cardinality `m` can be enumerated by a tuple `Fin m → ℂ`. -/
private lemma exists_enum (M : Multiset ℂ) {m : ℕ} (hcard : M.card = m) :
    ∃ r : Fin m → ℂ, Multiset.map r Finset.univ.val = M := by
  induction M using Quotient.inductionOn with
  | _ L =>
    simp only [Multiset.quot_mk_to_coe, Multiset.coe_card] at hcard ⊢
    subst hcard
    refine ⟨L.get, ?_⟩
    rw [show (Finset.univ.val : Multiset (Fin L.length)) = ↑(List.finRange L.length) from rfl,
      Multiset.map_coe, List.map_get_finRange]

/-- **Newton's identity for a tuple of complex numbers** (image of Mathlib's `mul_esymm_eq_sum`
under `aeval`). -/
private lemma tuple_newton (m k : ℕ) (r : Fin m → ℂ) :
    (k : ℂ) * (aeval r) (MvPolynomial.esymm (Fin m) ℂ k)
      = (-1) ^ (k + 1) * ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
          (-1) ^ a.1 * (aeval r) (MvPolynomial.esymm (Fin m) ℂ a.1) * (∑ i, (r i) ^ a.2) := by
  have h := mul_esymm_eq_sum (Fin m) ℂ k
  have h2 := congrArg (aeval r) h
  simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one] at h2
  rw [h2]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  refine congrArg _ ?_
  rw [MvPolynomial.psum]; simp [map_sum]

/-- **Newton's identity for a finite multiset of complex numbers.** For every `k`,
`k · esymm M k = (-1)^{k+1} ∑_{i+j=k, i<k} (-1)^i · esymm M i · pⱼ(M)`, where `pⱼ(M)` is the
`j`-th power sum `(M.map (·^j)).sum`. The only place that uses `ℂ` is the ambient ring; the identity
is purely formal once the multiset is enumerated. -/
theorem multiset_newton (M : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * M.esymm k
      = (-1) ^ (k + 1) * ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
          (-1) ^ a.1 * M.esymm a.1 * (M.map (· ^ a.2)).sum := by
  obtain ⟨n, hn⟩ : ∃ n, M.card = n := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := exists_enum M hn
  have hesymm : ∀ j, (aeval r) (MvPolynomial.esymm (Fin n) ℂ j) = M.esymm j := by
    intro j; rw [aeval_esymm_eq_multiset_esymm, hr]
  have hpsum : ∀ j, (∑ i, (r i) ^ j) = (M.map (· ^ j)).sum := by
    intro j
    rw [← hr, Multiset.map_map]
    rfl
  rw [← hesymm k, tuple_newton n k r]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [hesymm a.1, hpsum a.2]

/-- **Elementary symmetric functions of an analytic root family are analytic.** If every power sum
`z ↦ (M z).map (·^j) |>.sum` is analytic at `x₀`, then so is every `z ↦ (M z).esymm k` — the content
of Newton's identities is that `esymm` is a polynomial (over `ℚ`) in the power sums. -/
theorem esymm_analyticAt_of_powerSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : E → Multiset ℂ} {x₀ : E}
    (hpow : ∀ j, AnalyticAt ℂ (fun z => ((M z).map (· ^ j)).sum) x₀) (k : ℕ) :
    AnalyticAt ℂ (fun z => (M z).esymm k) x₀ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · have heq : (fun z => (M z).esymm k) = fun _ => (1 : ℂ) := by
        funext z; rw [hk]; simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [heq]; exact analyticAt_const
    · have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      have heq : (fun z => (M z).esymm k)
          = fun z => (k : ℂ)⁻¹ * ((-1) ^ (k + 1) *
              ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
                (-1) ^ a.1 * (M z).esymm a.1 * ((M z).map (· ^ a.2)).sum) := by
        funext z
        rw [← multiset_newton (M z) k, ← mul_assoc, inv_mul_cancel₀ hkne, one_mul]
      rw [heq]
      refine analyticAt_const.mul (analyticAt_const.mul (analyticAt_fun_sum _ fun a ha => ?_))
      rw [Finset.mem_filter] at ha
      exact (analyticAt_const.mul (ih a.1 ha.2)).mul (hpow a.2)

/-- Power sum of a multiset built as `∑ a, n a • {a}`. -/
private lemma sum_nsmul_singleton_powerSum (T : Finset ℂ) (n : ℂ → ℕ) (j : ℕ) :
    ((∑ a ∈ T, n a • ({a} : Multiset ℂ)).map (· ^ j)).sum = ∑ a ∈ T, ((n a : ℂ) * a ^ j) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih]
    simp [Multiset.map_nsmul, Multiset.sum_nsmul, mul_comm]

/-- Cardinality of a multiset built as `∑ a, n a • {a}`. -/
private lemma sum_nsmul_singleton_card (T : Finset ℂ) (n : ℂ → ℕ) :
    (∑ a ∈ T, n a • ({a} : Multiset ℂ)).card = ∑ a ∈ T, n a := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.card_add, ih]; simp

/-- `esymm k` of an all-zero multiset vanishes for `k ≥ 1`. -/
private lemma esymm_nsmul_zero {m k : ℕ} (hk : 0 < k) : (m • ({0} : Multiset ℂ)).esymm k = 0 := by
  rw [Multiset.esymm]
  refine Multiset.sum_eq_zero fun x hx => ?_
  rw [Multiset.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [Multiset.mem_powersetCard] at ht
  refine Multiset.prod_eq_zero ?_
  have hne : t ≠ 0 := by rw [← Multiset.card_pos]; omega
  obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
  have hy0 : y = 0 := (by simpa using Multiset.mem_of_le ht.1 hy : ¬m = 0 ∧ y = 0).2
  rwa [hy0] at hy

/-- The **multiset of zeros** of the slice `G(z,·)` inside `closedBall 0 R₁`: each divisor-support
point `a` taken with multiplicity `(divisor … a).toNat`. The Weierstrass polynomial is the monic
polynomial with exactly these roots. -/
def rootMultiset (G : CParam s e × ℂ → ℂ) (R₁ : ℝ) (z : CParam s e) : Multiset ℂ :=
  ∑ a ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset,
    (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall 0 R₁) a).toNat • ({a} : Multiset ℂ)

open Polynomial in
/-- Coefficient of the Weierstrass polynomial. -/
private lemma weierstrassPoly_coeff (m : ℕ) (a : Fin m → (CParam s e → ℂ)) (w : CParam s e)
    (j : ℕ) :
    (weierstrassPoly m a w).coeff j
      = (if j = m then 1 else 0) + ∑ i : Fin m, a i w * (if j = (i : ℕ) then 1 else 0) := by
  rw [weierstrassPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- **The Weierstrass coefficients (Layer C, piece 4).** From `G` analytic at `0` and `t`-regular of
order `m > 0`, there is an analytic family of coefficients `a` with `a i 0 = 0` such that, for `z`
near `0`, the monic polynomial `weierstrassPoly m a z` is precisely the polynomial whose roots are the
zeros of `G(z,·)` inside the disc (with multiplicity): `W(z,·) = ∏_{r ∈ rootMultiset z} (X - r)`.
The coefficients are the elementary symmetric functions of the roots, analytic by Newton's identities
(`esymm_analyticAt_of_powerSum`), and they vanish at `0` because there all roots are `0`. -/
theorem weierstrass_coeffs_exist (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hm_pos : 0 < m) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ (a : Fin m → (CParam s e → ℂ)) (R R₁ : ℝ), 0 < R ∧ R < R₁ ∧
      (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      (∀ ζ ∈ sphere (0 : ℂ) R, AnalyticAt ℂ G (0, ζ)) ∧
      (∀ ζ ∈ sphere (0 : ℂ) R, G (0, ζ) ≠ 0) ∧
      ∀ᶠ z in 𝓝 (0 : CParam s e),
        AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall 0 R₁) ∧
        (∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0) ∧
        (∀ a' ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support,
          a' ∈ ball (0 : ℂ) R) ∧
        weierstrassPoly m a z
          = ((rootMultiset G R₁ z).map (fun r => Polynomial.X - Polynomial.C r)).prod := by
  classical
  obtain ⟨R, R₁, hR, hRR₁, hGan_sph, hG0_sph, hiso0, hev⟩ :=
    zero_count_eventually G hG m hm_pos hreg
  -- power sums of the root multiset are analytic (they are the contour integrals)
  have hpow : ∀ j, AnalyticAt ℂ (fun z => ((rootMultiset G R₁ z).map (· ^ j)).sum) 0 := by
    intro j
    have hI : AnalyticAt ℂ (fun z : CParam s e => (2 * π * I)⁻¹ *
        ∮ ζ in C(0, R), ζ ^ j * fderiv ℂ G (z, ζ) (0, 1) / G (z, ζ)) 0 :=
      powerSum_analyticAt G hR j hGan_sph hG0_sph
    refine hI.congr ?_
    filter_upwards [hev] with z hz
    obtain ⟨hAn, hDiff, hNe, hSupp, _⟩ := hz
    rw [slice_powerSum_eq_rootSum hR hRR₁ hAn hDiff hNe hSupp j, rootMultiset,
      sum_nsmul_singleton_powerSum]
  -- hence the elementary symmetric functions are analytic
  have hE : ∀ k, AnalyticAt ℂ (fun z => (rootMultiset G R₁ z).esymm k) 0 :=
    esymm_analyticAt_of_powerSum hpow
  -- the root multiset at `0` is `m • {0}`
  have hroot0 : rootMultiset G R₁ 0 = m • ({0} : Multiset ℂ) := by
    obtain ⟨hAn0, _, _, _, _⟩ := hev.self_of_nhds
    have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R₁ := by
      rw [mem_closedBall, dist_self]; linarith
    have hdiv0 : (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁)) 0 = (m : ℤ) :=
      divisor_eq_of_analyticOrder h0mem hAn0 hreg
    have hsupp_eq : (divisor_support_finite (R₁ := R₁) (fun t => G (0, t))).toFinset = {0} := by
      ext b
      rw [Set.Finite.mem_toFinset, Finset.mem_singleton, Function.mem_support]
      constructor
      · intro hb
        by_contra hbne
        have hbmem : b ∈ closedBall (0 : ℂ) R₁ :=
          (MeromorphicOn.divisor (fun t => G (0, t)) (closedBall (0 : ℂ) R₁)).supportWithinDomain hb
        exact hb (divisor_eq_zero_of_ne hAn0 hbmem (hiso0 b hbmem hbne))
      · intro hb; rw [hb, hdiv0]; exact_mod_cast hm_pos.ne'
    rw [rootMultiset, hsupp_eq, Finset.sum_singleton, hdiv0, Int.toNat_natCast]
  -- define the coefficients as signed elementary symmetric functions
  refine ⟨fun i z => (-1) ^ (m - (i : ℕ)) * (rootMultiset G R₁ z).esymm (m - (i : ℕ)), R, R₁,
    hR, hRR₁, fun i => analyticAt_const.mul (hE _), fun i => ?_, hGan_sph, hG0_sph, ?_⟩
  · -- a i 0 = 0  (esymm of an all-zero multiset, since `m - i ≥ 1`)
    show (-1) ^ (m - (i : ℕ)) * (rootMultiset G R₁ 0).esymm (m - (i : ℕ)) = 0
    rw [hroot0, esymm_nsmul_zero (by omega : 0 < m - (i : ℕ)), mul_zero]
  · -- the polynomial identity: W = ∏ (X - root)
    filter_upwards [hev] with z hz
    obtain ⟨hAn, hDiff, hNe, hSupp, hcount⟩ := hz
    refine ⟨hAn, hNe, hSupp, ?_⟩
    set M := rootMultiset G R₁ z with hM
    have hcard : M.card = m := by
      rw [hM, rootMultiset, sum_nsmul_singleton_card]; exact hcount
    refine Polynomial.ext fun j => ?_
    rw [weierstrassPoly_coeff]
    rcases lt_trichotomy j m with hj | hj | hj
    · -- j < m
      rw [if_neg (by omega : j ≠ m), zero_add,
        Finset.sum_eq_single (⟨j, hj⟩ : Fin m)
          (fun i _ hi => by rw [if_neg (fun h => hi (Fin.ext h.symm)), mul_zero])
          (fun h => absurd (Finset.mem_univ _) h),
        if_pos rfl, mul_one,
        Multiset.prod_X_sub_C_coeff M (by rw [hcard]; omega), hcard]
    · -- j = m
      rw [if_pos hj, Finset.sum_eq_zero (fun i _ => by
        rw [if_neg (by omega : j ≠ (i : ℕ)), mul_zero]), add_zero,
        Multiset.prod_X_sub_C_coeff M (by rw [hcard]; omega), hcard, hj, Nat.sub_self, pow_zero,
        Multiset.esymm, Multiset.powersetCard_zero_left]
      simp
    · -- j > m
      rw [if_neg (by omega : j ≠ m), zero_add,
        Finset.sum_eq_zero (fun i _ => by rw [if_neg (by omega : j ≠ (i : ℕ)), mul_zero]),
        Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]; exact hj

end
