import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# C4.3 engine — partial products of holomorphic root sections (foundational brick)

The connectedness kernel (irreducible Weierstrass ⟹ root variety path-connected over the punctured
locus) is proved by contraposition: a clopen splitting of the root cover yields a **partial product**
`h_A(z, z_n) = ∏_{i ∈ A} (z_n - φ_i(z))` over the sheets in one component, and the assertion is that
its coefficients (the elementary symmetric functions of the `A`-sheets) are holomorphic. Globally this
needs single-valuedness (monodromy-invariance of `A`) plus a removable-singularity extension across the
discriminant locus; *locally*, where the sheets are holomorphic sections `φ_i`, the coefficients are
visibly analytic. This file provides that local analytic core:

* `analyticAt_coeff_prod` — the coefficients of a finite product of analytic polynomial families are
  analytic (the base-point/normed-space-general version of `analyticCoeffs_prodFamily`);
* `analyticAt_coeff_prod_X_sub_C` — specialisation to `∏ (X - C (φ i ·))`: when the root sections
  `φ i` are analytic at `z₀`, every coefficient of the partial product is analytic at `z₀`.
-/

noncomputable section

open Polynomial

/-- **Coefficients of a finite product of analytic polynomial families are analytic.** The
base-point-general, arbitrary-normed-space version of `analyticCoeffs_prodFamily`: if each family
`fac l` has analytic coefficients at `z₀`, so does the product `∏ l ∈ t, fac l`. -/
theorem analyticAt_coeff_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (t : Finset ι) (fac : ι → E → Polynomial ℂ) {z₀ : E}
    (hc : ∀ l i, AnalyticAt ℂ (fun z => (fac l z).coeff i) z₀) :
    ∀ j, AnalyticAt ℂ (fun z => (∏ l ∈ t, fac l z).coeff j) z₀ := by
  classical
  induction t using Finset.induction with
  | empty => intro j; simpa only [Finset.prod_empty] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : Polynomial ℂ).coeff j) z₀)
  | insert a t ha IH =>
      intro j
      have hrw : (fun z => (∏ l ∈ insert a t, fac l z).coeff j)
          = fun z => ∑ x ∈ Finset.antidiagonal j,
              (fac a z).coeff x.1 * (∏ l ∈ t, fac l z).coeff x.2 := by
        funext z; rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      rw [hrw]
      exact Finset.analyticAt_fun_sum _ fun x _ => (hc a x.1).mul (IH x.2)

/-- **The partial product `∏ (X - C (φ l ·))` has analytic coefficients.** When the root sections
`φ l : E → ℂ` are analytic at `z₀`, every coefficient of `∏ l ∈ t, (X - C (φ l z))` is analytic at
`z₀`. This is the local analytic core of the partial-product factor in the connectedness proof: the
elementary symmetric functions of a finite set of holomorphic root sections are holomorphic. -/
theorem analyticAt_coeff_prod_X_sub_C {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (t : Finset ι) (φ : ι → E → ℂ) {z₀ : E}
    (hφ : ∀ l, AnalyticAt ℂ (φ l) z₀) (j : ℕ) :
    AnalyticAt ℂ (fun z => (∏ l ∈ t, (X - C (φ l z))).coeff j) z₀ := by
  refine analyticAt_coeff_prod t (fun l z => X - C (φ l z)) ?_ j
  intro l i
  have key : (fun z => ((X : Polynomial ℂ) - C (φ l z)).coeff i)
      = (fun z => (X : Polynomial ℂ).coeff i - (if i = 0 then φ l z else 0)) := by
    funext z; rw [Polynomial.coeff_sub, Polynomial.coeff_C]
  rw [key]
  apply AnalyticAt.sub analyticAt_const
  by_cases hi : i = 0
  · subst hi; simpa using hφ l
  · simp only [if_neg hi]; exact analyticAt_const

/-- **Uniform coefficient bound for a partial product.** Every coefficient of `∏ i ∈ S, (X - C (a i))`
is bounded in norm by `∏ i ∈ S, (1 + ‖a i‖)`. (By induction on `S` using the recurrence
`((X - C c) * p).coeff (k+1) = p.coeff k - c * p.coeff (k+1)`.) Applied with the `a i` ranging over a
fixed disc, this makes the partial-product coefficients *bounded* near the discriminant point — the
hypothesis the removable-singularity extension (`exists_analyticAt_extend_of_bddUnder`) consumes. -/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ∀ j, ‖(∏ i ∈ S, (X - C (a i))).coeff j‖ ≤ ∏ i ∈ S, (1 + ‖a i‖) := by
  classical
  induction S using Finset.induction with
  | empty =>
      intro j
      simp only [Finset.prod_empty, Polynomial.coeff_one]
      split <;> simp
  | insert i₀ S hi₀ IH =>
      intro j
      rw [Finset.prod_insert hi₀, Finset.prod_insert hi₀]
      have hnn : (0 : ℝ) ≤ ∏ i ∈ S, (1 + ‖a i‖) :=
        Finset.prod_nonneg (fun i _ => by positivity)
      cases j with
      | zero =>
          rw [Polynomial.mul_coeff_zero]
          have hc0 : ((X - C (a i₀)) : Polynomial ℂ).coeff 0 = - a i₀ := by
            simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
          rw [hc0, norm_mul, norm_neg]
          calc ‖a i₀‖ * ‖(∏ i ∈ S, (X - C (a i))).coeff 0‖
              ≤ ‖a i₀‖ * ∏ i ∈ S, (1 + ‖a i‖) :=
                mul_le_mul_of_nonneg_left (IH 0) (norm_nonneg _)
            _ ≤ (1 + ‖a i₀‖) * ∏ i ∈ S, (1 + ‖a i‖) := by
                apply mul_le_mul_of_nonneg_right _ hnn; linarith [norm_nonneg (a i₀)]
      | succ k =>
          rw [coeff_X_sub_C_mul]
          calc ‖(∏ i ∈ S, (X - C (a i))).coeff k
                  - a i₀ * (∏ i ∈ S, (X - C (a i))).coeff (k + 1)‖
              ≤ ‖(∏ i ∈ S, (X - C (a i))).coeff k‖
                  + ‖a i₀ * (∏ i ∈ S, (X - C (a i))).coeff (k + 1)‖ := norm_sub_le _ _
            _ = ‖(∏ i ∈ S, (X - C (a i))).coeff k‖
                  + ‖a i₀‖ * ‖(∏ i ∈ S, (X - C (a i))).coeff (k + 1)‖ := by rw [norm_mul]
            _ ≤ (∏ i ∈ S, (1 + ‖a i‖)) + ‖a i₀‖ * ∏ i ∈ S, (1 + ‖a i‖) :=
                add_le_add (IH k) (mul_le_mul_of_nonneg_left (IH (k + 1)) (norm_nonneg _))
            _ = (1 + ‖a i₀‖) * ∏ i ∈ S, (1 + ‖a i‖) := by ring

/-- **Root-set product = indexing-section product.** When the sections `φ i` are injective (distinct
roots), the partial product over the *set* of roots satisfying a predicate `P` equals the product over
the indices `i` with `P (φ i)`. This is the bridge from the fiberwise partial product (over the finite
root set of the cover) to the section form consumed by `partialProd_filter_coeff_analyticAt`. -/
theorem prod_X_sub_C_image_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → ℂ) (hφ : Function.Injective φ) (P : ℂ → Prop) [DecidablePred P] :
    ∏ t ∈ (Finset.univ.image φ).filter P, (X - C t)
      = ∏ i ∈ Finset.univ.filter (fun i => P (φ i)), (X - C (φ i)) := by
  rw [Finset.filter_image, Finset.prod_image (fun a _ b _ h => hφ h)]

/-- **A monic separable complex polynomial is the product over its (distinct) roots.** Over `ℂ`
(algebraically closed) a monic `p` splits, and separability makes its roots simple, so
`p = ∏ t ∈ p.roots.toFinset, (X - C t)`. -/
theorem eq_prod_roots_toFinset_of_monic_separable {p : Polynomial ℂ}
    (hp : p.Monic) (hsep : p.Separable) :
    p = ∏ t ∈ p.roots.toFinset, (X - C t) := by
  have hcard : Multiset.card p.roots = p.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard
  have hrhs : (∏ t ∈ p.roots.toFinset, (X - C t)) = (p.roots.map (fun a => X - C a)).prod := by
    rw [show (∏ t ∈ p.roots.toFinset, (X - C t))
          = ((p.roots.toFinset).val.map (fun a => X - C a)).prod from rfl,
        Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hsep)]
  rw [hrhs]; exact hprod.symm

/-- **Splitting a monic separable polynomial by a root predicate.** `p` factors as the product over
its `P`-roots times the product over its `¬P`-roots — the algebraic source of the Weierstrass
factorisation `q = h_A · h_B` from a clopen component `A`. -/
theorem eq_prod_filter_mul_prod_filter_not_of_monic_separable {p : Polynomial ℂ}
    (hp : p.Monic) (hsep : p.Separable) (P : ℂ → Prop) [DecidablePred P] :
    p = (∏ t ∈ p.roots.toFinset.filter P, (X - C t))
      * (∏ t ∈ p.roots.toFinset.filter (fun t => ¬ P t), (X - C t)) := by
  conv_lhs => rw [eq_prod_roots_toFinset_of_monic_separable hp hsep]
  exact (Finset.prod_filter_mul_prod_filter_not p.roots.toFinset P (fun t => X - C t)).symm

/-- **`d` injective roots of a monic degree-`d` polynomial are all its roots.** If `φ : Fin d → ℂ` is
injective and each `φ i` is a root of the monic degree-`d` polynomial `p`, then `p.roots.toFinset` is
exactly the image of `φ`. (The image has `d` elements and sits inside `p.roots.toFinset`, whose size is
at most `deg p = d`.) This discharges the `hroots`/`hinj` hypotheses of `globalPartialProd_analyticAt`
from local root sections on the separable locus. -/
theorem roots_toFinset_eq_image_of_monic {p : Polynomial ℂ} {d : ℕ} (hp : p.Monic)
    (hdeg : p.natDegree = d) (φ : Fin d → ℂ) (hinj : Function.Injective φ)
    (hroot : ∀ i, p.IsRoot (φ i)) :
    p.roots.toFinset = Finset.univ.image φ := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hsub : Finset.univ.image φ ⊆ p.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hroot i
  have hcard_img : (Finset.univ.image φ).card = d := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcard_roots : p.roots.toFinset.card ≤ d := by
    calc p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = d := hdeg
  exact (Finset.eq_of_subset_of_card_le hsub (hcard_roots.trans_eq hcard_img.symm)).symm

/-- **Uniform coefficient bound for a partial product with bounded roots.** If every `a i` (`i ∈ S`)
has `‖a i‖ ≤ ε`, then each coefficient of `∏ i ∈ S, (X - C (a i))` is bounded by `(1 + ε) ^ S.card`.
With `S` a subset of the (≤ `m`) roots in a disc of radius `ε`, this gives a `y`-uniform bound on the
factor coefficients — exactly the `BddUnder` hypothesis of the removable-singularity extension. -/
theorem norm_coeff_prod_X_sub_C_le_pow {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    {ε : ℝ} (hbdd : ∀ i ∈ S, ‖a i‖ ≤ ε) (j : ℕ) :
    ‖(∏ i ∈ S, (X - C (a i))).coeff j‖ ≤ (1 + ε) ^ S.card := by
  refine (norm_coeff_prod_X_sub_C_le S a j).trans ?_
  calc ∏ i ∈ S, (1 + ‖a i‖)
      ≤ ∏ i ∈ S, (1 + ε) :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => by linarith [hbdd i hi])
    _ = (1 + ε) ^ S.card := by rw [Finset.prod_const]

/-- **The factor coefficient is bounded by `(1+ε)^(deg p)` when the roots lie in the `ε`-disc.** For
any predicate `P`, every coefficient of the partial product `∏_{t ∈ roots, P t} (X - C t)` is bounded by
`(1 + ε) ^ p.natDegree` once all roots have norm `≤ ε`. This is the `y`-uniform bound (degree is
constant in a Weierstrass family) feeding the removable-singularity extension of `h_A` across `0`. -/
theorem norm_coeff_factor_le {p : Polynomial ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (P : ℂ → Prop) [DecidablePred P]
    (hbdd : ∀ t ∈ p.roots.toFinset, ‖t‖ ≤ ε) (j : ℕ) :
    ‖((p.roots.toFinset.filter P).prod (fun t => X - C t)).coeff j‖ ≤ (1 + ε) ^ p.natDegree := by
  have hbdd' : ∀ t ∈ p.roots.toFinset.filter P, ‖t‖ ≤ ε :=
    fun t ht => hbdd t (Finset.mem_of_mem_filter t ht)
  refine (norm_coeff_prod_X_sub_C_le_pow (p.roots.toFinset.filter P) id hbdd' j).trans ?_
  refine pow_le_pow_right₀ (by linarith) ?_
  calc (p.roots.toFinset.filter P).card
      ≤ p.roots.toFinset.card := Finset.card_filter_le _ _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' _

/-- **A monic divisor of `X ^ m` is a power of `X`.** Since `X` is prime, any monic `p ∣ X ^ m` is
associated to some `X ^ k`, hence (both monic) equals `X ^ (p.natDegree)`. This discharges the
Weierstrass `coeff_zero_vanish` of the factor `h_A` *without root continuity*: from
`H_A(0) · H_B(0) = q(0) = X ^ m` (coefficient continuity) and monicity, each factor at `0` is a power
of `X`. -/
theorem eq_X_pow_of_monic_dvd_X_pow {p : Polynomial ℂ} {m : ℕ} (hp : p.Monic)
    (hdvd : p ∣ X ^ m) : p = X ^ p.natDegree := by
  obtain ⟨k, _, hassoc⟩ := (dvd_prime_pow prime_X m).mp hdvd
  have hpk : p = X ^ k := eq_of_monic_of_associated hp (monic_X_pow k) hassoc
  have : p.natDegree = k := by rw [hpk, natDegree_X_pow]
  rw [this, ← hpk]

/-- **`X ^ m + (lower-degree)` is monic of degree `m`.** The structural form of the Weierstrass factor
`H_A := X ^ d_A + ∑_{j < d_A} C (F_j ·) X ^ j`: a leading `X ^ m` plus a polynomial of degree `< m` is
monic of degree exactly `m`. -/
theorem monic_natDegree_X_pow_add {p : Polynomial ℂ} {m : ℕ} (hp : p.natDegree < m) :
    (X ^ m + p).Monic ∧ (X ^ m + p).natDegree = m := by
  have hdeglt : p.degree < (X ^ m : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hp)
  refine ⟨(monic_X_pow m).add_of_left hdeglt, ?_⟩
  have hdeg_eq : (X ^ m + p : Polynomial ℂ).degree = (m : ℕ) := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt hdeglt, Polynomial.degree_X_pow]
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg_eq

/-- **Monic reconstruction.** A monic polynomial of degree `m` is `X ^ m + ∑_{j < m} C (p.coeff j) X^j`.
Off `0`, the Weierstrass factor `H_A` (defined as `X ^ d_A + ∑_{j<d_A} C (F_j ·) X^j`) thus equals the
partial product `h_A` (monic of degree `d_A`), via this reconstruction applied to `h_A`. -/
theorem monic_eq_X_pow_add_lower {p : Polynomial ℂ} {m : ℕ} (hp : p.Monic) (hdeg : p.natDegree = m) :
    p = X ^ m + ∑ j ∈ Finset.range m, C (p.coeff j) * X ^ j := by
  conv_lhs => rw [p.as_sum_range' (m + 1) (by rw [hdeg]; omega)]
  rw [Finset.sum_range_succ]
  have hcm : p.coeff m = 1 := by have hc := hp.coeff_natDegree; rwa [hdeg] at hc
  rw [hcm]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul]
  rw [add_comm]

/-- **`∑_{j < m} C (a j) X^j` has degree `< m`.** The lower part of the Weierstrass factor `H_A`. -/
theorem degree_sum_C_mul_X_pow_lt {m : ℕ} (a : ℕ → ℂ) :
    (∑ j ∈ Finset.range m, C (a j) * X ^ j).degree < (m : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-- The partial product `∏_{t ∈ S} (X - C t)` is monic. -/
theorem monic_prod_X_sub_C (S : Finset ℂ) : (∏ t ∈ S, (X - C t)).Monic :=
  monic_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)

/-- The partial product `∏_{t ∈ S} (X - C t)` has degree `|S|`. -/
theorem natDegree_prod_X_sub_C (S : Finset ℂ) : (∏ t ∈ S, (X - C t)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ (fun t _ => X_sub_C_ne_zero t)]
  simp

end
