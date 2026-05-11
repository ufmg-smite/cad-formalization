import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Cad.Multivariate.ProjectionTheorem.DiscrProdInvariant
import Cad.Multivariate.ProjectionTheorem.OrderInvariantFactor
import Cad.Multivariate.ProjectionTheorem.SquarefreeBasis
import Cad.Multivariate.ProjectionTheorem.Projection

/-!
# Generalized Projection Theorem (Theorem 3.2.3')

Proof that the generalized lifting theorem (Theorem 3.2.1') implies the
generalized projection theorem (Theorem 3.2.3'). The generalized versions
replace discriminants and resultants with arbitrary nonzero elements of the
corresponding elimination ideals `⟨F, F'⟩ ∩ R[x]` and `⟨F, G⟩ ∩ R[x]`.

## Main results

- `lifting_theorem_generalized` (axiom): Theorem 3.2.1' — the generalized lifting theorem.
- `nullstellensatz_elim` (theorem): a power of the product of elimination ideal elements
  belongs to `⟨f, f'⟩ ∩ R[x]`, proved via the radical-equals-intersection-of-primes
  characterization.
- `mccallum_3_2_3_generalized`: Theorem 3.2.3' — the generalized projection theorem,
  proved from the two axioms above.

## References

- `patched_3_2_3.pdf`: Statement and proof of Theorems 3.2.1' and 3.2.3'.
- McCallum, "An Improved Projection Operation for Cylindrical Algebraic Decomposition" (1985).
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-! ### Axiom: Generalized Lifting Theorem (Theorem 3.2.1') -/

/-- **Theorem 3.2.1'** (Generalized Lifting Theorem).

This generalizes `lifting_theorem` by replacing the discriminant hypothesis with an
arbitrary nonzero element `P ∈ ⟨f, ∂f/∂xᵣ⟩ ∩ R[x]` that is order-invariant on `S`.
The discriminant is one such element, so the original theorem is a special case. -/
axiom lifting_theorem_generalized
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hpos : 0 < f.natDegree)
    (hsf : Squarefree f)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S))

/-! ### Elimination product -/

/-- The product `R = (∏ F ∈ A, d F) · (∏ F ∈ A, ∏ G ∈ A \ {F}, r F G)` of
the chosen elimination ideal elements. This is the `R` from the proof in
`patched_3_2_3.pdf`, except we include both `r(F,G)` and `r(G,F)` for each
pair; this only makes `R` larger and does not affect the argument. -/
def elimProduct (A : Finset (PolyR n))
    (d : PolyR n → MvPolyR n) (r : PolyR n → PolyR n → MvPolyR n) : MvPolyR n :=
  (∏ F ∈ A, d F) * (∏ F ∈ A, ∏ G ∈ A.erase F, r F G)

private theorem erase_mem_ne {A : Finset (PolyR n)} {F G : PolyR n}
    (hG : G ∈ A.erase F) : G ∈ A ∧ F ≠ G :=
  ⟨Finset.mem_of_mem_erase hG, fun h => Finset.ne_of_mem_erase hG h.symm⟩

theorem elimProduct_ne_zero
    (A : Finset (PolyR n))
    (d : PolyR n → MvPolyR n) (r : PolyR n → PolyR n → MvPolyR n)
    (hd_ne : ∀ F ∈ A, d F ≠ 0)
    (hr_ne : ∀ F ∈ A, ∀ G ∈ A, F ≠ G → r F G ≠ 0) :
    elimProduct A d r ≠ 0 := by
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun F hF => hd_ne F hF)
  · apply Finset.prod_ne_zero_iff.mpr; intro F hF
    apply Finset.prod_ne_zero_iff.mpr; intro G hG
    exact hr_ne F hF G (erase_mem_ne hG).1 (erase_mem_ne hG).2

theorem elimProduct_order_invariant
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (d : PolyR n → MvPolyR n) (r : PolyR n → PolyR n → MvPolyR n)
    (hd_oi : ∀ F ∈ A, OrderInvariantMv (d F) S)
    (hr_oi : ∀ F ∈ A, ∀ G ∈ A, F ≠ G → OrderInvariantMv (r F G) S) :
    OrderInvariantMv (elimProduct A d r) S := by
  apply order_invariant_mul_mv
  · exact order_invariant_prod_mv S A (fun F => d F) (fun F hF => hd_oi F hF)
  · apply order_invariant_prod_mv S A (fun F => ∏ G ∈ A.erase F, r F G)
    intro F hF
    apply order_invariant_prod_mv S (A.erase F) (fun G => r F G)
    intro G hG
    exact hr_oi F hF G (erase_mem_ne hG).1 (erase_mem_ne hG).2

/-! ### Order-invariance of powers -/

theorem order_invariant_pow_mv
    (S : Set (Fin n → ℝ)) (g : MvPolyR n) (N : ℕ)
    (hg : OrderInvariantMv g S) :
    OrderInvariantMv (g ^ N) S := by
  induction N with
  | zero =>
    simp only [pow_zero]
    intro a _ b _
    have h1 : polyOrder n (1 : MvPolyR n) a = 0 :=
      (polyOrder_zero_iff n 1 a).mpr (by simp)
    have h2 : polyOrder n (1 : MvPolyR n) b = 0 :=
      (polyOrder_zero_iff n 1 b).mpr (by simp)
    rw [h1, h2]
  | succ k ih =>
    rw [pow_succ]
    exact order_invariant_mul_mv S _ _ ih hg

/-! ### Helper: cofactor of F in the product -/

/-- The cofactor of `F` in `∏ H ∈ A, H`, i.e., `∏ H ∈ A \ {F}, H`. -/
abbrev cofactorProd (A : Finset (PolyR n)) (F : PolyR n) : PolyR n :=
  ∏ H ∈ A.erase F, H

lemma prod_eq_mul_cofactorProd (A : Finset (PolyR n)) (F : PolyR n) (hF : F ∈ A) :
    ∏ H ∈ A, H = F * cofactorProd A F :=
  (Finset.mul_prod_erase A id hF).symm

/-! ### Algebraic helper lemmas for elimination ideal membership -/

/-- The resultant-like factor `cofactor(F) · cofactor(G) · C(r(F,G))` belongs to
`⟨f, f'⟩` where `f = ∏ H ∈ A, H`. Since `C(r) ∈ ⟨F, G⟩`, multiplying generators
by cofactors yields multiples of `f`. -/
lemma cofactors_mul_r_mem (A : Finset (PolyR n)) (F G : PolyR n)
    (hF : F ∈ A) (hG : G ∈ A)
    (r_FG : MvPolyR n)
    (hr : Polynomial.C r_FG ∈ Ideal.span ({F, G} : Set (PolyR n))) :
    cofactorProd A F * cofactorProd A G * Polynomial.C r_FG ∈
      Ideal.span ({∏ H ∈ A, H, Polynomial.derivative (∏ H ∈ A, H)} : Set (PolyR n)) := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hr
  rw [← huv]
  have h1 : F * cofactorProd A F = ∏ H ∈ A, H := (prod_eq_mul_cofactorProd A F hF).symm
  have h2 : G * cofactorProd A G = ∏ H ∈ A, H := (prod_eq_mul_cofactorProd A G hG).symm
  have key : cofactorProd A F * cofactorProd A G * (u * F + v * G) =
      (u * cofactorProd A G + v * cofactorProd A F) * (∏ H ∈ A, H) := by
    calc cofactorProd A F * cofactorProd A G * (u * F + v * G)
        = u * (F * cofactorProd A F) * cofactorProd A G +
          v * cofactorProd A F * (G * cofactorProd A G) := by ring
      _ = u * (∏ H ∈ A, H) * cofactorProd A G +
          v * cofactorProd A F * (∏ H ∈ A, H) := by rw [h1, h2]
      _ = (u * cofactorProd A G + v * cofactorProd A F) * (∏ H ∈ A, H) := by ring
  rw [key]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- The discriminant-like factor `cofactor(F)² · C(d(F))` belongs to `⟨f, f'⟩`.
Uses the product rule: `f' = F'·G_F + F·G_F'`, giving
`G_F²·(u·F + v·F') = (u·G_F - v·G_F')·f + v·G_F·f'`. -/
lemma cofactor_sq_mul_d_mem (A : Finset (PolyR n)) (F : PolyR n) (hF : F ∈ A)
    (d_F : MvPolyR n)
    (hd : Polynomial.C d_F ∈ Ideal.span ({F, Polynomial.derivative F} : Set (PolyR n))) :
    cofactorProd A F ^ 2 * Polynomial.C d_F ∈
      Ideal.span ({∏ H ∈ A, H, Polynomial.derivative (∏ H ∈ A, H)} : Set (PolyR n)) := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hd
  rw [← huv]
  have h1 : F * cofactorProd A F = ∏ H ∈ A, H := (prod_eq_mul_cofactorProd A F hF).symm
  have hder : Polynomial.derivative (∏ H ∈ A, H) =
      Polynomial.derivative F * cofactorProd A F +
        F * Polynomial.derivative (cofactorProd A F) := by
    conv_lhs => rw [prod_eq_mul_cofactorProd A F hF]
    exact Polynomial.derivative_mul
  have key : cofactorProd A F ^ 2 * (u * F + v * Polynomial.derivative F) =
      (u * cofactorProd A F - v * Polynomial.derivative (cofactorProd A F)) * (∏ H ∈ A, H) +
      v * cofactorProd A F * Polynomial.derivative (∏ H ∈ A, H) := by
    calc cofactorProd A F ^ 2 * (u * F + v * Polynomial.derivative F)
        = u * (F * cofactorProd A F) * cofactorProd A F +
          v * cofactorProd A F *
            (Polynomial.derivative F * cofactorProd A F +
              F * Polynomial.derivative (cofactorProd A F)) -
          v * Polynomial.derivative (cofactorProd A F) *
            (F * cofactorProd A F) := by ring
      _ = u * (∏ H ∈ A, H) * cofactorProd A F +
          v * cofactorProd A F * Polynomial.derivative (∏ H ∈ A, H) -
          v * Polynomial.derivative (cofactorProd A F) * (∏ H ∈ A, H) := by
        rw [h1, ← hder]
      _ = (u * cofactorProd A F - v * Polynomial.derivative (cofactorProd A F)) * (∏ H ∈ A, H) +
          v * cofactorProd A F * Polynomial.derivative (∏ H ∈ A, H) := by ring
  rw [key]
  apply Ideal.add_mem
  · exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_insert _ _))
  · exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)))

/-! ### Nullstellensatz for elimination ideals -/

/-- **Nullstellensatz for elimination ideals**.

Given `d(Fᵢ) ∈ ⟨Fᵢ, Fᵢ'⟩ ∩ R[x]` and `r(Fᵢ, Fⱼ) ∈ ⟨Fᵢ, Fⱼ⟩ ∩ R[x]`, some positive
power of `R = ∏ d(Fᵢ) · ∏ r(Fᵢ, Fⱼ)` belongs to `⟨f, f'⟩ ∩ R[x]` where `f = ∏ Fᵢ`.

The proof uses the algebraic characterization of the radical: `C(R) ∈ √⟨f,f'⟩` iff
`C(R) ∈ P` for every prime `P ⊇ ⟨f,f'⟩`. For such a prime, `f ∈ P` forces some
`F₀ ∈ P` (primality), and `f' ∈ P` then forces `F₀' ∈ P` or some `H₀ ≠ F₀` with
`H₀ ∈ P`. In either case, one factor of `R` lies in `P` via ideal containment. -/
theorem nullstellensatz_elim
    (A : Finset (PolyR n))
    (d : PolyR n → MvPolyR n)
    (hd_mem : ∀ F ∈ A,
      Polynomial.C (d F) ∈
        Ideal.span ({F, Polynomial.derivative F} : Set (PolyR n)))
    (r : PolyR n → PolyR n → MvPolyR n)
    (hr_mem : ∀ F ∈ A, ∀ G ∈ A, F ≠ G →
      Polynomial.C (r F G) ∈ Ideal.span ({F, G} : Set (PolyR n))) :
    ∃ N : ℕ, 0 < N ∧
      Polynomial.C (elimProduct A d r ^ N) ∈
        Ideal.span ({∏ F ∈ A, F,
          Polynomial.derivative (∏ F ∈ A, F)} : Set (PolyR n)) := by
  set I := Ideal.span ({∏ F ∈ A, F, Polynomial.derivative (∏ F ∈ A, F)} : Set (PolyR n))
  have h_radical : Polynomial.C (elimProduct A d r) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hPI, hPprime⟩
    haveI := hPprime
    have hfP : (∏ F ∈ A, F) ∈ P :=
      hPI (Ideal.subset_span (Set.mem_insert _ _))
    have hf'P : Polynomial.derivative (∏ F ∈ A, F) ∈ P :=
      hPI (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)))
    obtain ⟨F₀, hF₀A, hF₀P⟩ := Ideal.IsPrime.prod_mem_iff.mp hfP
    have hder : Polynomial.derivative (∏ F ∈ A, F) =
        Polynomial.derivative F₀ * cofactorProd A F₀ +
          F₀ * Polynomial.derivative (cofactorProd A F₀) := by
      conv_lhs => rw [prod_eq_mul_cofactorProd A F₀ hF₀A]
      exact Polynomial.derivative_mul
    have hFG'P : F₀ * Polynomial.derivative (cofactorProd A F₀) ∈ P := by
      rw [mul_comm]; exact Ideal.mul_mem_left P _ hF₀P
    have hF'GP : Polynomial.derivative F₀ * cofactorProd A F₀ ∈ P := by
      have h : Polynomial.derivative F₀ * cofactorProd A F₀ =
          Polynomial.derivative (∏ F ∈ A, F) -
            F₀ * Polynomial.derivative (cofactorProd A F₀) := by
        rw [hder]; ring
      rw [h]; exact sub_mem hf'P hFG'P
    have hC_split : Polynomial.C (elimProduct A d r) =
        Polynomial.C (∏ F ∈ A, d F) *
          Polynomial.C (∏ F ∈ A, ∏ G ∈ A.erase F, r F G) := by
      unfold elimProduct; exact map_mul Polynomial.C _ _
    rcases hPprime.mem_or_mem hF'GP with hF₀'P | hG₀P
    · have hle : Ideal.span ({F₀, Polynomial.derivative F₀} : Set (PolyR n)) ≤ P :=
        Ideal.span_le.mpr (Set.insert_subset_iff.mpr
          ⟨hF₀P, Set.singleton_subset_iff.mpr hF₀'P⟩)
      rw [hC_split, mul_comm]
      apply Ideal.mul_mem_left
      rw [map_prod]
      exact Ideal.IsPrime.prod_mem_iff.mpr ⟨F₀, hF₀A, hle (hd_mem F₀ hF₀A)⟩
    · obtain ⟨H₀, hH₀e, hH₀P⟩ := Ideal.IsPrime.prod_mem_iff.mp hG₀P
      have ⟨hH₀A, hF₀neH₀⟩ := erase_mem_ne hH₀e
      have hle : Ideal.span ({F₀, H₀} : Set (PolyR n)) ≤ P :=
        Ideal.span_le.mpr (Set.insert_subset_iff.mpr
          ⟨hF₀P, Set.singleton_subset_iff.mpr hH₀P⟩)
      rw [hC_split]
      apply Ideal.mul_mem_left
      rw [map_prod]
      exact Ideal.IsPrime.prod_mem_iff.mpr ⟨F₀, hF₀A, by
        rw [map_prod]
        exact Ideal.IsPrime.prod_mem_iff.mpr ⟨H₀, hH₀e,
          hle (hr_mem F₀ hF₀A H₀ hH₀A hF₀neH₀)⟩⟩
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp h_radical
  exact ⟨N + 1, Nat.succ_pos N, by
    rw [map_pow]
    have h : Polynomial.C (elimProduct A d r) ^ (N + 1) =
        Polynomial.C (elimProduct A d r) * Polynomial.C (elimProduct A d r) ^ N := by ring
    rw [h]; exact Ideal.mul_mem_left _ _ hN⟩

/-! ### Generalized Projection Theorem (Theorem 3.2.3') -/

/-- **Theorem 3.2.3'** (Generalized Projection Theorem).

Let `A` be a finite squarefree basis, `S` a connected analytic submanifold.
For each `F ∈ A`, let `d(F)` be a chosen nonzero element of `⟨F, F'⟩ ∩ R[x]`, and
for each pair `F ≠ G`, let `r(F,G)` be a chosen nonzero element of `⟨F, G⟩ ∩ R[x]`.
Suppose all coefficients of elements of `A` and all chosen `d(F)`, `r(F,G)` are
order-invariant on `S`, and each element of `A` is not identically zero on `S`.

Then each element of `A` is degree-invariant and analytically delineable on `S`,
the sections of `A` over `S` are pairwise disjoint, and each element of `A` is
order-invariant in every section of `A` over `S`.

This generalizes `mccallum_3_2_3`: taking `d(F) = disc(F)` and `r(F,G) = Res(F,G)`
recovers the original theorem. -/
theorem mccallum_3_2_3_generalized
    (A : Finset (PolyR n))
    (S : Set (Fin n → ℝ))
    (hA : IsSquarefreeBasis A)
    (hA_ne : A.Nonempty)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hnonzero : ∀ f ∈ A, NotIdenticallyZeroOn f S)
    (hcoeff : ∀ f ∈ A, ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S)
    (d : PolyR n → MvPolyR n)
    (hd_ne : ∀ F ∈ A, d F ≠ 0)
    (hd_mem : ∀ F ∈ A,
      Polynomial.C (d F) ∈
        Ideal.span ({F, Polynomial.derivative F} : Set (PolyR n)))
    (hd_oi : ∀ F ∈ A, OrderInvariantMv (d F) S)
    (r : PolyR n → PolyR n → MvPolyR n)
    (hr_ne : ∀ F ∈ A, ∀ G ∈ A, F ≠ G → r F G ≠ 0)
    (hr_mem : ∀ F ∈ A, ∀ G ∈ A, F ≠ G →
      Polynomial.C (r F G) ∈ Ideal.span ({F, G} : Set (PolyR n)))
    (hr_oi : ∀ F ∈ A, ∀ G ∈ A, F ≠ G → OrderInvariantMv (r F G) S) :
    (∀ f ∈ A, DegreeInvariant f S) ∧
    (∀ f ∈ A, AnalyticDelineable f S) ∧
    SectionsDisjoint A S ∧
    OrderInvariantInAllSections A S := by
  have hS_ne : S.Nonempty := hS_conn.1
  -- Degree invariance from coefficient order-invariance
  have h_deg : ∀ f ∈ A, DegreeInvariant f S :=
    fun f hf => degree_invariant_of_coeff_order_invariant S f (hcoeff f hf)
  -- Sections are disjoint by coprimality
  have h_disjoint : SectionsDisjoint A S := by
    intro F hF G hG hne a _
    rw [Set.disjoint_left]
    intro y hyF hyG
    exact no_common_root_of_coprime F G
      (hA.pairwise_coprime F hF G hG hne) a y ⟨hyF, hyG⟩
  -- Form the product f = ∏ A
  set f := ∏ g ∈ A, g with hf_def
  have hf_sf : Squarefree f :=
    prod_squarefree_of_coprime A hA.sq_free hA.pairwise_coprime
  have hf_pos : 0 < f.natDegree :=
    prod_pos_degree A hA_ne hA.pos_degree
  have hf_nz : NotIdenticallyZeroOn f S :=
    not_identically_zero_prod S A hnonzero hcoeff hS_ne
  have hf_deg : DegreeInvariant f S :=
    degree_invariant_prod S A h_deg
      (fun f hf => specialize_nonzero_everywhere f S (hnonzero f hf) (hcoeff f hf))
  -- Build P = R^N via the Nullstellensatz
  have hR_ne : elimProduct A d r ≠ 0 :=
    elimProduct_ne_zero A d r hd_ne hr_ne
  have hR_oi : OrderInvariantMv (elimProduct A d r) S :=
    elimProduct_order_invariant S A d r hd_oi hr_oi
  obtain ⟨N, _, hPN_mem⟩ := nullstellensatz_elim A d hd_mem r hr_mem
  set P := elimProduct A d r ^ N
  have hP_ne : P ≠ 0 := pow_ne_zero N hR_ne
  have hP_oi : OrderInvariantMv P S := order_invariant_pow_mv S _ N hR_oi
  -- Apply the generalized lifting theorem to f with witness P
  obtain ⟨hf_delin, hf_oi_sections⟩ := lifting_theorem_generalized S f hS_submfld hS_conn
    hf_pos hf_sf hf_nz hf_deg P hP_ne hPN_mem hP_oi
  -- Factor the conclusions back to individual polynomials
  refine ⟨h_deg, ?_, h_disjoint, ?_⟩
  · exact delineable_factor_of_delineable_prod S hS_conn.isPreconnected A
      hA.pairwise_coprime hf_delin
  · intro F hF G hG θ hθ_cont hθ_root
    have hθ_prod : IsRootFunction (∏ g ∈ A, g) θ S :=
      root_function_factor_of_prod S A G hG θ hθ_root
    have hprod_oi : OrderInvariantFull (∏ g ∈ A, g) (SectionGraph θ S) :=
      hf_oi_sections θ hθ_cont hθ_prod
    have hT_preconn : IsPreconnected (SectionGraph θ S) := by
      have : SectionGraph θ S = (fun a => (a, θ a)) '' S := by
        ext p; simp [SectionGraph]; exact ⟨fun ⟨h1, h2⟩ => ⟨p.1, h1, Prod.ext rfl h2.symm⟩,
          fun ⟨a, ha, he⟩ => ⟨he ▸ ha, by rw [← he]⟩⟩
      rw [this]
      exact hS_conn.isPreconnected.image _
        (continuousOn_id.prodMk hθ_cont)
    have hA_ne_zero : ∀ f ∈ A, f ≠ 0 :=
      fun f hf h => by linarith [hA.pos_degree f hf, show f.natDegree = 0 from by rw [h]; simp]
    exact order_invariant_full_factor_of_prod A (SectionGraph θ S) hT_preconn hA_ne_zero
      hprod_oi F hF

#print axioms mccallum_3_2_3_generalized

end
