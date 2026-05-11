import Cad.Multivariate.ProjectionTheorem.DiscrNonzero
import Cad.Multivariate.ProjectionTheorem.DiscrMul
import Cad.Multivariate.ProjectionTheorem.DiscrProdInvariant
import Cad.Multivariate.ProjectionTheorem.OrderInvariantFactor
import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Cad.Multivariate.ProjectionTheorem.SquarefreeBasis

/-!
# McCallum's Reduced Projection Theorem (Theorem 3.2.3)

This file contains the statement and proof of Theorem 3.2.3 from McCallum's PhD thesis
"An Improved Projection Operation for Cylindrical Algebraic Decomposition" (1984).

## Main result

**Theorem 3.2.3**: Let `A` be a finite squarefree basis of `r`-variate integral polynomials
(`r ≥ 2`), `S` a connected submanifold of `ℝ^{r-1}`. Suppose each element of `A` is not
identically zero on `S`, and each element of the reduced projection `P(A)` is
order-invariant in `S`. Then:
1. Each element of `A` is degree-invariant on `S`
2. Each element of `A` is analytically delineable on `S`
3. The sections of `A` over `S` are pairwise disjoint
4. Each element of `A` is order-invariant in every section of `A` over `S`
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- Coprime polynomials have no common root after specialization. -/
theorem no_common_root_of_coprime (F G : PolyR n) (hcop : IsCoprime F G)
    (a : Fin n → ℝ) (y : ℝ) :
    ¬ ((specialize F a).IsRoot y ∧ (specialize G a).IsRoot y) := by
  intro ⟨hF, hG⟩
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : specialize (u * F + v * G) a = 1 := by
    rw [huv]; simp [specialize, Polynomial.map_one]
  have h2 : (specialize (u * F + v * G) a).eval y = 1 := by
    rw [h1]; simp
  simp only [specialize, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.eval_add, Polynomial.eval_mul] at h2
  rw [Polynomial.IsRoot] at hF hG
  simp only [specialize] at hF hG
  rw [hF, hG] at h2
  linarith

/-- **Theorem 3.2.3** (McCallum PhD, p.47). -/
theorem mccallum_3_2_3
    (A : Finset (PolyR n))
    (S : Set (Fin n → ℝ))
    (hA : IsSquarefreeBasis A)
    (hA_ne : A.Nonempty)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hnonzero : ∀ f ∈ A, NotIdenticallyZeroOn f S)
    (hP : ∀ g ∈ reducedProjection A, OrderInvariantMv g S) :
    (∀ f ∈ A, DegreeInvariant f S) ∧
    (∀ f ∈ A, AnalyticDelineable f S) ∧
    SectionsDisjoint A S ∧
    OrderInvariantInAllSections A S := by
  have hS_ne : S.Nonempty := hS_conn.1
  have hcoeff_oi : ∀ f ∈ A, ∀ k : ℕ, f.coeff k ≠ 0 →
      OrderInvariantMv (f.coeff k) S := by
    intro f hf k hk
    apply hP; left; left
    exact ⟨f, hf, k, rfl, hk⟩
  have h_deg : ∀ f ∈ A, DegreeInvariant f S := by
    intro f hf
    exact degree_invariant_of_coeff_order_invariant S f (hcoeff_oi f hf)
  have h_disjoint : SectionsDisjoint A S := by
    intro F hF G hG hne a _
    rw [Set.disjoint_left]
    intro y hyF hyG
    exact no_common_root_of_coprime F G
      (hA.pairwise_coprime F hF G hG hne) a y ⟨hyF, hyG⟩
  have hdisc_oi : ∀ f ∈ A, OrderInvariantMv (Polynomial.discr f) S := by
    intro f hf
    by_cases hdeg : 2 ≤ f.natDegree
    · apply hP; left; right; exact ⟨f, hf, hdeg, rfl⟩
    · have hpos := hA.pos_degree f hf
      have h1 : f.natDegree = 1 := by omega
      exact discr_degree_one_order_invariant S f h1
  have hres_oi : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      OrderInvariantMv (Polynomial.resultant f g) S := by
    intro f hf g hg hne
    apply hP; right
    exact ⟨f, hf, g, hg, hne, hA.pos_degree f hf, hA.pos_degree g hg, rfl⟩
  set f := ∏ g ∈ A, g with hf_def
  have hf_sf : Squarefree f :=
    prod_squarefree_of_coprime A hA.sq_free hA.pairwise_coprime
  have hf_pos : 0 < f.natDegree :=
    prod_pos_degree A hA_ne hA.pos_degree
  have hf_discr_ne : Polynomial.discr f ≠ 0 :=
    discr_ne_zero_of_squarefree f hf_sf hf_pos
  have hf_nz : NotIdenticallyZeroOn f S :=
    not_identically_zero_prod S A hnonzero hcoeff_oi hS_ne
  have hf_deg : DegreeInvariant f S :=
    degree_invariant_prod S A h_deg
      (fun f hf => specialize_nonzero_everywhere f S (hnonzero f hf) (hcoeff_oi f hf))
  have hf_discr_oi : OrderInvariantMv (Polynomial.discr f) S :=
    discr_prod_order_invariant S A hA.pos_degree hA.sq_free hA.pairwise_coprime hdisc_oi hres_oi
  obtain ⟨hf_delin, hf_oi_sections⟩ := lifting_theorem S f hS_submfld hS_conn hf_pos hf_sf
    hf_discr_ne hf_nz hf_deg hf_discr_oi
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

#print axioms mccallum_3_2_3

end
