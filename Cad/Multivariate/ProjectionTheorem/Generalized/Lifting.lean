import Cad.Multivariate.ProjectionTheorem.Prerequisites
import Cad.Multivariate.ProjectionTheorem.DiscrProdInvariant
import Cad.Multivariate.ProjectionTheorem.OrderComp
import Cad.Multivariate.ProjectionTheorem.SquarefreeBasis
import Cad.Multivariate.ProjectionTheorem.Generalized.SimpleRoots
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Generalized Lifting Theorem (Theorem 3.2.1')

Proof of the generalized lifting theorem, which replaces the discriminant hypothesis
of the original Theorem 3.2.1 with an arbitrary nonzero element
`P ∈ ⟨f, ∂f/∂xᵣ⟩ ∩ ℝ[x]` that is order-invariant on `S`.

## Proof outline

The proof splits into two cases by the dimension `s` of `S`:

- **Case s = r - 1** (S is open): `P` nonzero and order-invariant on an open connected set
  forces `P` to be nowhere-vanishing. Since `P ∈ ⟨f, f'⟩`, this means `f` has no repeated
  roots at any point of `S`. The implicit function theorem gives simple root sections.

- **Case 1 ≤ s ≤ r - 2** (S has positive codimension): After a coordinate change (submanifold
  chart), complexification, and Weierstrass preparation `g = u·h`, we use the elimination
  ideal structure: `P̃ ∈ ⟨h, h'⟩ ∩ O(Δ) = (disc(h))`, so `P̃ = disc(h)·Q`. The order
  additivity lemma then forces `disc(h)` to be order-invariant. Zariski's theorem applies.

## References

- `thesis/generalized/proof.tex`: Full informal proof.
- McCallum, "An Improved Projection Operation for CAD" (1985), §3.3.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-! ### Case s = r - 1: S is open -/

/-- A nonzero multivariate polynomial over `ℝ` cannot vanish on all of a nonempty
open set. This follows from `MvPolynomial.funext_set` applied to an open box
(product of open intervals) contained in the open set. -/
theorem mvpoly_nonzero_on_open (P : MvPolyR n) (hP : P ≠ 0)
    (S : Set (Fin n → ℝ)) (hS_open : IsOpen S) (hS_ne : S.Nonempty) :
    ∃ a ∈ S, MvPolynomial.eval a P ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hP
  obtain ⟨a₀, ha₀⟩ := hS_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS_open a₀ ha₀
  set s := fun i : Fin n => Set.Ioo (a₀ i - ε) (a₀ i + ε) with hs_def
  have hs_inf : ∀ i, (s i).Infinite := by
    intro i; exact Set.Ioo_infinite (by linarith)
  have hpi_sub : Set.pi Set.univ s ⊆ S := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have := hx i (Set.mem_univ i)
    rw [hs_def, Set.mem_Ioo] at this
    rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hsub : ∀ x ∈ Set.pi Set.univ s, MvPolynomial.eval x P = MvPolynomial.eval x 0 := by
    intro x hx
    simp [hall x (hpi_sub hx)]
  exact MvPolynomial.funext_set s hs_inf hsub

/-- When `S` is open and connected, an order-invariant nonzero polynomial on `S` is
nowhere-vanishing. This is because on an open connected subset of `ℝⁿ`, a polynomial
with constant vanishing order is either identically zero or has order 0 everywhere. -/
theorem order_invariant_nowhere_vanishing_on_open
    (S : Set (Fin n → ℝ))
    (P : MvPolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hP_ne : P ≠ 0)
    (hP_oi : OrderInvariantMv P S) :
    ∀ a ∈ S, MvPolynomial.eval a P ≠ 0 := by
  obtain ⟨a₀, ha₀S, ha₀_ne⟩ := mvpoly_nonzero_on_open P hP_ne S hS_open hS_conn.1
  have hord₀ : polyOrder n P a₀ = 0 := (polyOrder_zero_iff n P a₀).mpr ha₀_ne
  intro a ha
  have hord : polyOrder n P a = 0 := by rw [hP_oi a ha a₀ ha₀S]; exact hord₀
  exact (polyOrder_zero_iff n P a).mp hord


/-- If `P ∈ ⟨f, f'⟩ ∩ ℝ[x]` and `P(a) ≠ 0`, then `f(a, ·)` is separable (coprime with
its derivative). This is because the Bézout identity `C(P) = A·f + B·f'` specializes to
give `C(P(a)) ∈ ⟨f(a,·), f'(a,·)⟩`, and `P(a) ≠ 0` makes this a unit. -/
theorem separable_of_elim_nonvanishing
    (f : PolyR n)
    (P : MvPolyR n)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (a : Fin n → ℝ)
    (hP_nz : MvPolynomial.eval a P ≠ 0) :
    IsCoprime (specialize f a) (Polynomial.derivative (specialize f a)) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP_mem
  have hspec : specialize (Polynomial.C P) a =
      specialize A a * specialize f a +
      specialize B a * specialize (Polynomial.derivative f) a := by
    have : specialize (A * f + B * Polynomial.derivative f) a =
        specialize A a * specialize f a +
        specialize B a * specialize (Polynomial.derivative f) a := by
      simp [specialize, Polynomial.map_add, Polynomial.map_mul]
    rw [← this, ← hAB]
  have hCP : specialize (Polynomial.C P) a = Polynomial.C (MvPolynomial.eval a P) := by
    simp [specialize, Polynomial.map_C]
  have hder : specialize (Polynomial.derivative f) a =
      Polynomial.derivative (specialize f a) := by
    simp [specialize, Polynomial.derivative_map]
  rw [hCP, hder] at hspec
  have hunit : IsUnit (Polynomial.C (MvPolynomial.eval a P)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hP_nz)
  rw [isUnit_iff_exists_inv] at hunit
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u * specialize A a, u * specialize B a, ?_⟩
  calc (u * specialize A a) * specialize f a +
        (u * specialize B a) * Polynomial.derivative (specialize f a)
      = u * (specialize A a * specialize f a +
             specialize B a * Polynomial.derivative (specialize f a)) := by ring
    _ = u * Polynomial.C (MvPolynomial.eval a P) := by rw [← hspec]
    _ = 1 := by rw [mul_comm]; exact hu

/-! ### Delineability from separability (proved in SimpleRoots.lean) -/

/-- A polynomial that is separable (coprime with its derivative) at every point
of a connected open set is analytically delineable there, and order-invariant in each section.

This is `simple_roots_delineable'` from `Cad.Multivariate.ProjectionTheorem.Generalized.SimpleRoots`, which proves it
from the IFT axiom + root continuity axiom + orderFull infrastructure. -/
theorem simple_roots_delineable
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hdeg : DegreeInvariant f S)
    (hsep : ∀ a ∈ S, IsCoprime (specialize f a) (Polynomial.derivative (specialize f a))) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) :=
  simple_roots_delineable' S f hS_open hS_conn hdeg hsep

/-- Case s = r - 1 of the generalized lifting theorem.
When `S` is an open connected subset of `ℝ^{r-1}`, the theorem holds. -/
theorem lifting_generalized_open_case
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hdeg : DegreeInvariant f S)
    (P : MvPolyR n)
    (hP_ne : P ≠ 0)
    (hP_mem : Polynomial.C P ∈
      Ideal.span ({f, Polynomial.derivative f} : Set (PolyR n)))
    (hP_oi : OrderInvariantMv P S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S)) := by
  have hP_nv := order_invariant_nowhere_vanishing_on_open S P hS_open hS_conn hP_ne hP_oi
  have hsep : ∀ a ∈ S, IsCoprime (specialize f a) (Polynomial.derivative (specialize f a)) :=
    fun a ha => separable_of_elim_nonvanishing f P hP_mem a (hP_nv a ha)
  exact simple_roots_delineable S f hS_open hS_conn hdeg hsep

/-! ### Order additivity lemma (Thesis Lemma 4.1) -/

section OrderAdditivity

open scoped Topology
open Filter

end OrderAdditivity

/-! ### Norm identity for monic polynomials -/

section NormResultant

/-- Norm factorization: `norm K (mk ((X - C a) * h') g) = eval a g * norm K (mk h' g)` for
monic h'. Uses `LinearMap.det_eq_det_mul_det` on the kernel of the projection
`AdjoinRoot ((X-C a) * h') → AdjoinRoot h'`, which is 1-dimensional with scalar action g(a). -/
private lemma norm_mk_mul_X_sub_C {K : Type*} [Field K] (a : K) (h' g : Polynomial K)
    (hm' : h'.Monic) :
    Algebra.norm K (AdjoinRoot.mk ((Polynomial.X - Polynomial.C a) * h') g) =
      Polynomial.eval a g * Algebra.norm K (AdjoinRoot.mk h' g) := by
  set h := (Polynomial.X - Polynomial.C a) * h' with h_def
  have hm : h.Monic := (Polynomial.monic_X_sub_C a).mul hm'
  haveI := hm.finite_adjoinRoot (R := K)
  -- The projection π : AdjoinRoot h →ₐ[K] AdjoinRoot h'
  have heval : Polynomial.aeval (AdjoinRoot.root h') h = 0 := by
    rw [AdjoinRoot.aeval_eq, h_def, map_mul, AdjoinRoot.mk_self, mul_zero]
  let π : AdjoinRoot h →ₐ[K] AdjoinRoot h' :=
    AdjoinRoot.liftAlgHom h (AdjoinRoot.ofAlgHom K h') (AdjoinRoot.root h') (by finiteness)
  have hπ_mk (p : Polynomial K) : π (AdjoinRoot.mk h p) = AdjoinRoot.mk h' p := by
    show AdjoinRoot.liftHom h (AdjoinRoot.root h') heval (AdjoinRoot.mk h p) = _
    exact AdjoinRoot.aeval_eq p
  -- Left multiplication by mk h g, and its kernel
  let e : AdjoinRoot h →ₗ[K] AdjoinRoot h :=
    (Algebra.lmul K (AdjoinRoot h)) (AdjoinRoot.mk h g)
  let W : Submodule K (AdjoinRoot h) := π.toLinearMap.ker
  have he : W ≤ W.comap e := by
    intro w hw
    simp only [Submodule.mem_comap, W, LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hw ⊢
    show π (AdjoinRoot.mk h g * w) = 0
    rw [map_mul, hw, mul_zero]
  -- Unfold norm to det and apply det factorization
  simp only [Algebra.norm_apply]
  show e.det = Polynomial.eval a g *
    (Algebra.lmul K (AdjoinRoot h') (AdjoinRoot.mk h' g)).det
  rw [LinearMap.det_eq_det_mul_det W e he]
  -- π is surjective (shared between both goals)
  have hπ_surj : Function.Surjective π.toLinearMap := by
    intro y; obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨AdjoinRoot.mk h p, hπ_mk p⟩
  congr 1
  · -- det(e|_W) = eval a g
    -- Convert he to explicit form for LinearMap.restrict
    have he' : ∀ x ∈ W, e x ∈ W := fun x hx => he hx
    change (e.restrict he').det = Polynomial.eval a g
    -- e acts as scalar (eval a g) on W
    have hscalar : e.restrict he' = (Polynomial.eval a g) • LinearMap.id := by
      ext ⟨w, hw⟩
      simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
        SetLike.val_smul, e, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
      rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul]
      -- Decompose w as mk h f before using map_sub/map_mul
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective w
      change (AdjoinRoot.mk h g - AdjoinRoot.mk h
        (Polynomial.C (Polynomial.eval a g))) * AdjoinRoot.mk h f = 0
      rw [← map_sub, ← map_mul]
      have hmk_zero : AdjoinRoot.mk h' f = 0 := by
        have := LinearMap.mem_ker.mp hw
        rwa [AlgHom.toLinearMap_apply, hπ_mk] at this
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_eq_zero.mp hmk_zero
      have hroot : Polynomial.IsRoot (g - Polynomial.C (Polynomial.eval a g)) a := by
        simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
      obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      exact AdjoinRoot.mk_eq_zero.mpr ⟨r * q, by rw [hr, h_def]; ring⟩
    -- finrank K W = 1 by rank-nullity
    have hfr_W : Module.finrank K ↥W = 1 := by
      have h1 := Submodule.finrank_quotient_add_finrank W
      have h2 : Module.finrank K (AdjoinRoot h ⧸ W) = h'.natDegree := by
        rw [LinearEquiv.finrank_eq (π.toLinearMap.quotKerEquivOfSurjective hπ_surj)]
        exact (AdjoinRoot.powerBasis hm'.ne_zero).finrank
      have h3 : Module.finrank K (AdjoinRoot h) = h.natDegree :=
        (AdjoinRoot.powerBasis hm.ne_zero).finrank
      have h4 : h.natDegree = h'.natDegree + 1 := by
        rw [h_def, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero hm'.ne_zero,
          Polynomial.natDegree_X_sub_C, add_comm]
      omega
    rw [hscalar, LinearMap.det_smul, LinearMap.det_id, mul_one, hfr_W, pow_one]
  · -- det(quotient map) = norm K (mk h' g)
    let φ := π.toLinearMap.quotKerEquivOfSurjective hπ_surj
    -- Show mapQ = φ⁻¹ ∘ lmul ∘ φ by quotient induction
    have hmapQ : W.mapQ W e he =
        φ.symm.toLinearMap ∘ₗ (Algebra.lmul K (AdjoinRoot h') (AdjoinRoot.mk h' g)) ∘ₗ
          φ.toLinearMap := by
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W q
      simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, Algebra.coe_lmul_eq_mul]
      change Submodule.Quotient.mk (e x) =
        φ.symm ((LinearMap.mul K (AdjoinRoot h') ((AdjoinRoot.mk h') g))
          (φ (Submodule.Quotient.mk x)))
      rw [LinearEquiv.eq_symm_apply]
      simp only [φ, LinearMap.quotKerEquivOfSurjective_apply_mk, AlgHom.toLinearMap_apply,
        e, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', map_mul, hπ_mk]
    rw [hmapQ]
    exact LinearMap.det_conj _ φ.symm

open Polynomial AdjoinRoot Algebra in
private lemma norm_eq_prod_eval_of_monic_splits {K : Type*} [Field K]
    (s : Multiset K) (g : Polynomial K) :
    Algebra.norm K (AdjoinRoot.mk ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod) g) =
    (s.map (Polynomial.eval · g)).prod := by
  induction s using Multiset.induction with
  | empty =>
    have heq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (0 : Multiset K)).prod = (1 : Polynomial K) := by
      rw [Multiset.map_zero, Multiset.prod_zero]
    rw [heq, Multiset.map_zero, Multiset.prod_zero]
    haveI : Subsingleton (AdjoinRoot (1 : Polynomial K)) := by
      rw [show (1 : Polynomial K) = Polynomial.C 1 from Polynomial.C_1.symm,
        AdjoinRoot, Ideal.span_singleton_eq_top.mpr (isUnit_C.mpr isUnit_one)]
      infer_instance
    rw [show mk (1 : Polynomial K) g = 1 from Subsingleton.elim _ _, map_one]
  | cons a s ih =>
    have hm' : ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod).Monic :=
      monic_multiset_prod_of_monic s _ (fun a _ => monic_X_sub_C a)
    have heq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (a ::ₘ s)).prod =
        (Polynomial.X - Polynomial.C a) *
          (s.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [heq, norm_mk_mul_X_sub_C a _ g hm', ih, Multiset.map_cons, Multiset.prod_cons]

end NormResultant

/-- The algebra norm on `AdjoinRoot h` commutes with ring maps, for monic `h`.
The proof shows that the left multiplication matrix entries (coefficients of `g * X^j %ₘ h`)
commute with ring maps via `map_modByMonic`. -/
private lemma norm_adjoinRoot_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (h g : Polynomial R) (hm : h.Monic) :
    φ (Algebra.norm R (AdjoinRoot.mk h g)) =
    Algebra.norm S (AdjoinRoot.mk (h.map φ) (g.map φ)) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  have hnd : (h.map φ).natDegree = h.natDegree := hm.natDegree_map φ
  rw [Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasis' hm).basis, RingHom.map_det]
  conv_rhs =>
    rw [Algebra.norm_eq_matrix_det ((AdjoinRoot.powerBasis' (hm.map φ)).basis.reindex
      (finCongr hnd))]
  congr 1; ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply, finCongr_symm]
  simp only [(AdjoinRoot.powerBasis' hm).basis_eq_pow,
    (AdjoinRoot.powerBasis' (hm.map φ)).basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  -- Reduce repr to modByMonicHom coeff
  change φ ((AdjoinRoot.powerBasisAux' hm).repr _ _) =
    (AdjoinRoot.powerBasisAux' (hm.map φ)).repr _ _
  simp only [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  -- Simplify mk * root^j using root = mk X
  simp only [AdjoinRoot.root, ← map_pow (AdjoinRoot.mk h), ← map_mul (AdjoinRoot.mk h),
    ← map_pow (AdjoinRoot.mk (h.map φ)), ← map_mul (AdjoinRoot.mk (h.map φ))]
  simp only [AdjoinRoot.modByMonicHom_mk]
  rw [← Polynomial.coeff_map φ, Polynomial.map_modByMonic _ hm,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  simp only [finCongr_apply, Fin.val_cast]

/-- **Norm–resultant identity for monic polynomials** (Thesis Lemma 5.1).

For `h` monic of degree `m` over a commutative ring `R`, the algebra norm of `ḡ` in
`R[z]/(h)` equals `Res(h, g)`.

The proof uses a universal coefficient approach: reduce to the case where the base ring
is a field and `h` splits into linear factors (via `induction_of_Splits`), then use
`resultant_eq_prod_eval` and the norm decomposition for products of linear factors. -/
theorem norm_eq_resultant_monic
    (R : Type*) [CommRing R]
    (h g : Polynomial R) (hm : h.Monic) :
    Algebra.norm R (AdjoinRoot.mk h g) = Polynomial.resultant h g := by
  revert hm g
  induction h using Polynomial.induction_of_Splits_of_injective_of_surjective with
  | Splits K h hh =>
    intro g hm
    -- Both sides equal (h.roots.map g.eval).prod
    have hres : Polynomial.resultant h g = (h.roots.map g.eval).prod := by
      have := Polynomial.resultant_eq_prod_eval h g g.natDegree le_rfl hh
      rwa [hm.leadingCoeff, one_pow, one_mul] at this
    rw [hres]
    conv_lhs => rw [hh.eq_prod_roots_of_monic hm]
    exact norm_eq_prod_eval_of_monic_splits h.roots g
  | injective R' S' φ hφ h IH =>
    intro g hm
    have := IH (g.map φ) (hm.map φ)
    rw [Polynomial.resultant_map_map,
      Polynomial.natDegree_map_eq_of_injective hφ h,
      Polynomial.natDegree_map_eq_of_injective hφ g,
      ← norm_adjoinRoot_map φ h g hm] at this
    exact hφ this
  | surjective R' S' φ hφ h IH =>
    intro g hm
    obtain ⟨h', hh', ndh, hh'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.map_surjective φ hφ h) hm
    obtain ⟨g', hg', eg⟩ := Polynomial.mem_lifts_and_degree_eq
      (Polynomial.map_surjective φ hφ g)
    have hndh : (Polynomial.map φ h').natDegree = h'.natDegree :=
      (congr_arg Polynomial.natDegree hh').trans ndh.symm
    have hndg : (Polynomial.map φ g').natDegree = g'.natDegree :=
      (congr_arg Polynomial.natDegree hg').trans (Polynomial.natDegree_eq_natDegree eg).symm
    rw [← hg', ← hh', Polynomial.resultant_map_map,
      ← norm_adjoinRoot_map φ h' g' hh'm, hndh, hndg]
    exact congrArg φ (IH h' g' hh'm)

/-- **Norm identity for elimination ideals** (Thesis Corollary 5.2).

For `h` monic of degree `m`, if a constant `P ∈ R` belongs to the ideal `⟨h, g⟩`
(i.e., `C(P) = h·a + g·b` for some `a, b`), then
`P^m = Res(h,g) · N(b̄)` where `N` is the algebra norm on `R[z]/(h)`.

This replaces the false claim that `Res(h,g) | P`. The `m`-th power relationship
suffices for the order additivity argument in the codim case of the lifting theorem. -/
theorem norm_identity_elim
    (R : Type*) [CommRing R]
    (h g : Polynomial R) (hm : h.Monic)
    (P : R) (hP_mem : Polynomial.C P ∈ Ideal.span ({h, g} : Set (Polynomial R))) :
    ∃ Q : R, P ^ h.natDegree = Polynomial.resultant h g * Q := by
  rw [Ideal.mem_span_pair] at hP_mem
  obtain ⟨a, b, hab⟩ := hP_mem
  have key : AdjoinRoot.mk h g * AdjoinRoot.mk h b = algebraMap R (AdjoinRoot h) P := by
    change _ = AdjoinRoot.mk h (Polynomial.C P)
    have := congr_arg (AdjoinRoot.mk h) hab
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, mul_comm] at this
    exact this
  have hnorm := congr_arg (Algebra.norm R) key
  rw [map_mul, norm_eq_resultant_monic R h g hm,
    Algebra.norm_algebraMap_of_basis (AdjoinRoot.powerBasis' hm).basis] at hnorm
  simp only [Fintype.card_fin, AdjoinRoot.powerBasis'_dim] at hnorm
  exact ⟨Algebra.norm R (AdjoinRoot.mk h b), hnorm.symm⟩


/-! ### Complexification of real-analytic functions

Following Thesis §3.3.1: extend real-analytic functions from `ℝˢ` to holomorphic
functions on `ℂˢ`, and transfer order-invariance.

The key results are:
1. `analyticAt_complexify`: a real-analytic function extends to a holomorphic function
2. `holomorphic_eq_zero_of_real_eq_zero`: identity theorem — holomorphic on `ℂˢ`,
   zero on `ℝˢ` implies zero everywhere
3. `complexify_order_eq`: orders match between real and complex
4. `complexify_order_invariant`: constant order on `ℝˢ` implies constant order on `ℂˢ`
-/

section Complexification

open scoped Topology
open Filter

/-- A ℂ-multilinear map on `Fin s → ℂ` that vanishes on all tuples of standard basis
vectors is zero. This generalizes `continuousMultilinearMap_eq_zero_iff_basis` to ℂ. -/
lemma cml_eq_zero_of_basis_eq_zero {s k : ℕ}
    (g : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin s → ℂ) ℂ)
    (h : ∀ v : Fin k → Fin s, g (fun i => Pi.single (v i) 1) = 0) : g = 0 := by
  ext x
  simp only [ContinuousMultilinearMap.zero_apply]
  have hx : ∀ i : Fin k,
      x i = ∑ j : Fin s, (x i j) • (Pi.single j (1 : ℂ) : Fin s → ℂ) := by
    intro i; funext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
               mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have heq : x = fun i => ∑ j : Fin s, (x i j) • (Pi.single j (1 : ℂ) : Fin s → ℂ) :=
    funext hx
  rw [heq, show (g fun i => ∑ j : Fin s, x i j • (Pi.single j (1 : ℂ) : Fin s → ℂ)) =
      ∑ v : Fin k → Fin s, g (fun i => x i (v i) • (Pi.single (v i) (1 : ℂ) : Fin s → ℂ)) from
    g.toMultilinearMap.map_sum (fun i j => x i j • (Pi.single j (1 : ℂ) : Fin s → ℂ))]
  apply Finset.sum_eq_zero
  intro v _
  rw [g.map_smul_univ]
  simp [h v]

/-- The real embedding `ι : ℝˢ → ℂˢ` as a continuous ℝ-linear map. -/
noncomputable def realEmbedding (s : ℕ) :
    (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) :=
  ContinuousLinearMap.pi (fun j =>
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj j))

@[simp]
lemma realEmbedding_apply {s : ℕ} (x : Fin s → ℝ) :
    realEmbedding s x = Complex.ofReal ∘ x := by
  ext j; simp [realEmbedding]

/-- Standard basis vectors are in the image of the real embedding. -/
lemma realEmbedding_single {s : ℕ} (j : Fin s) :
    realEmbedding s (Pi.single j 1) = Pi.single j (1 : ℂ) := by
  ext i; simp [realEmbedding, Pi.single_apply, apply_ite]

/-- **Identity theorem on ℝˢ ⊂ ℂˢ** (Thesis §3.3.1).

If `g : ℂˢ → ℂ` is holomorphic at `z₀ = ofReal ∘ x₀` and vanishes on `ℝˢ` near `x₀`,
then `g` has infinite vanishing order at `z₀` (i.e., all iteratedFDeriv vanish).

The proof shows each `iteratedFDeriv ℂ k g z₀` is a ℂ-multilinear map that
vanishes on real basis inputs (via the chain rule for `g ∘ ι`), hence is zero. -/
lemma order_eq_top_of_real_eq_zero {s : ℕ}
    (g : (Fin s → ℂ) → ℂ) (x₀ : Fin s → ℝ)
    (hg : AnalyticAt ℂ g (Complex.ofReal ∘ x₀))
    (hgz : ∀ᶠ x in 𝓝 x₀, g (Complex.ofReal ∘ x) = 0) :
    order ℂ g (Complex.ofReal ∘ x₀) = ⊤ := by
  rw [order_eq_top_iff]
  intro k
  set z₀ := Complex.ofReal ∘ x₀
  let ι : (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) := realEmbedding s
  have hι_eq : ⇑ι = fun x => Complex.ofReal ∘ x := funext realEmbedding_apply
  have hι_x₀ : ι x₀ = z₀ := by rw [hι_eq]
  -- Step 1: g ∘ ι = 0 near x₀, so all ℝ-iterated derivatives vanish
  have hgι_zero : (g ∘ ⇑ι) =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hgz] with x hx
    simp only [Function.comp_apply, hι_eq, hx, Pi.zero_apply]
  have hgι_deriv : iteratedFDeriv ℝ k (g ∘ ⇑ι) x₀ = 0 := by
    have h := (hgι_zero.iteratedFDeriv ℝ k).self_of_nhds
    rw [h]
    rcases k with _ | k
    · ext m; simp [iteratedFDeriv_zero_apply]
    · exact congr_fun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k) (0 : ℂ)) x₀
  -- Step 2: Local chain rule via open ball where g is smooth
  obtain ⟨p, r, hp⟩ := hg
  set U := Metric.eball z₀ r with hU_def
  have hU_open : IsOpen U := Metric.isOpen_eball
  have hz₀U : z₀ ∈ U := Metric.mem_eball_self hp.r_pos
  have hg_smooth : ContDiffOn ℝ ⊤ g U :=
    hp.analyticOnNhd.contDiffOn_of_completeSpace |>.restrict_scalars ℝ
  have hιU_open : IsOpen (ι ⁻¹' U) := hU_open.preimage ι.continuous
  have hx₀_ιU : x₀ ∈ ι ⁻¹' U := show ι x₀ ∈ U from hι_x₀ ▸ hz₀U
  have hchain_within : iteratedFDerivWithin ℝ k (g ∘ ⇑ι) (ι ⁻¹' U) x₀ =
      (iteratedFDerivWithin ℝ k g U z₀).compContinuousLinearMap (fun _ => ι) :=
    ι.iteratedFDerivWithin_comp_right (hg_smooth.of_le le_top)
      hU_open.uniqueDiffOn hιU_open.uniqueDiffOn (hι_x₀ ▸ hz₀U) le_top
  rw [iteratedFDerivWithin_of_isOpen k hιU_open hx₀_ιU,
      iteratedFDerivWithin_of_isOpen k hU_open hz₀U] at hchain_within
  -- Step 3: Connect ℝ and ℂ derivatives via restrictScalars
  have hcd : ContDiffAt ℂ (↑k) g z₀ :=
    hp.hasFPowerSeriesAt.analyticAt.contDiffAt.of_le le_top
  have hrestr : (iteratedFDeriv ℂ k g z₀).restrictScalars ℝ = iteratedFDeriv ℝ k g z₀ :=
    ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) hcd
  -- Step 4: iteratedFDeriv ℂ k g z₀ vanishes on all real inputs
  have hvanish : ∀ w : Fin k → (Fin s → ℝ),
      (iteratedFDeriv ℂ k g z₀) (fun i => ι (w i)) = 0 := by
    intro w
    have h1 : ((iteratedFDeriv ℂ k g z₀).restrictScalars ℝ).compContinuousLinearMap
        (fun _ => ι) = 0 := by
      rw [hrestr, ← hchain_within]; exact hgι_deriv
    have h2 := DFunLike.congr_fun h1 w
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.coe_restrictScalars,
      ContinuousMultilinearMap.zero_apply] at h2
    exact h2
  -- Step 5: Basis argument — vanishing on basis vectors implies zero
  apply cml_eq_zero_of_basis_eq_zero
  intro v
  rw [show (fun i => Pi.single (v i) (1 : ℂ)) =
      (fun i => ι (Pi.single (v i) (1 : ℝ))) from
    funext fun i => (realEmbedding_single (v i)).symm]
  exact hvanish _

/-- Complexify a continuous multilinear map from `(Fin s → ℝ)^n → ℝ` to
`(Fin s → ℂ)^n → ℂ` by expanding in the standard basis. -/
private noncomputable def complexifyMultilinear {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin s → ℂ) ℂ :=
  ∑ σ : Fin n → Fin s,
    Complex.ofReal (T (fun j => Pi.single (σ j) 1)) •
    (ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (1 : ℂ)).compContinuousLinearMap
      (fun j => ContinuousLinearMap.proj (σ j))

private lemma complexifyMultilinear_apply {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ)
    (v : (i : Fin n) → Fin s → ℂ) :
    complexifyMultilinear T v =
      ∑ σ : Fin n → Fin s,
        Complex.ofReal (T (fun j => Pi.single (σ j) 1)) * ∏ j : Fin n, v j (σ j) := by
  unfold complexifyMultilinear
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mul_one]

private lemma complexifyMultilinear_real {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ)
    (x : (i : Fin n) → Fin s → ℝ) :
    complexifyMultilinear T (fun i => Complex.ofReal ∘ x i) =
      Complex.ofReal (T x) := by
  rw [complexifyMultilinear_apply]
  simp only [Function.comp_apply]
  simp_rw [← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  have hx : x = fun i => ∑ j : Fin s, x i j • (Pi.single j (1 : ℝ) : Fin s → ℝ) := by
    ext i k; simp [Pi.single_apply]
  conv_rhs => rw [hx, T.map_sum]
  simp_rw [T.map_smul_univ, smul_eq_mul]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

private lemma complexifyMultilinear_norm_le {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ) :
    ‖complexifyMultilinear T‖ ≤ (s : ℝ) ^ n * ‖T‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v; rw [complexifyMultilinear_apply]
  have hterm : ∀ σ : Fin n → Fin s,
      ‖Complex.ofReal (T (fun j => Pi.single (σ j) 1)) * ∏ j, v j (σ j)‖ ≤
      ‖T‖ * ∏ j, ‖v j‖ := by
    intro σ
    have h1 : ‖Complex.ofReal (T (fun j => Pi.single (σ j) 1))‖ ≤ ‖T‖ := by
      rw [Complex.norm_real]
      exact (T.le_opNorm _).trans_eq (by simp [Pi.norm_single])
    have h2 : ‖∏ j : Fin n, v j (σ j)‖ ≤ ∏ j, ‖v j‖ :=
      (Finset.norm_prod_le Finset.univ (fun j => v j (σ j))).trans (Finset.prod_le_prod
        (fun j _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (v j) (σ j)))
    exact (norm_mul_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _))
  calc ‖∑ σ : Fin n → Fin s, Complex.ofReal (T (fun j => Pi.single (σ j) 1)) *
          ∏ j, v j (σ j)‖
      ≤ ∑ σ : Fin n → Fin s, ‖Complex.ofReal (T (fun j => Pi.single (σ j) 1)) *
          ∏ j, v j (σ j)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin n → Fin s, ‖T‖ * ∏ j, ‖v j‖ :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (s : ℝ) ^ n * ‖T‖ * ∏ j, ‖v j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        simp only [Fintype.card_fin, Nat.cast_pow]; ring

/-- Complexified formal multilinear series. -/
private noncomputable def complexifyFMS {s : ℕ}
    (p : FormalMultilinearSeries ℝ (Fin s → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (Fin s → ℂ) ℂ :=
  fun n => complexifyMultilinear (p n)

private lemma complexifyFMS_radius_pos {s : ℕ}
    (p : FormalMultilinearSeries ℝ (Fin s → ℝ) ℝ) (hp : 0 < p.radius) :
    0 < (complexifyFMS p).radius := by
  obtain ⟨r, hr_pos, hr_lt⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (ENNReal.natCast_ne_top s) (ne_of_gt hp)
  set R : NNReal := (s : NNReal) * r
  have hR_lt : (↑R : ENNReal) < p.radius := by
    show ↑((s : NNReal) * r) < p.radius; rwa [ENNReal.coe_mul, mul_comm]
  have hsumm := p.summable_norm_mul_pow hR_lt
  have hR_eq : (R : ℝ) = ↑s * ↑r := by
    simp only [R, NNReal.coe_mul, NNReal.coe_natCast]
  have hle : (↑r : ENNReal) ≤ (complexifyFMS p).radius :=
    (complexifyFMS p).le_radius_of_summable <|
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun n => by
          calc ‖complexifyFMS p n‖ * (↑r : ℝ) ^ n
              ≤ ((↑s : ℝ) ^ n * ‖p n‖) * (↑r : ℝ) ^ n := by
                gcongr; exact complexifyMultilinear_norm_le (p n)
            _ = ‖p n‖ * (R : ℝ) ^ n := by rw [hR_eq]; ring)
        hsumm
  exact lt_of_lt_of_le (by exact_mod_cast hr_pos) hle

/-- A real-analytic function at a point has a holomorphic (ℂ-analytic) extension
to `Fin s → ℂ` near the corresponding complex point, with matching vanishing order.

The extension is defined by the same convergent power series with complex variables
substituted (Thesis Theorem 2.1.2). The order equality follows from the
identity theorem on `ℝˢ ⊂ ℂˢ`. -/
private lemma complexifyMultilinear_eq_zero_iff {n s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin s → ℝ) ℝ) :
    complexifyMultilinear T = 0 ↔ T = 0 := by
  constructor
  · intro h
    ext x
    have h1 := DFunLike.congr_fun h (fun i => Complex.ofReal ∘ x i)
    simp only [ContinuousMultilinearMap.zero_apply] at h1
    rw [complexifyMultilinear_real] at h1
    exact_mod_cast h1
  · intro h; subst h
    ext v; simp [complexifyMultilinear_apply]

/-- **L1 — real restriction of the order.** For a complex-analytic `f_ℂ` whose real restriction is
`f` (`f_ℂ(ℝ x) = ℝ(f x)` near `x₀`, real-analytic `f`), McCallum's order agrees on the real point:
`ord_ℂ f_ℂ (ℝ x₀) = ord_ℝ f x₀`. The real Taylor coefficients of `f` are the complex ones of `f_ℂ`
(chain rule with the `ℝ`-linear embedding `ι = realEmbedding`), and a complex multilinear form
vanishes iff it vanishes on real arguments (real points are determining). This is the transport that
turns the complex Zariski order-invariance into the real one. -/
theorem order_real_eq_order_complex {s : ℕ}
    (f : (Fin s → ℝ) → ℝ) (f_ℂ : (Fin s → ℂ) → ℂ) (x₀ : Fin s → ℝ)
    (hf : AnalyticAt ℝ f x₀)
    (hf_ℂ : AnalyticAt ℂ f_ℂ (Complex.ofReal ∘ x₀))
    (hagree : ∀ᶠ x in 𝓝 x₀, f_ℂ (Complex.ofReal ∘ x) = Complex.ofReal (f x)) :
    order ℂ f_ℂ (Complex.ofReal ∘ x₀) = order ℝ f x₀ := by
  set z₀ := Complex.ofReal ∘ x₀ with hz₀def
  let ι : (Fin s → ℝ) →L[ℝ] (Fin s → ℂ) := realEmbedding s
  have hι_eq : ⇑ι = fun x => Complex.ofReal ∘ x := funext realEmbedding_apply
  have hι_x₀ : ι x₀ = z₀ := by rw [hι_eq]
  obtain ⟨r, hr, hf_ℂ_on⟩ := hf_ℂ.exists_ball_analyticOnNhd
  set U := Metric.ball z₀ r with hU_def
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hz₀U : z₀ ∈ U := Metric.mem_ball_self hr
  have hf_ℂ_smooth : ContDiffOn ℝ ⊤ f_ℂ U :=
    hf_ℂ_on.contDiffOn_of_completeSpace |>.restrict_scalars ℝ
  have hf_cd : ContDiffAt ℝ ⊤ f x₀ := hf.contDiffAt
  have hιU_open : IsOpen (ι ⁻¹' U) := hU_open.preimage ι.continuous
  have hx₀_ιU : x₀ ∈ ι ⁻¹' U := show ι x₀ ∈ U from hι_x₀ ▸ hz₀U
  have hfeq : (f_ℂ ∘ ⇑ι) =ᶠ[𝓝 x₀] (Complex.ofRealCLM ∘ f) := by
    filter_upwards [hagree] with x hx
    show f_ℂ (ι x) = Complex.ofRealCLM (f x)
    rw [show (ι x : Fin s → ℂ) = Complex.ofReal ∘ x from congr_fun hι_eq x]
    exact hx
  have hchain_eq : ∀ n : ℕ, iteratedFDeriv ℝ n (f_ℂ ∘ ⇑ι) x₀ =
      ((iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ).compContinuousLinearMap
        (fun _ => ι) := by
    intro n
    have h1 : iteratedFDerivWithin ℝ n (f_ℂ ∘ ⇑ι) (ι ⁻¹' U) x₀ =
        (iteratedFDerivWithin ℝ n f_ℂ U z₀).compContinuousLinearMap (fun _ => ι) :=
      ι.iteratedFDerivWithin_comp_right (hf_ℂ_smooth.of_le le_top)
        hU_open.uniqueDiffOn hιU_open.uniqueDiffOn (hι_x₀ ▸ hz₀U) le_top
    rw [iteratedFDerivWithin_of_isOpen n hιU_open hx₀_ιU,
        iteratedFDerivWithin_of_isOpen n hU_open hz₀U] at h1
    have hcd : ContDiffAt ℂ (↑n) f_ℂ z₀ := hf_ℂ.contDiffAt.of_le le_top
    have hrestr : (iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ =
        iteratedFDeriv ℝ n f_ℂ z₀ :=
      ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) hcd
    rw [h1, hrestr]
  have hleft_eq : ∀ n : ℕ, iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) x₀ =
      Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x₀) :=
    fun n => Complex.ofRealCLM.iteratedFDeriv_comp_left (hf_cd.of_le le_top) le_top
  suffices h_zero_iff : ∀ n : ℕ, iteratedFDeriv ℂ n f_ℂ z₀ = 0 ↔
      iteratedFDeriv ℝ n f x₀ = 0 by
    simp only [order]
    have h_ne : ∀ n : ℕ, iteratedFDeriv ℂ n f_ℂ z₀ ≠ 0 ↔
        iteratedFDeriv ℝ n f x₀ ≠ 0 := fun n => (h_zero_iff n).not
    by_cases hex : ∃ n, iteratedFDeriv ℝ n f x₀ ≠ 0
    · have hex_c := (exists_congr fun n => h_ne n).mpr hex
      rw [dif_pos hex_c, dif_pos hex]
      exact congr_arg _ (Nat.find_congr' (fun {n} => h_ne n))
    · have : ¬ ∃ n, iteratedFDeriv ℂ n f_ℂ z₀ ≠ 0 :=
        fun h => hex ((exists_congr fun n => h_ne n).mp h)
      rw [dif_neg this, dif_neg hex]
  intro n
  constructor
  · intro hc
    have h_comp_zero : iteratedFDeriv ℝ n (f_ℂ ∘ ⇑ι) x₀ = 0 := by
      rw [hchain_eq n, hc]; ext; simp
    have h_feq_deriv := (hfeq.iteratedFDeriv ℝ n).self_of_nhds
    rw [h_comp_zero, hleft_eq] at h_feq_deriv
    ext v
    have hv := DFunLike.congr_fun h_feq_deriv.symm v
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.zero_apply] at hv
    exact Complex.ofReal_eq_zero.mp hv
  · intro hr_
    have h_left_zero : iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) x₀ = 0 := by
      rw [hleft_eq, hr_]; ext; simp
    have h_feq_deriv := (hfeq.iteratedFDeriv ℝ n).self_of_nhds
    rw [h_left_zero] at h_feq_deriv
    have h_vanish : ((iteratedFDeriv ℂ n f_ℂ z₀).restrictScalars ℝ).compContinuousLinearMap
        (fun _ => ι) = 0 := by rw [← hchain_eq]; exact h_feq_deriv
    apply cml_eq_zero_of_basis_eq_zero
    intro v
    rw [show (fun i => Pi.single (v i) (1 : ℂ)) = (fun i => ι (Pi.single (v i) (1 : ℝ))) from
      funext fun i => (realEmbedding_single (v i)).symm]
    have h2 := DFunLike.congr_fun h_vanish (fun i => Pi.single (v i) (1 : ℝ))
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.coe_restrictScalars,
      ContinuousMultilinearMap.zero_apply] at h2
    exact h2

theorem analyticAt_complexify {s : ℕ}
    (f : (Fin s → ℝ) → ℝ) (x₀ : Fin s → ℝ)
    (hf : AnalyticAt ℝ f x₀) :
    ∃ f_ℂ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ f_ℂ (Complex.ofReal ∘ x₀) ∧
      (∀ᶠ x in 𝓝 x₀, f_ℂ (Complex.ofReal ∘ x) = Complex.ofReal (f x)) ∧
      order ℂ f_ℂ (Complex.ofReal ∘ x₀) = order ℝ f x₀ := by
  obtain ⟨p, r, hball⟩ := hf
  set q := complexifyFMS p
  set z₀ := Complex.ofReal ∘ x₀
  have hq_rad : 0 < q.radius := complexifyFMS_radius_pos p hball.radius_pos
  have hq_ball : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall hq_rad
  set f_ℂ := fun z : Fin s → ℂ => q.sum (z - z₀)
  have hf_ℂ_ball : HasFPowerSeriesOnBall f_ℂ q z₀ q.radius := {
    r_le := le_rfl
    r_pos := hq_rad
    hasSum := fun {y} hy => by
      have h := hq_ball.hasSum hy
      rw [zero_add] at h
      change HasSum _ (q.sum ((z₀ + y) - z₀))
      rw [add_sub_cancel_left]
      exact h }
  -- Agreement on reals helper
  have hagree : ∀ᶠ x in 𝓝 x₀, f_ℂ (Complex.ofReal ∘ x) = Complex.ofReal (f x) := by
    filter_upwards [Metric.eball_mem_nhds x₀ (lt_min hball.r_pos hq_rad)] with x hx
    set y := x - x₀
    have hy_e : edist y 0 < min r q.radius := by
      show edist (x - x₀) 0 < _
      rw [edist_dist, dist_zero_right, ← dist_eq_norm, ← edist_dist]
      exact Metric.mem_eball.mp hx
    have hy_r : y ∈ Metric.eball (0 : Fin s → ℝ) r :=
      Metric.mem_eball.mpr (lt_of_lt_of_le hy_e (min_le_left _ _))
    have h_edist : edist (Complex.ofReal ∘ y : Fin s → ℂ) (0 : Fin s → ℂ) =
        edist y (0 : Fin s → ℝ) := by
      simp only [edist_pi_def, Function.comp_apply, Pi.zero_apply, ← Complex.ofReal_zero,
        Complex.isometry_ofReal.edist_eq]
    have hy_q : (Complex.ofReal ∘ y : Fin s → ℂ) ∈ Metric.eball (0 : Fin s → ℂ) q.radius :=
      Metric.mem_eball.mpr (h_edist ▸ lt_of_lt_of_le hy_e (min_le_right _ _))
    have h_cplx := hf_ℂ_ball.hasSum hy_q
    have h_rw : ∀ n, q n (fun _ => Complex.ofReal ∘ y) =
        Complex.ofReal (p n (fun _ => y)) := fun n =>
      complexifyMultilinear_real (p n) (fun _ => y)
    simp_rw [h_rw] at h_cplx
    have h_eq := h_cplx.unique (Complex.ofRealCLM.hasSum (hball.hasSum hy_r))
    rwa [show z₀ + Complex.ofReal ∘ y = Complex.ofReal ∘ x from by
           ext i; simp only [z₀, y, Pi.add_apply, Function.comp_apply, Pi.sub_apply]; push_cast; ring,
         show x₀ + y = x from by ext; simp [y]] at h_eq
  exact ⟨f_ℂ, ⟨q, q.radius, hf_ℂ_ball⟩, hagree,
    order_real_eq_order_complex f f_ℂ x₀ hball.analyticAt ⟨q, q.radius, hf_ℂ_ball⟩ hagree⟩
/-- **Schwarz reflection / real restriction** (decomposition step 6, now PROVED).

A function `ψ` holomorphic at a real point `realEmbedding s x₀` restricts to a real-analytic
function on `ℝˢ`: `x ↦ Re (ψ (ofReal ∘ x))` is real-analytic at `x₀`. When `ψ` is a holomorphic
root section taking real values on the real slice, this is exactly the real root function.

This is the real-analyticity half of recovering real root sections from holomorphic ones in the
complexification approach to the delineation axiom. Proof: `ψ` is ℂ-analytic hence ℝ-analytic
(`restrictScalars`); precompose with the ℝ-linear embedding and postcompose with `Re`, both
continuous-linear hence analytic. -/
theorem real_restriction_analytic {s : ℕ}
    (ψ : (Fin s → ℂ) → ℂ) (x₀ : Fin s → ℝ)
    (hψ : AnalyticAt ℂ ψ (realEmbedding s x₀)) :
    AnalyticAt ℝ (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) x₀ := by
  have h1 : AnalyticAt ℝ ψ (realEmbedding s x₀) := hψ.restrictScalars
  have h2 : AnalyticAt ℝ (fun x => ψ (realEmbedding s x)) x₀ :=
    h1.comp ((realEmbedding s).analyticAt x₀)
  exact (Complex.reCLM.analyticAt _).comp h2

/-- **Phase F1 (Schwarz real recovery).** A holomorphic section `ψ` that is **real-valued on the
real slice** near `x₀` restricts to a real-analytic `η := Re ∘ ψ ∘ realEmbedding`, and `ψ` is
recovered from `η` on the real slice: `(η x : ℂ) = ψ (realEmbedding s x)` for `x` near `x₀`.

This packages `real_restriction_analytic` (the Schwarz-reflection content) with the trivial
"real part recovers the value" fact, giving F3 exactly the real root functions plus the bridge that
turns the complex Zariski factorization into a statement about the real roots of `g(·,0)`. -/
theorem real_section_of_real_valued {s : ℕ}
    (ψ : (Fin s → ℂ) → ℂ) (x₀ : Fin s → ℝ)
    (hψ : AnalyticAt ℂ ψ (realEmbedding s x₀))
    (hreal : ∀ᶠ x in 𝓝 x₀, (ψ (realEmbedding s x)).im = 0) :
    AnalyticAt ℝ (fun x : Fin s → ℝ => (ψ (realEmbedding s x)).re) x₀ ∧
    (∀ᶠ x in 𝓝 x₀,
      ((ψ (realEmbedding s x)).re : ℂ) = ψ (realEmbedding s x)) := by
  refine ⟨real_restriction_analytic ψ x₀ hψ, ?_⟩
  filter_upwards [hreal] with x hx
  have h := Complex.re_add_im (ψ (realEmbedding s x))
  rw [hx] at h
  simpa using h

end Complexification

open scoped Topology
open Filter

/-! ### Axioms for the analytic core (to be proved)

The single axiom `analytic_pseudopoly_delineable` below is the only non-standard
axiom on which the main theorem `mccallum_3_2_3_generalized` depends. We plan to
decompose it into the following smaller pieces, each of which is a well-known
classical theorem of complex analysis:

**Decomposition plan:**

1. **`weierstrass_preparation_complex`** (TODO axiom) — classical Weierstrass
   preparation theorem for holomorphic functions in several complex variables.
   A holomorphic `f` on `Δ × Δ(0, R)` with `f(0, ·)` having a zero of order
   exactly `m` at `0` factors as `f = u · h` where `u` is a unit and
   `h(z, w) = w^m + a₁(z) w^{m-1} + ... + a_m(z)` is a "Weierstrass polynomial"
   with `aᵢ(0) = 0`. **Status:** Mathlib has the algebraic version
   (`PowerSeries.exists_isWeierstrassFactorization`) for formal power series
   over complete local rings. Bridging to convergent power series is the gap.

2. **`zariski_root_sections_complex`** (TODO axiom) — Zariski's 1975 theorem.
   For a Weierstrass polynomial `h(z, w)` with `disc(h)` of constant nonzero
   vanishing order on a connected open set in `ℂˢ`, `h` has holomorphic root
   sections `ψᵢ : Δ → ℂ` with constant multiplicities. **Status:** not in
   Mathlib; classical reference is Zariski's "Studies in equisingularity I"
   (1965) or Tougeron, *Idéaux de fonctions différentiables*.

3. **`real_root_section_of_complex`** (theorem, provable) — Schwarz reflection.
   If `ψ : Δ → ℂ` is holomorphic, takes real values on `Δ ∩ ℝˢ`, then its
   restriction to `Δ ∩ ℝˢ` is real-analytic with real-valued power series.

4. **`analytic_pseudopoly_delineable`** (theorem, provable from 1–3) — the
   real-analytic delineation result currently stated as an axiom.

For now, we state the monolithic axiom below; the decomposition is documented
here as the path toward a fully-axiom-free proof.
-/

end
