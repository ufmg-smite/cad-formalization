import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Connected.Clopen
import Cad.Multivariate.ProjectionTheorem.Delineability
import Cad.Multivariate.ProjectionTheorem.Invariance
import Cad.Multivariate.ProjectionTheorem.Submanifold

/-!
# Prerequisites for Theorem 3.2.3

The axioms representing results from McCallum's thesis that we use as black boxes
(Theorem 3.2.1 "Lifting", Theorem 2.3.3 + Lemma 3.2.2, etc.), together with the
helper lemmas that are proved in Lean.

We state the product-based axioms using `Finset` products `∏ f ∈ A, f` directly
(rather than indexed families `∏ i : Fin m, F i`) to avoid conversion overhead.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- Product of squarefree pairwise coprime polynomials is squarefree. -/
theorem prod_squarefree_of_coprime
    (A : Finset (PolyR n))
    (hsf : ∀ f ∈ A, Squarefree f)
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g) :
    Squarefree (∏ f ∈ A, f) := by
  induction A using Finset.induction with
  | empty => simp
  | @insert p A hpA ih =>
    rw [Finset.prod_insert hpA, squarefree_mul_iff]
    refine ⟨?_, hsf p (Finset.mem_insert_self p A), ?_⟩
    · apply IsCoprime.isRelPrime
      apply IsCoprime.prod_right
      intro g hg
      refine hcop p (Finset.mem_insert_self p A) g (Finset.mem_insert_of_mem hg) ?_
      intro heq; rw [heq] at hpA; exact hpA hg
    · exact ih (fun f hf => hsf f (Finset.mem_insert_of_mem hf))
        (fun f hf g hg hne =>
          hcop f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg) hne)

/-! ### Helper lemmas for `delineable_factor_of_delineable_prod` -/

/-- Coprime polynomials have no common root after specialization (local copy to
avoid a circular import; see `no_common_root_of_coprime` in `Projection.lean`). -/
private theorem coprime_no_common_root
    (F G : PolyR n) (hcop : IsCoprime F G) (a : Fin n → ℝ) (y : ℝ) :
    ¬ ((specialize F a).IsRoot y ∧ (specialize G a).IsRoot y) := by
  intro ⟨hF, hG⟩
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : specialize (u * F + v * G) a = 1 := by
    rw [huv]; simp [specialize, Polynomial.map_one]
  have h2 : (specialize (u * F + v * G) a).eval y = 1 := by rw [h1]; simp
  simp only [specialize, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.eval_add, Polynomial.eval_mul] at h2
  rw [Polynomial.IsRoot] at hF hG
  simp only [specialize] at hF hG
  rw [hF, hG] at h2; linarith

/-- Specialization commutes with finite products. -/
private theorem specialize_prod
    (A : Finset (PolyR n)) (a : Fin n → ℝ) :
    specialize (∏ f ∈ A, f) a = ∏ f ∈ A, specialize f a := by
  simp [specialize, Polynomial.map_prod]

/-- Continuity of `a ↦ (specialize F a).eval y(a)` when `y` is continuous on `S`. -/
private theorem continuousOn_specialize_eval
    (F : PolyR n) (y : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ))
    (hy : ContinuousOn y S) :
    ContinuousOn (fun a => (specialize F a).eval (y a)) S := by
  have heq : (fun a => (specialize F a).eval (y a)) =
      (fun a => ∑ i ∈ F.support, MvPolynomial.eval a (F.coeff i) * (y a) ^ i) := by
    ext a
    show ((F.map (evalBase a)).eval (y a)) = _
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [heq]
  apply continuousOn_finset_sum
  intro i _
  exact ((MvPolynomial.continuous_eval _).continuousOn).mul (hy.pow i)

/-- Delineability of product implies delineability of each factor (coprime case).

The proof uses a topological argument: for each root function `θ i` of the product,
the function `a ↦ (specialize F a).eval (θ i a)` is continuous on `S`. By coprimality,
at each `a ∈ S`, `θ i a` is a root of exactly one factor, partitioning `S` into the
finitely many closed sets `{a | θ i a is a root of F}`. By preconnectedness, exactly
one such set equals `S`, so each `θ i` is a root function of a unique factor on all
of `S`. Restricting `θ` and `m` to the indices owned by `F` yields the delineability
witness for `F`. -/
theorem delineable_factor_of_delineable_prod
    (S : Set (Fin n → ℝ))
    (hS_pc : IsPreconnected S)
    (A : Finset (PolyR n))
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g)
    (hprod : AnalyticDelineable (∏ f ∈ A, f) S) :
    ∀ f ∈ A, AnalyticDelineable f S := by
  -- Empty case is trivial
  rcases Set.eq_empty_or_nonempty S with hSem | hS_ne
  · intro F _
    refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro a ha; rw [hSem] at ha; exact absurd ha (Set.notMem_empty a)
    · intro a ha; rw [hSem] at ha; exact absurd ha (Set.notMem_empty a)
    · intro i; exact i.elim0
    · intro a ha; rw [hSem] at ha; exact absurd ha (Set.notMem_empty a)
  -- Main case: unpack hypothesis
  obtain ⟨k, θ, m, hθ_an, hθ_str, hθ_root, hm_pos, hm_mult⟩ := hprod
  obtain ⟨a₀, ha₀⟩ := hS_ne
  -- Each θ i is continuous on S (analytic implies continuous)
  have hθ_cont : ∀ i : Fin k, ContinuousOn (θ i) S :=
    fun i => (hθ_an i).continuousOn
  -- For each i and a ∈ S, θ i a is a root of the product, hence of some factor
  have h_some_factor : ∀ a ∈ S, ∀ i : Fin k,
      ∃ F ∈ A, (specialize F a).eval (θ i a) = 0 := by
    intro a ha i
    have hroot : (specialize (∏ f ∈ A, f) a).IsRoot (θ i a) :=
      (hθ_root a ha (θ i a)).mpr ⟨i, rfl⟩
    rw [Polynomial.IsRoot, specialize_prod, Polynomial.eval_prod] at hroot
    exact Finset.prod_eq_zero_iff.mp hroot
  -- Uniqueness via coprimality
  have h_unique_factor : ∀ a ∈ S, ∀ i : Fin k, ∀ F ∈ A, ∀ G ∈ A,
      (specialize F a).eval (θ i a) = 0 →
      (specialize G a).eval (θ i a) = 0 → F = G := by
    intro a _ i F hF G hG hFR hGR
    by_contra hne
    exact coprime_no_common_root F G (hcop F hF G hG hne) a (θ i a) ⟨hFR, hGR⟩
  -- For each i, the unique owner factor is constant on S (by preconnectedness)
  have h_owner_constant : ∀ i : Fin k, ∃ F ∈ A,
      ∀ a ∈ S, (specialize F a).eval (θ i a) = 0 := by
    intro i
    -- Pick the owner at a₀
    obtain ⟨F₀, hF₀A, hF₀R⟩ := h_some_factor a₀ ha₀ i
    refine ⟨F₀, hF₀A, ?_⟩
    -- Use preconnectedness: T = {a ∈ S | (specialize F₀ a).eval (θ i a) = 0} is clopen, contains a₀
    haveI : PreconnectedSpace S := Subtype.preconnectedSpace hS_pc
    -- Define f : S → ℝ as the evaluation
    let f : S → ℝ := fun a => (specialize F₀ a.val).eval (θ i a.val)
    have hf_cont : Continuous f := by
      have hg : ContinuousOn (fun a => (specialize F₀ a).eval (θ i a)) S :=
        continuousOn_specialize_eval F₀ (θ i) S (hθ_cont i)
      exact hg.comp_continuous continuous_subtype_val (fun a => a.2)
    -- T is the zero set of f
    let T : Set S := {a | f a = 0}
    have hT_closed : IsClosed T := isClosed_eq hf_cont continuous_const
    -- T is open: complement is finite union of closed sets
    have hT_open : IsOpen T := by
      rw [← isClosed_compl_iff]
      have heq : Tᶜ = ⋃ G ∈ A.erase F₀, {a : S | (specialize G a.val).eval (θ i a.val) = 0} := by
        ext ⟨a, ha⟩
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_erase, T, f]
        refine ⟨?_, ?_⟩
        · intro hne
          obtain ⟨G, hGA, hGR⟩ := h_some_factor a ha i
          refine ⟨G, ⟨?_, hGA⟩, hGR⟩
          intro hG_eq; rw [hG_eq] at hGR; exact hne hGR
        · rintro ⟨G, ⟨hGne, hGA⟩, hGR⟩ hF₀eq
          exact hGne (h_unique_factor a ha i G hGA F₀ hF₀A hGR hF₀eq)
      rw [heq]
      apply isClosed_biUnion_finset
      intro G _
      have hG_cont : Continuous (fun a : S => (specialize G a.val).eval (θ i a.val)) := by
        have hg : ContinuousOn (fun a => (specialize G a).eval (θ i a)) S :=
          continuousOn_specialize_eval G (θ i) S (hθ_cont i)
        exact hg.comp_continuous continuous_subtype_val (fun a => a.2)
      exact isClosed_eq hG_cont continuous_const
    -- T is clopen
    have hT_clopen : IsClopen T := ⟨hT_closed, hT_open⟩
    -- T contains ⟨a₀, ha₀⟩, so T = univ
    have ha₀T : (⟨a₀, ha₀⟩ : S) ∈ T := hF₀R
    have hT_univ : T = Set.univ := by
      have : Set.univ ⊆ T :=
        (PreconnectedSpace.isPreconnected_univ).subset_isClopen hT_clopen
          ⟨⟨a₀, ha₀⟩, Set.mem_univ _, ha₀T⟩
      exact Set.eq_univ_of_univ_subset this
    intro a ha
    have : (⟨a, ha⟩ : S) ∈ T := by rw [hT_univ]; trivial
    exact this
  -- Define the owner function (constant on S for each i)
  let owner : Fin k → PolyR n := fun i => (h_owner_constant i).choose
  have h_owner_mem : ∀ i, owner i ∈ A := fun i => (h_owner_constant i).choose_spec.1
  have h_owner_root : ∀ i a, a ∈ S → (specialize (owner i) a).eval (θ i a) = 0 :=
    fun i a ha => (h_owner_constant i).choose_spec.2 a ha
  -- Now construct the delineability witness for each F ∈ A
  intro F hF
  let J : Finset (Fin k) := Finset.univ.filter (fun i => owner i = F)
  let kF := J.card
  let σ : Fin kF ≃o J := J.orderIsoOfFin rfl
  refine ⟨kF, fun i => θ (σ i).val, fun i => m (σ i).val, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Analyticity
    intro i; exact hθ_an _
  · -- 2. Strict order
    intro a ha i j hij
    have h_lt : σ i < σ j := σ.lt_iff_lt.mpr hij
    exact hθ_str a ha (σ i).val (σ j).val h_lt
  · -- 3. Root condition
    intro a ha y
    constructor
    · -- (→) y root of F's specialization → y = θ at some Fin kF index
      intro hyF
      -- y is also a root of the product
      have hyProd : (specialize (∏ g ∈ A, g) a).IsRoot y := by
        rw [Polynomial.IsRoot, specialize_prod, Polynomial.eval_prod]
        exact Finset.prod_eq_zero hF hyF
      -- Get the original index j
      obtain ⟨j, hj⟩ := (hθ_root a ha y).mp hyProd
      -- Show owner j = F
      have hyF' : (specialize F a).eval (θ j a) = 0 := by rw [← hj]; exact hyF
      have h_owner_eq : owner j = F :=
        h_unique_factor a ha j (owner j) (h_owner_mem j) F hF
          (h_owner_root j a ha) hyF'
      have hjJ : j ∈ J := by
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_owner_eq
      -- Convert j ∈ J to a Fin kF index via σ.symm
      refine ⟨σ.symm ⟨j, hjJ⟩, ?_⟩
      have h_eq : (σ (σ.symm ⟨j, hjJ⟩)).val = j := by
        rw [σ.apply_symm_apply]
      show y = θ (σ (σ.symm ⟨j, hjJ⟩)).val a
      rw [h_eq]; exact hj
    · -- (←) y = θ at some Fin kF index → y root of F's specialization
      rintro ⟨i, hyi⟩
      have hi_mem : (σ i).val ∈ J := (σ i).property
      have h_owner_eq : owner (σ i).val = F := by
        have := hi_mem
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      have h_root := h_owner_root (σ i).val a ha
      rw [h_owner_eq] at h_root
      rw [hyi]; exact h_root
  · -- 4. Multiplicity positive
    intro i; exact hm_pos _
  · -- 5. Multiplicity constant
    intro a ha i
    have h_mult := hm_mult a ha (σ i).val
    rw [specialize_prod] at h_mult
    -- Each factor's specialization is nonzero (product mult > 0 implies product nonzero)
    have h_prod_ne : (∏ G ∈ A, specialize G a) ≠ 0 := by
      intro h_zero
      rw [h_zero, Polynomial.rootMultiplicity_zero] at h_mult
      exact (hm_pos _).ne' h_mult.symm
    have h_each_ne : ∀ G ∈ A, specialize G a ≠ 0 :=
      fun G hG h_zero => h_prod_ne (Finset.prod_eq_zero hG h_zero)
    -- (σ i).val is in J, so the owner of θ (σ i).val is F
    have hi_mem : (σ i).val ∈ J := (σ i).property
    have h_owner_eq : owner (σ i).val = F := by
      have := hi_mem
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    -- F has θ (σ i).val a as a root
    have hF_root : (specialize F a).IsRoot (θ (σ i).val a) := by
      have := h_owner_root (σ i).val a ha
      rwa [h_owner_eq] at this
    -- For G ≠ F in A, θ (σ i).val a is NOT a root of specialize G a
    have h_G_ne_root : ∀ G ∈ A, G ≠ F →
        ¬ (specialize G a).IsRoot (θ (σ i).val a) := by
      intro G hGA hGF h_root
      exact hGF (h_unique_factor a ha (σ i).val F hF G hGA hF_root h_root).symm
    -- Multiplicity of product = sum of multiplicities (since all factors nonzero)
    have h_prod_mult : ∀ (s : Finset (PolyR n)) (h_ne : ∀ G ∈ s, specialize G a ≠ 0),
        (∏ G ∈ s, specialize G a).rootMultiplicity (θ (σ i).val a) =
        ∑ G ∈ s, (specialize G a).rootMultiplicity (θ (σ i).val a) := by
      intro s
      induction s using Finset.induction with
      | empty =>
        intro _
        simp only [Finset.prod_empty, Finset.sum_empty,
          show (1 : Polynomial ℝ) = Polynomial.C 1 from (map_one _).symm,
          Polynomial.rootMultiplicity_C]
      | @insert p s hps ih =>
        intro h_ne
        have h_p_ne : specialize p a ≠ 0 := h_ne p (Finset.mem_insert_self _ _)
        have h_s_ne : ∀ G ∈ s, specialize G a ≠ 0 :=
          fun G hG => h_ne G (Finset.mem_insert_of_mem hG)
        have h_pr_ne : (∏ G ∈ s, specialize G a) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr h_s_ne
        rw [Finset.prod_insert hps, Finset.sum_insert hps,
          Polynomial.rootMultiplicity_mul (mul_ne_zero h_p_ne h_pr_ne), ih h_s_ne]
    rw [h_prod_mult A h_each_ne] at h_mult
    -- Sum reduces to mult_F (others are 0)
    rw [← Finset.add_sum_erase A _ hF] at h_mult
    have h_sum_zero :
        ∑ G ∈ A.erase F, (specialize G a).rootMultiplicity (θ (σ i).val a) = 0 := by
      apply Finset.sum_eq_zero
      intro G hG
      rw [Finset.mem_erase] at hG
      exact Polynomial.rootMultiplicity_eq_zero (h_G_ne_root G hG.2 hG.1)
    rw [h_sum_zero, Nat.add_zero] at h_mult
    exact h_mult

/-- Root function of a factor is a root function of the product. -/
theorem root_function_factor_of_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n)) (G : PolyR n) (hG : G ∈ A)
    (θ : (Fin n → ℝ) → ℝ)
    (hθ : IsRootFunction G θ S) :
    IsRootFunction (∏ f ∈ A, f) θ S := by
  intro a ha
  have hprod : specialize (∏ f ∈ A, f) a = ∏ f ∈ A, specialize f a := by
    simp [specialize, Polynomial.map_prod]
  rw [Polynomial.IsRoot, hprod, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hG (hθ a ha)

/-- Degree-invariance of product from degree-invariance of factors.

**Note:** The original statement used `NotIdenticallyZeroOn` (existential) for `hne`,
but that is too weak — a factor can be degree-invariant with constant degree 0, not
identically zero, yet have its specialization vanish at some points, breaking
degree-invariance of the product. The corrected hypothesis requires each specialization
to be nonzero everywhere on `S`, which is what is available at the call site via
`specialize_nonzero_everywhere`. -/
theorem degree_invariant_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hdeg : ∀ f ∈ A, DegreeInvariant f S)
    (hne : ∀ f ∈ A, ∀ a ∈ S, specialize f a ≠ 0) :
    DegreeInvariant (∏ f ∈ A, f) S := by
  intro a ha b hb
  have ha' : ∀ f ∈ A, Polynomial.map (evalBase a) f ≠ 0 := fun f hf => hne f hf a ha
  have hb' : ∀ f ∈ A, Polynomial.map (evalBase b) f ≠ 0 := fun f hf => hne f hf b hb
  simp only [specialize, Polynomial.map_prod]
  rw [Polynomial.natDegree_prod _ _ ha', Polynomial.natDegree_prod _ _ hb']
  exact Finset.sum_congr rfl (fun f hf => hdeg f hf a ha b hb)

/-- If a nonzero coefficient of `f` is order-invariant on `S` and `f` is not identically
    zero on `S`, then at every point of `S` the specialization of `f` is nonzero. -/
theorem specialize_nonzero_everywhere
    (f : PolyR n)
    (S : Set (Fin n → ℝ))
    (hne : NotIdenticallyZeroOn f S)
    (hcoeff : ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S) :
    ∀ a ∈ S, specialize f a ≠ 0 := by
  obtain ⟨a₀, ha₀, hfa₀⟩ := hne
  rw [Ne, Polynomial.ext_iff, not_forall] at hfa₀
  push Not at hfa₀
  obtain ⟨k, hk⟩ := hfa₀
  simp only [specialize, Polynomial.coeff_map, Polynomial.coeff_zero] at hk
  have hc_ne : f.coeff k ≠ 0 := by
    intro heq; apply hk; simp [heq]
  have hc_oi := hcoeff k hc_ne
  have hord₀ : polyOrder n (f.coeff k) a₀ = 0 := by
    rw [polyOrder_zero_iff]; exact hk
  intro a ha
  have hord : polyOrder n (f.coeff k) a = 0 := by
    rw [hc_oi a ha a₀ ha₀, hord₀]
  rw [polyOrder_zero_iff] at hord
  intro hfa
  apply hord
  have : (specialize f a).coeff k = 0 := by rw [hfa]; simp
  simp [specialize, Polynomial.coeff_map] at this
  exact this

/-- Product of not-identically-zero polynomials is not identically zero on `S`,
    when all nonzero coefficients of each factor are order-invariant on `S`. -/
theorem not_identically_zero_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hne : ∀ f ∈ A, NotIdenticallyZeroOn f S)
    (hcoeff : ∀ f ∈ A, ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S)
    (hS_ne : S.Nonempty) :
    NotIdenticallyZeroOn (∏ f ∈ A, f) S := by
  have hall : ∀ f ∈ A, ∀ a ∈ S, specialize f a ≠ 0 :=
    fun f hf => specialize_nonzero_everywhere f S (hne f hf) (hcoeff f hf)
  obtain ⟨a, ha⟩ := hS_ne
  refine ⟨a, ha, ?_⟩
  rw [show specialize (∏ f ∈ A, f) a = ∏ f ∈ A, specialize f a from by
    simp [specialize, Polynomial.map_prod]]
  exact Finset.prod_ne_zero_iff.mpr (fun f hf => hall f hf a ha)

lemma natDegree_mul {n : Nat} (p q : PolyR n) (hp : 0 < p.natDegree) (hq : 0 < q.natDegree) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  refine Polynomial.natDegree_mul (p := p) (q := q) ?_ ?_
  · exact ne_zero_of_natDegree_gt hp
  · exact ne_zero_of_natDegree_gt hq

lemma prod_insert (A : Finset (PolyR n)) (x : (PolyR n)) (hx : x ∉ A) :
    ∏ i ∈ insert x A, i = x *  ∏ i ∈ A, i := by
  rw [Finset.prod_eq_prod_diff_singleton_mul (i := x)]
  · have : insert x A \ {x} = A := by grind
    rw [this]
    exact CommMonoid.mul_comm (∏ x ∈ A, x) x
  · exact Finset.mem_insert_self x A

theorem prod_pos_degree'
    (A : Finset (PolyR n)) (hA : A.Nonempty)
    (hpos : ∀ f ∈ A, 0 < f.natDegree) :
    (∏ f ∈ A, f).natDegree = ∑ f ∈ A, f.natDegree := by
  induction A using Finset.induction
  next => simp at hA
  next p A p_not_mem IH =>
    if hA: A.Nonempty then
      have deg_pos : ∀ f ∈ A, 0 < natDegree f := by simp_all only [Finset.mem_insert, or_true,
        implies_true, forall_const, Finset.insert_nonempty, forall_eq_or_imp]
      have := IH hA deg_pos
      rw [prod_insert A p _, natDegree_mul, IH]
      · exact Eq.symm (Finset.sum_insert p_not_mem)
      · exact hA
      · assumption
      · exact hpos p (Finset.mem_insert_self p A)
      · rw [this]
        exact Finset.sum_pos deg_pos hA
      · exact p_not_mem
    else
      have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      rw [this]
      simp

/-- Product of positive-degree polynomials has positive degree
    (when the set is nonempty). -/
theorem prod_pos_degree
    (A : Finset (PolyR n)) (hA : A.Nonempty)
    (hpos : ∀ f ∈ A, 0 < f.natDegree) :
    0 < (∏ f ∈ A, f).natDegree := by
  rw [prod_pos_degree' _ hA hpos]
  exact Finset.sum_pos hpos hA

end
