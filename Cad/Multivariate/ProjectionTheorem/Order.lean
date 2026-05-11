import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.BourbakiWitt

noncomputable section

open scoped Topology
open Filter Set Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (f : E → F)
variable (x₀ : E)

/-- The vanishing order of `f` at `x₀`, as an element of `ℕ∞`.

The order is defined to be `⊤` if all iterated Fréchet derivatives of `f` vanish at `x₀`, and
otherwise the smallest `n` such that `iteratedFDeriv 𝕜 n f x₀ ≠ 0`. -/
noncomputable def order (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (x₀ : E) : ℕ∞ :=
  -- Note: `iteratedFDeriv 𝕜 n f x₀ is a `ContinuousMultilinearMap`, taking a list of
  -- `n` vectors and producing the derivative of `f` along these vectors. If this function
  -- is `0`, it means that the output is `0` for all list of vectors, in particular for
  -- the vectors that would output the classical partial derivative. Also, if it is not `0`,
  -- it must be in particular not `0` for the vectors that would output the partial derivatives.
  if h : ∃ n, iteratedFDeriv 𝕜 n f x₀ ≠ 0 then ↑(Nat.find h)
  else ⊤


section PDeriv

open MvPolynomial

/-- The partial derivative of a multivariate polynomial according to a list
of variables to differentiate -/
def iteratedPDeriv {n : Nat} (l : List (Fin n))
    (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  l.foldr (fun i q => MvPolynomial.pderiv i q) p

/-- An alternative definition for the order of a multivariate polynomial at
a point based on partial derivatives -/
def order' (n : Nat) (f : MvPolynomial (Fin n) ℝ) (p : Fin n → Real) : ℕ∞ :=
  if h: (∃ k : Nat, ∃ l : List (Fin n), l.length = k ∧ (iteratedPDeriv l f).eval p ≠ 0) then ↑(Nat.find h)
  else ⊤

/-- The Fréchet derivative of a polynomial evaluation in the direction of the j-th
basis vector equals the algebraic partial derivative evaluated at the point. -/
-- Helper: evaluation of a polynomial is differentiable
theorem differentiableAt_eval (m : Nat) (q : MvPolynomial (Fin m) ℝ) (p : Fin m → ℝ) :
    DifferentiableAt ℝ (fun x => eval x q) p :=
  (AnalyticOnNhd.eval_mvPolynomial q p (Set.mem_univ p)).differentiableAt

theorem fderiv_eval_eq_pderiv_eval (m : Nat) (q : MvPolynomial (Fin m) ℝ)
    (p : Fin m → ℝ) (j : Fin m) :
    fderiv ℝ (fun x => eval x q) p (Pi.single j 1) = (pderiv j q).eval p := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C]
    have : HasFDerivAt (fun _ : Fin m → ℝ => a) (0 : (Fin m → ℝ) →L[ℝ] ℝ) p :=
      hasFDerivAt_const a p
    simp [this.fderiv]
  | add q₁ q₂ ih₁ ih₂ =>
    simp only [map_add]
    have h1 : DifferentiableAt ℝ (fun x => eval x q₁) p := differentiableAt_eval m q₁ p
    have h2 : DifferentiableAt ℝ (fun x => eval x q₂) p := differentiableAt_eval m q₂ p
    have heq : (fun x => eval x q₁ + eval x q₂) =
        (fun x => eval x q₁) + (fun x => eval x q₂) := rfl
    rw [heq, (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv]
    simp [ih₁, ih₂]
  | mul_X q i ih =>
    -- eval x (q * X i) = eval x q * x i
    have heq : ∀ x, eval x (q * X i) = eval x q * x i := by simp [eval_mul, eval_X]
    simp_rw [heq]
    have hf : HasFDerivAt (fun x => eval x q) (fderiv ℝ (fun x => eval x q) p) p :=
      (differentiableAt_eval m q p).hasFDerivAt
    have hg : HasFDerivAt (fun x : Fin m → ℝ => x i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) p :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).hasFDerivAt
    have hmul' : HasFDerivAt (fun x => eval x q * x i)
        ((eval p q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i +
         p i • fderiv ℝ (fun x => eval x q) p) p := hf.mul hg
    simp only [hmul'.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, ih, (pderiv j).leibniz, map_add,
        smul_eq_mul, eval_mul, eval_X]
    congr 1
    simp [pderiv_X, Pi.single_apply, eq_comm]

/-- Auxiliary: `iteratedPDeriv` unfolds on cons via `foldr`. -/
theorem iteratedPDeriv_cons {m : Nat} (j : Fin m) (l : List (Fin m))
    (f : MvPolynomial (Fin m) ℝ) :
    iteratedPDeriv (j :: l) f = pderiv j (iteratedPDeriv l f) := by
  simp [iteratedPDeriv, List.foldr_cons]

/-- Evaluating a ContinuousMultilinearMap commutes with taking fderiv:
`(fderiv g x v) m = fderiv (fun y => g y m) x v`. -/
private lemma fderiv_cml_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {g : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    {x v : E} {m : Fin n → E}
    (hg : DifferentiableAt ℝ g x) :
    (fderiv ℝ g x v) m = fderiv ℝ (fun y => g y m) x v := by
  have heval :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F m).hasFDerivAt (x := g x)
  have hcomp : HasFDerivAt (fun y => g y m)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F m).comp (fderiv ℝ g x)) x := by
    have := heval.comp x hg.hasFDerivAt
    simp at this; exact this
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- The k-th iterated Fréchet derivative of a polynomial, applied to standard basis vectors
indexed by a function `v : Fin k → Fin m`, equals the iterated partial derivative
(with respect to the corresponding variable list) evaluated at the point. -/
theorem iteratedFDeriv_basis_eq_iteratedPDeriv (m : Nat) (f : MvPolynomial (Fin m) ℝ)
    (p : Fin m → ℝ) (k : ℕ) (v : Fin k → Fin m) :
    iteratedFDeriv ℝ k (fun x => eval x f) p
      (fun i => Pi.single (v i) (1 : ℝ)) =
    (iteratedPDeriv (List.ofFn v) f).eval p := by
  induction k generalizing f p with
  | zero =>
    simp [iteratedPDeriv, List.ofFn, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ, iteratedPDeriv_cons, iteratedFDeriv_succ_apply_left]
    -- Commute fderiv evaluation with CML application
    have hDiff : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k (fun x => eval x f) y) p := by
      have han : AnalyticOnNhd ℝ (fun x => eval x f) Set.univ :=
        fun x _ => AnalyticOnNhd.eval_mvPolynomial f x (Set.mem_univ x)
      exact ((han.iteratedFDeriv k) p (Set.mem_univ p)).differentiableAt
    rw [fderiv_cml_apply hDiff]
    -- Simplify Fin.tail of the basis vector tuple
    have tail_eq : Fin.tail (fun i : Fin (k + 1) => (Pi.single (v i) (1 : ℝ) : Fin m → ℝ)) =
        fun i => Pi.single (v (Fin.succ i)) 1 := by ext i; simp [Fin.tail]
    simp_rw [tail_eq]
    -- Use the IH pointwise (generalised over p) to rewrite the inner iteratedFDeriv
    have key : (fun y : Fin m → ℝ =>
          iteratedFDeriv ℝ k (fun x => eval x f) y (fun i => Pi.single (v (Fin.succ i)) 1)) =
        (fun y => (iteratedPDeriv (List.ofFn (v ∘ Fin.succ)) f).eval y) := by
      ext y; exact ih f y (v ∘ Fin.succ)
    simp_rw [key]
    exact fderiv_eval_eq_pderiv_eval m (iteratedPDeriv (List.ofFn (v ∘ Fin.succ)) f) p (v 0)

/-- A continuous multilinear map on `Fin m → ℝ` is zero iff it vanishes on all
tuples of standard basis vectors. -/
theorem continuousMultilinearMap_eq_zero_iff_basis (m k : Nat)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin m → ℝ) ℝ) :
    g = 0 ↔ ∀ v : Fin k → Fin m,
      g (fun i => Pi.single (v i) 1) = 0 := by
  constructor
  · intro h v; simp [h]
  · intro h
    ext x
    simp only [ContinuousMultilinearMap.zero_apply]
    -- Express each component x i as a sum of scaled basis vectors
    have hx : ∀ i : Fin k,
        x i = ∑ j : Fin m, (x i j) • (Pi.single j (1 : ℝ) : Fin m → ℝ) := by
      intro i; funext l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
                 mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    -- Rewrite x in terms of basis vectors and expand via multilinearity
    have heq : x = fun i => ∑ j : Fin m, (x i j) • (Pi.single j (1 : ℝ) : Fin m → ℝ) :=
      funext hx
    rw [heq, show (g fun i => ∑ j : Fin m, x i j • (Pi.single j (1 : ℝ) : Fin m → ℝ)) =
        ∑ v : Fin k → Fin m, g (fun i => x i (v i) • (Pi.single (v i) (1 : ℝ) : Fin m → ℝ)) from
      g.toMultilinearMap.map_sum (fun i j => x i j • (Pi.single j (1 : ℝ) : Fin m → ℝ))]
    apply Finset.sum_eq_zero
    intro v _
    rw [g.map_smul_univ]
    simp [h v]

/-- The k-th Fréchet derivative of a polynomial is nonzero at a point iff some
k-fold iterated partial derivative is nonzero at that point. -/
theorem iteratedFDeriv_ne_zero_iff_exists_iteratedPDeriv (m : Nat)
    (f : MvPolynomial (Fin m) ℝ) (p : Fin m → ℝ) (k : ℕ) :
    iteratedFDeriv ℝ k (fun x => eval x f) p ≠ 0 ↔
    ∃ l : List (Fin m), l.length = k ∧ (iteratedPDeriv l f).eval p ≠ 0 := by
  rw [Ne, continuousMultilinearMap_eq_zero_iff_basis]
  push Not
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨List.ofFn v, List.length_ofFn, ?_⟩
    rwa [← iteratedFDeriv_basis_eq_iteratedPDeriv]
  · rintro ⟨l, hl, hne⟩
    subst hl
    refine ⟨fun i => l.get i, ?_⟩
    rwa [iteratedFDeriv_basis_eq_iteratedPDeriv, List.ofFn_get]

theorem order_order' (m : Nat) (f : MvPolynomial (Fin m) ℝ) (p : Fin m → ℝ) (k : ℕ∞) :
    order' m f p = k ↔
      order ℝ (fun x => MvPolynomial.eval x f) p = k := by
  -- Both sides are defined via `Nat.find` on equivalent predicates.
  -- The key bridge: the predicates inside `Nat.find` are equivalent at each level.
  set g := fun x => eval x f
  set hfp := AnalyticOnNhd.eval_mvPolynomial f p (Set.mem_univ p)
  unfold order' order
  -- Show the existential predicates are equivalent
  have equiv : (∃ k, ∃ l : List (Fin m), l.length = k ∧ (iteratedPDeriv l f).eval p ≠ 0) ↔
      (∃ k, iteratedFDeriv ℝ k g p ≠ 0) := by
    constructor
    · rintro ⟨k, l, hl, hne⟩
      exact ⟨k, (iteratedFDeriv_ne_zero_iff_exists_iteratedPDeriv m f p k).mpr ⟨l, hl, hne⟩⟩
    · rintro ⟨k, hk⟩
      obtain ⟨l, hl, hne⟩ := (iteratedFDeriv_ne_zero_iff_exists_iteratedPDeriv m f p k).mp hk
      exact ⟨k, l, hl, hne⟩
  by_cases h1 : ∃ j, ∃ l : List (Fin m), l.length = j ∧ (iteratedPDeriv l f).eval p ≠ 0
  · -- Both predicates hold; show Nat.find agrees
    have h2 : ∃ j, iteratedFDeriv ℝ j g p ≠ 0 := equiv.mp h1
    rw [dif_pos h1, dif_pos h2]
    suffices Nat.find h1 = Nat.find h2 by rw [this]
    apply le_antisymm
    · -- Show Nat.find h1 ≤ Nat.find h2:
      -- Nat.find h2 satisfies predicate of h1
      apply Nat.find_min' h1
      exact (iteratedFDeriv_ne_zero_iff_exists_iteratedPDeriv m f p _).mp (Nat.find_spec h2)
    · -- Show Nat.find h2 ≤ Nat.find h1:
      -- Nat.find h1 satisfies predicate of h2
      apply Nat.find_min' h2
      obtain ⟨l, hl, hne⟩ := Nat.find_spec h1
      exact (iteratedFDeriv_ne_zero_iff_exists_iteratedPDeriv m f p _).mpr ⟨l, hl, hne⟩
  · -- Neither predicate holds; both sides are ⊤
    have h2 : ¬∃ j, iteratedFDeriv ℝ j g p ≠ 0 := fun h => h1 (equiv.mpr h)
    rw [dif_neg h1, dif_neg h2]

end PDeriv


variable {f g : E → F} {x₀ : E} {n : ℕ}

theorem order_eq_top_iff :
    order 𝕜 f x₀ = ⊤ ↔ ∀ n, iteratedFDeriv 𝕜 n f x₀ = 0 := by
  unfold order
  split_ifs with h
  · exact ⟨fun hc => absurd hc (ENat.coe_ne_top _),
     fun hall => by obtain ⟨n, hn⟩ := h; exact absurd (hall n) hn⟩
  · push Not at h
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem order_eq_natCast_iff :
    order 𝕜 f x₀ = ↑n ↔
      (∀ m, m < n → iteratedFDeriv 𝕜 m f x₀ = 0) ∧ iteratedFDeriv 𝕜 n f x₀ ≠ 0 := by
  unfold order
  constructor
  · intro h
    split_ifs at h with hex
    · have heq : Nat.find hex = n := by exact_mod_cast h
      rw [← heq]
      exact ⟨fun m hm => by_contra fun hne => Nat.find_min hex hm hne,
             Nat.find_spec hex⟩
    · exact absurd h (ENat.top_ne_coe _)
  · intro ⟨hlt, hne⟩
    have hex : ∃ n, iteratedFDeriv 𝕜 n f x₀ ≠ 0 := ⟨n, hne⟩
    rw [dif_pos hex]
    congr 1
    apply le_antisymm
    · exact Nat.find_min' hex hne
    · by_contra hlt'
      push Not at hlt'
      exact Nat.find_spec hex (hlt _ hlt')

theorem iteratedFDeriv_eq_zero_of_lt_order
    (hn : ↑n < order 𝕜 f x₀) :
    iteratedFDeriv 𝕜 n f x₀ = 0 := by
  by_contra hne
  have hex : ∃ n, iteratedFDeriv 𝕜 n f x₀ ≠ 0 := ⟨n, hne⟩
  have : order 𝕜 f x₀ ≤ ↑n := by
    unfold order
    rw [dif_pos hex]
    exact_mod_cast Nat.find_min' hex hne
  exact not_le.mpr hn this

/-- The analytic order of `g ∈ ℝ[x₁,…,xₘ]` at `a`, defined via Frechet derivatives.
    This is a wrapper around `order` from `CAD.Order`, specializing to polynomial
    evaluation functions which are always analytic. -/
def polyOrder (m : Nat) (g : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) : ℕ∞ :=
  order ℝ (fun x => MvPolynomial.eval x g) a

/-- The 0th iterated Fréchet derivative of `f` is nonzero at `x₀` iff `f(x₀) ≠ 0`. -/
private lemma iteratedFDeriv_zero_ne_zero_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x₀ : E} :
    iteratedFDeriv ℝ 0 f x₀ ≠ 0 ↔ f x₀ ≠ 0 := by
  constructor
  · intro h hfx; apply h; ext m; simp [iteratedFDeriv_zero_apply, hfx]
  · intro h heq; apply h
    have := iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := f) (x := x₀) (fun i => Fin.elim0 i)
    rw [heq] at this; simp at this; exact this.symm

/-- `polyOrder m g a = 0` iff `eval a g ≠ 0`. -/
theorem polyOrder_zero_iff (m : Nat) (g : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    polyOrder m g a = 0 ↔ MvPolynomial.eval a g ≠ 0 := by
  unfold polyOrder order
  constructor
  · intro h
    split_ifs at h with hex
    · have hfind : Nat.find hex = 0 := by exact_mod_cast h
      have hspec := Nat.find_spec hex
      rw [hfind] at hspec
      exact (iteratedFDeriv_zero_ne_zero_iff (f := fun x => MvPolynomial.eval x g)).mp hspec
    · simp at h
  · intro h
    have hex : ∃ k, iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x g) a ≠ 0 :=
      ⟨0, (iteratedFDeriv_zero_ne_zero_iff (f := fun x => MvPolynomial.eval x g)).mpr h⟩
    rw [dif_pos hex]
    have : Nat.find hex = 0 :=
      Nat.eq_zero_of_le_zero (Nat.find_min' hex
        ((iteratedFDeriv_zero_ne_zero_iff (f := fun x => MvPolynomial.eval x g)).mpr h))
    simp [this]
