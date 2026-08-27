import Mathlib
import CompPoly
import Cad.Univariate.Utils

def seqVar_aux {α : Type*} [Ring α] [LinearOrder α] [DecidableEq α] (prev : α) : List α → ℕ
| [] => 0
| a :: as =>
  if a == 0 then seqVar_aux prev as
  else if prev * a < 0 then 1 + seqVar_aux a as
  else seqVar_aux a as

def seqVar {α : Type*} [Ring α] [LinearOrder α] [DecidableEq α] : List α → ℕ
| [] => 0
| a :: as => seqVar_aux a as

theorem seqVar_aux_map {α β : Type*} [Ring α] [LinearOrder α] [DecidableEq α]
    [Ring β] [LinearOrder β] [DecidableEq β] {f : α → β}
    (hf0 : ∀ x, f x = 0 ↔ x = 0) (hfmul : ∀ x y, f x * f y < 0 ↔ x * y < 0)
    (prev : α) (l : List α) :
    seqVar_aux (f prev) (l.map f) = seqVar_aux prev l := by
  induction l generalizing prev with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, seqVar_aux, beq_iff_eq, hf0, hfmul]
    split_ifs <;> simp [ih]

/-- `seqVar` is invariant under any map preserving zeroness and signs of products
(e.g. casts and `sgn`). -/
theorem seqVar_map {α β : Type*} [Ring α] [LinearOrder α] [DecidableEq α]
    [Ring β] [LinearOrder β] [DecidableEq β] {f : α → β}
    (hf0 : ∀ x, f x = 0 ↔ x = 0) (hfmul : ∀ x y, f x * f y < 0 ↔ x * y < 0)
    (l : List α) :
    seqVar (l.map f) = seqVar l := by
  cases l with
  | nil => rfl
  | cons a as => exact seqVar_aux_map hf0 hfmul a as

section RealPoly

open Polynomial

open Classical in
theorem termination_sturmSeq {α : Type*} [Field α] (f g : Polynomial α) (hf : f ≠ 0) :
    (if g = 0 then 0 else if -f % g = 0 then 1 else 2 + (-f % g).degree) <
    if f = 0 then 0 else if g = 0 then 1 else 2 + g.degree := by
  if g1: g = 0 then
    simp_all
  else if h : g ∣ f then
    simp_all
    have gnatdeg : g.degree ≥ 0 := zero_le_degree_iff.mpr g1
    refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
  else
    simp_all only [↓reduceIte, EuclideanDomain.mod_eq_zero, dvd_neg]
    have : (-f % g).degree < g.degree := by
      refine degree_lt_degree ?_; refine natDegree_mod_lt (-f) ?_
      have : g.natDegree = 0 → g ∣ f := by
        intro hg
        have : ∃ c : α, C c = g := natDegree_eq_zero.mp hg
        rcases this with ⟨c, rfl⟩; use C c⁻¹ * f
        have hds : c ≠ 0 := by
          intro abs; rw [abs] at hg; simp at g1; exact g1 abs
        ext x
        simp_all only [map_eq_zero, not_false_eq_true, isUnit_map_iff, isUnit_iff_ne_zero, ne_eq,
          IsUnit.dvd, not_true_eq_false]
      have : g.natDegree ≠ 0 := by simp_all only [imp_false, ne_eq, not_false_eq_true]
      exact this
    refine WithBot.add_lt_add_left ?_ this; simp_all

open Classical in
noncomputable def sturmSeq {α : Type*} [Field α] (f g : Polynomial α) : List (Polynomial α) :=
  if f = 0 then
    []
  else
    f::(sturmSeq g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + degree g
  decreasing_by exact termination_sturmSeq f g (by assumption)

noncomputable def sgn_pos_inf (p : Polynomial ℝ) : ℤ :=
  sgn p.leadingCoeff

noncomputable def sgn_neg_inf (p : Polynomial ℝ) : ℤ :=
  if Even p.natDegree then sgn p.leadingCoeff else - sgn p.leadingCoeff

noncomputable def seq_sgn_pos_inf : List (Polynomial ℝ) → List ℤ := List.map (fun x => sgn_pos_inf x)

noncomputable def seq_sgn_neg_inf : List (Polynomial ℝ) → List ℤ := List.map (fun x => sgn_neg_inf x)

def seqEval {α : Type*} [Semiring α] (k : α) : List (Polynomial α) → List α := List.map (eval k)

noncomputable def seqEvalSgn (k : ℝ) : List (Polynomial ℝ) → List ℤ := List.map (fun a => sgn (eval k a))

noncomputable def seqVar_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seqEval b P)

noncomputable def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b

noncomputable def seqVarAbove_a (P: List (Polynomial ℝ)) (a : ℝ) : ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seq_sgn_pos_inf P)

noncomputable def seqVarBelow_b (P: List (Polynomial ℝ)) (b : ℝ) : ℤ :=
  (seqVar (seq_sgn_neg_inf P) : Int) - seqVar (seqEval b P)

noncomputable def seqVarLine (P : List (Polynomial ℝ)) : ℤ :=
  (seqVar (seq_sgn_neg_inf P) : Int) - seqVar (seq_sgn_pos_inf P)

noncomputable def seqVarAboveSturm (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  seqVarAbove_a (sturmSeq p q) a

noncomputable def seqVarBelowSturm (p q : Polynomial ℝ) (b : ℝ) : ℤ :=
  seqVarBelow_b (sturmSeq p q) b

noncomputable def seqVarLineSturm (p q : Polynomial ℝ) : ℤ  :=
  seqVarLine (sturmSeq p q)

end RealPoly

section RatCPoly

open CompPoly
open CPolynomial

instance : DecidableEq (CPolynomial.Raw Rat) := instDecidableEqOfLawfulBEq

instance : DecidableEq (CPolynomial Rat) := Subtype.instDecidableEq

theorem termination_sturmSeqC (f g: CPolynomial ℚ) (hf : f ≠ 0) :
   (if g = 0 then 0 else if -f % g = 0 then 1 else 2 + (-f % g).degree) <
    if f = 0 then 0 else if g = 0 then 1 else 2 + g.degree := by
  if g1: g = 0 then
    simp_all
  else if h : f%g = 0 then
    simp_all
    have : ¬ g.toPoly = 0 := by
      intro hgp
      have : g = 0 := by
        apply CPolynomial.eq_zero_iff_coeff_zero.mpr
        have aux (x : ℚ) := CPolynomial.eval_toPoly x g
        rw[hgp] at aux; simp at aux
        simp only [CPolynomial.coeff_toPoly]
        rw[hgp]
        apply Polynomial.coeff_zero
      simp_all
    have : g.toPoly.degree ≥ 0 := Polynomial.zero_le_degree_iff.mpr this
    have gnatdeg : g.degree ≥ 0 := by
      have aux := CPolynomial.degree_toPoly g
      rw [← aux] at this; exact this
    have : -f % g = 0 := by
      have fgtopoly : (f % g).toPoly = 0 := by rw[h]; exact toPoly_zero
      have : ∃ k , f.toPoly = g.toPoly * k := by
        have : (f % g).toPoly = f.toPoly % g.toPoly := by apply toPoly_mod
        rw[this] at fgtopoly; simp_all only [ge_iff_le, EuclideanDomain.mod_eq_zero]
        exact fgtopoly
      rcases this with ⟨k, hk⟩
      have : (-f % g).toPoly = 0 := by
        have : (-f % g).toPoly = (-f).toPoly % g.toPoly := by apply toPoly_mod
        rw[this]
        have : (-f).toPoly = -f.toPoly := by exact toPoly_neg f
        rw[this, hk]
        have : -(g.toPoly * k) = g.toPoly*-k := by simp_all only [ge_iff_le, mul_neg]
        rw[this]; expose_names;
        refine CanonicalEuclideanDomain.mul_mod_eq_zero_of_mod_dvd g.toPoly (-k) g.toPoly this_1 ?_
        have : g.toPoly ∣ g.toPoly := by apply dvd_refl
        exact EuclideanDomain.mod_eq_zero.mpr this
      apply poly_eq0_of_toPoly_eq0; exact this
    simp_all
    refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
  else
    simp_all only [↓reduceIte]
    have : ¬ -f % g = 0 := by
      have k1 : ¬ (f % g).toPoly = 0 := by apply toPoly_ne0_of_poly_ne0; simp; exact h
      have : (f % g).toPoly = f.toPoly % g.toPoly := by exact toPoly_mod f g
      rw[this] at k1
      have k2 : (-f % g).toPoly = (-f).toPoly % g.toPoly := by apply toPoly_mod
      have k3 : (-f).toPoly = -f.toPoly := by exact toPoly_neg f
      have k4 : ¬ (-f % g).toPoly = 0 := by
        rw[k2, k3]; simp_all only [EuclideanDomain.mod_eq_zero, dvd_neg, not_false_eq_true]
      apply poly_ne0_of_toPoly_ne0; simp; exact k4
    simp_all
    have : (-f.toPoly % g.toPoly).degree < g.toPoly.degree := by
      refine Polynomial.degree_lt_degree ?_; refine Polynomial.natDegree_mod_lt (-f.toPoly) ?_
      have : g.toPoly.natDegree = 0 → g.toPoly ∣ f.toPoly := by
        intro hg
        have : ∃ c : ℚ, Polynomial.C c = g.toPoly := Polynomial.natDegree_eq_zero.mp hg
        rcases this with ⟨c, rf⟩; use Polynomial.C c⁻¹ * (f.toPoly)
        rw[←rf]; ring_nf
        have hds : c ≠ 0 := by
          by_contra
          have : Polynomial.C c = 0 := by
            rw[this]; aesop
          rw[this] at rf
          have : ¬ g.toPoly = 0 := by
            have : g.toPoly ≠ 0 := by apply toPoly_ne0_of_poly_ne0; simp; exact g1
            simp at this; exact this
          simp_all
        ext x
        simp_all only [ne_eq]
        rw[←rf]
        have : Polynomial.C c * Polynomial.C c⁻¹ = 1 := by
          have : Polynomial.C (c*c⁻¹) = Polynomial.C c * Polynomial.C c⁻¹ := by
            apply Polynomial.C_mul
          rw[← this]; simp_all only [ne_eq, not_false_eq_true, mul_inv_cancel₀, map_one]
        rw[this]; aesop
      have : ¬ (g.toPoly ∣ f.toPoly) → ¬ (g.toPoly.natDegree = 0) := by
        contrapose; exact this
      simp; apply this
      by_contra
      have : ¬ (f % g).toPoly = 0 := by apply toPoly_ne0_of_poly_ne0; simp; exact h
      have contr2 : (f % g).toPoly = f.toPoly % g.toPoly := by apply toPoly_mod
      simp_all
    have : (-f % g).toPoly.degree < g.toPoly.degree := by
      rw[toPoly_mod, toPoly_neg]
      simp_all
    have : (-f % g).degree < g.degree := by
      have : (-f%g).degree = (-f%g).toPoly.degree := by exact degree_toPoly (-f%g)
      rw[degree_toPoly]
      have : g.degree = g.toPoly.degree := by exact degree_toPoly g
      rw[this]; simp_all
    refine WithBot.add_lt_add_left ?_ this; simp_all

def sturmSeqC (f g : CPolynomial ℚ) : List (CPolynomial ℚ) :=
  if f = 0 then
    []
  else
    f::(sturmSeqC g (-f%g))
termination_by if f=0 then 0 else if g=0 then 1 else 2 + degree g
decreasing_by exact termination_sturmSeqC f g (by assumption)

def seqEvalC (k : ℚ) : List (CPolynomial ℚ) → List ℚ := List.map (eval k)

def seqVar_abC (P: List (CPolynomial ℚ)) (a b: ℚ): ℤ :=
  (seqVar (seqEvalC a P) : Int) - seqVar (seqEvalC b P)

def seqVarSturmC_ab (p q: (CPolynomial ℚ)) (a b : ℚ) : ℤ :=
  seqVar_abC (sturmSeqC p q) a b

def sgnC (q : ℚ) : ℤ :=
  if q < 0 then -1 else if q = 0 then 0 else 1

def sgn_pos_inf'' (p : CPolynomial ℚ) : ℤ :=
  sgnC p.leadingCoeff

def sgn_neg_inf'' (p : CPolynomial ℚ) : ℤ :=
  if Even p.natDegree then sgnC p.leadingCoeff else - sgnC p.leadingCoeff

def seq_sgn_pos_inf'' : List (CPolynomial ℚ) → List ℤ := List.map (fun x => sgn_pos_inf'' x)

def seq_sgn_neg_inf'' : List (CPolynomial ℚ) → List ℤ := List.map (fun x => sgn_neg_inf'' x)

def seqVarAboveC_a (P: List (CPolynomial ℚ)) (a : ℚ) : ℤ :=
  (seqVar (seqEvalC a P) : Int) - seqVar (seq_sgn_pos_inf'' P)

def seqVarBelowC_b (P: List (CPolynomial ℚ)) (b : ℚ) : ℤ :=
  (seqVar (seq_sgn_neg_inf'' P) : Int) - seqVar (seqEvalC b P)

def seqVarLineC (P : List (CPolynomial ℚ)) : ℤ :=
  (seqVar (seq_sgn_neg_inf'' P) : Int) - seqVar (seq_sgn_pos_inf'' P)

def seqVarAboveSturmC (p q : CPolynomial ℚ) (a : ℚ) : ℤ :=
  seqVarAboveC_a (sturmSeqC p q) a

def seqVarBelowSturmC (p q : CPolynomial ℚ) (b : ℚ) : ℤ :=
  seqVarBelowC_b (sturmSeqC p q) b

def seqVarLineSturmC (p q : CPolynomial ℚ) : ℤ  :=
  seqVarLineC (sturmSeqC p q)

end RatCPoly

open CompPoly

lemma leadingCoeff_toReal (p : CPolynomial ℚ) : p.leadingCoeff = (p.toPoly.map ratToRealHom).leadingCoeff := by
  simp only [CPolynomial.leadingCoeff_toPoly, Polynomial.leadingCoeff_map, eq_ratCast]

lemma natDegree_toReal (p: CPolynomial ℚ) : p.natDegree = (p.toPoly.map ratToRealHom).natDegree := by
  simp only [CPolynomial.natDegree_toPoly]
  norm_num

theorem seq_pos_inf_equiv (p : CPolynomial ℚ) : sgn_pos_inf'' p = sgn_pos_inf (p.toPoly.map ratToRealHom) := by
  unfold sgn_pos_inf'' sgn_pos_inf sgn sgnC
  rw [<- leadingCoeff_toReal]
  have : (p.leadingCoeff : Real) > 0 ↔ p.leadingCoeff > 0 := by norm_num
  have : (p.leadingCoeff : Real) = 0 ↔ p.leadingCoeff = 0 := by norm_num
  grind

theorem seq_neg_inf_equiv (p : CPolynomial ℚ) : sgn_neg_inf'' p = sgn_neg_inf (p.toPoly.map ratToRealHom) := by
  unfold sgn_neg_inf'' sgn_neg_inf sgn sgnC
  rw [<- leadingCoeff_toReal, <- natDegree_toReal]
  have : (p.leadingCoeff : Real) > 0 ↔ p.leadingCoeff > 0 := by norm_num
  have : (p.leadingCoeff : Real) = 0 ↔ p.leadingCoeff = 0 := by norm_num
  grind

theorem seq_sgn_pos_inf_eq (l : List (CPolynomial ℚ)) : seq_sgn_pos_inf'' l = seq_sgn_pos_inf (List.map (Polynomial.map ratToRealHom) (List.map CPolynomial.toPoly l)) := by
  unfold seq_sgn_pos_inf seq_sgn_pos_inf''
  have H := seq_pos_inf_equiv
  simp_all only [List.map_map, List.map_inj_left, Function.comp_apply, implies_true]

theorem seq_sgn_neg_inf_eq (l : List (CPolynomial ℚ)) : seq_sgn_neg_inf'' l = seq_sgn_neg_inf (List.map (Polynomial.map ratToRealHom) (List.map CPolynomial.toPoly l)) := by
  unfold seq_sgn_neg_inf seq_sgn_neg_inf''
  have H := seq_neg_inf_equiv
  simp_all only [List.map_map, List.map_inj_left, Function.comp_apply, implies_true]

theorem sturm_seq_toPoly (f g : CPolynomial ℚ) :
    sturmSeq f.toPoly g.toPoly = List.map CPolynomial.toPoly (sturmSeqC f g) := by
  unfold sturmSeq sturmSeqC
  split_ifs
  next => simp only [List.map_nil]
  next H1 H2 =>
    have := toPoly_ne0_of_poly_ne0 f H2
    contradiction
  next H1 H2 =>
    have := poly_ne0_of_toPoly_ne0 f H1
    contradiction
  next =>
    simp only [List.map_cons, List.cons.injEq, true_and]
    have IH := sturm_seq_toPoly g (-f%g)
    rw [<- IH]
    congr
    have h_mod := toPoly_mod (-f) g
    rw [h_mod]
    congr
    exact Eq.symm (CPolynomial.toPoly_neg f)
termination_by if f=0 then 0 else if g=0 then 1 else 2 + CPolynomial.degree g
decreasing_by exact termination_sturmSeqC f g (by assumption)

open Polynomial in
theorem sturm_seq_toReal (f g : Polynomial ℚ) :
    sturmSeq (f.map ratToRealHom) (g.map ratToRealHom) = List.map (Polynomial.map ratToRealHom) (sturmSeq f g) := by
  unfold sturmSeq
  if hf : f = 0 then
    rw [hf]
    simp only [Polynomial.map_zero, ↓reduceIte, List.map_nil]
  else
    have : f.map ratToRealHom ≠ 0 := Polynomial.map_ne_zero hf
    simp [this, hf]
    have IH := sturm_seq_toReal g (-f % g)
    rw [<- IH]
    congr
    rw [map_mod ratToRealHom]
    norm_num
termination_by if f=0 then 0 else if g=0 then 1 else 2 + Polynomial.degree g
decreasing_by
  if g1: g = 0 then
    simp_all
  else if h : g ∣ f then
    simp_all
    have gnatdeg : g.degree ≥ 0 := zero_le_degree_iff.mpr g1
    refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
  else
    simp_all only [↓reduceIte, EuclideanDomain.mod_eq_zero, dvd_neg]
    have : (-f % g).degree < g.degree := by
      refine degree_lt_degree ?_; refine natDegree_mod_lt (-f) ?_
      have : g.natDegree = 0 → g ∣ f := by
        intro hg
        have : ∃ c : Rat, C c = g := natDegree_eq_zero.mp hg
        rcases this with ⟨c, rfl⟩; use C c⁻¹ * f
        have hds : c ≠ 0 := by
          intro abs; rw [abs] at hg; simp at g1; exact g1 abs
        ext x
        simp_all only [map_eq_zero, not_false_eq_true, isUnit_map_iff, isUnit_iff_ne_zero, ne_eq,
          IsUnit.dvd, not_true_eq_false]
      have : g.natDegree ≠ 0 := by simp_all only [imp_false, ne_eq, not_false_eq_true]
      exact this
    refine WithBot.add_lt_add_left ?_ this; simp_all

theorem seqVarLineEquiv (fs : List (CPolynomial ℚ)) :
    seqVarLineC fs = seqVarLine (List.map (Polynomial.map ratToRealHom) (List.map CPolynomial.toPoly fs)) := by
  unfold seqVarLineC seqVarLine
  rw [seq_sgn_pos_inf_eq, seq_sgn_neg_inf_eq]

-- by computation, we can get the value of `seqVarLineSturmC f f.derivative`, say `k`. This theorem will conclude
-- that `seqVarLineSturm f.toPoly.toReal f.derivative.toPoly.toReal` is also `k`. `sturm_R` will conclude that
-- `f.toPoly.toReal` has `k` roots. From that point we only use with `f.toPoly.toReal`. Eventually we will need to evaluate it
-- at a given rational point. We need a theorem saying `f.toPoly.toReal.eval (x.toReal) = f.eval x` for rational x
theorem seqVarLineEquivSturm (f g : CPolynomial ℚ) : seqVarLineSturmC f g = seqVarLineSturm (f.toPoly.map ratToRealHom) (g.toPoly.map ratToRealHom) := by
  unfold seqVarLineSturm
  rw [sturm_seq_toReal, sturm_seq_toPoly]
  unfold seqVarLineSturmC
  exact seqVarLineEquiv (sturmSeqC f g)

lemma map_cast (p : Polynomial Rat) (x : Rat) :
    (p.eval x) = (p.map ratToRealHom).eval (ratToRealHom x) := by
  have := Polynomial.eval_map_apply ratToRealHom x (p := p)
  rw [this]
  norm_num

lemma cpolynomial_map_cast (x : Rat) (p : CPolynomial Rat) : p.eval x = (p.toPoly.map ratToRealHom).eval (x : Real) := by
  have := CPolynomial.eval_toPoly x p
  rw [this]
  have : (↑(Polynomial.eval x p.toPoly) : Real) = ratToRealHom (Polynomial.eval x p.toPoly) := by unfold ratToRealHom; norm_num
  rw [map_cast p.toPoly x]
  unfold ratToRealHom
  congr

private lemma seqEval_cast (a : ℚ) (L : List (CPolynomial ℚ)) :
    seqEval ((a : ℝ)) (List.map (Polynomial.map ratToRealHom) (List.map CPolynomial.toPoly L))
      = (seqEvalC a L).map ((↑) : ℚ → ℝ) := by
  unfold seqEval seqEvalC
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  rw [← cpolynomial_map_cast]

private lemma seqVar_ratCast (l : List ℚ) :
    seqVar (l.map ((↑) : ℚ → ℝ)) = seqVar l :=
  seqVar_map (fun x => by norm_num)
    (fun x y => by rw [← Rat.cast_mul]; exact Rat.cast_lt_zero) l

private lemma toPolyReal_mul (p q : CPolynomial ℚ) :
    toPolyReal (p * q) = toPolyReal p * toPolyReal q := by
  unfold toPolyReal
  rw [CPolynomial.toPoly_mul, Polynomial.map_mul]

private lemma toPolyReal_derivative (p : CPolynomial ℚ) :
    (toPolyReal p).derivative = toPolyReal p.derivative := by
  unfold toPolyReal
  rw [Polynomial.derivative_map, ← CPolynomial.derivative_toPoly]

private lemma sturmSeq_toPolyReal (f g : CPolynomial ℚ) :
    sturmSeq (toPolyReal f) (toPolyReal g)
      = List.map (Polynomial.map ratToRealHom) (List.map CPolynomial.toPoly (sturmSeqC f g)) := by
  unfold toPolyReal
  rw [sturm_seq_toReal, sturm_seq_toPoly]

theorem seqVarABEquivSturm (p q : CPolynomial ℚ) (a b : ℚ) :
    seqVarSturmC_ab p (p.derivative * q) a b
      = seqVarSturm_ab (toPolyReal p) ((toPolyReal p).derivative * (toPolyReal q)) a b := by
  unfold seqVarSturmC_ab seqVarSturm_ab seqVar_ab seqVar_abC
  rw [toPolyReal_derivative, ← toPolyReal_mul, sturmSeq_toPolyReal,
      seqEval_cast, seqEval_cast, seqVar_ratCast, seqVar_ratCast]
