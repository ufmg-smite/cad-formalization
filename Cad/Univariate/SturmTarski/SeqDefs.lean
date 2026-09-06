import Mathlib

open SignType

def seqVar {α : Type*} [Ring α] [LinearOrder α] [DecidableEq α] : List α → ℕ
| [] => 0
| _::[] => 0
| a::(b::as) =>
  if b == 0 then
    seqVar (a::as)
  else if a * b < 0 then
    1 + seqVar (b::as)
  else
    seqVar (b::as)

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

noncomputable def sign_pos_inf (p : Polynomial ℝ) : ℤ :=
  sign p.leadingCoeff

noncomputable def sign_neg_inf (p : Polynomial ℝ) : ℤ :=
  if Even p.natDegree then sign p.leadingCoeff else - sign p.leadingCoeff

noncomputable def seq_sign_pos_inf : List (Polynomial ℝ) → List ℤ := List.map (fun x => sign_pos_inf x)

noncomputable def seq_sign_neg_inf : List (Polynomial ℝ) → List ℤ := List.map (fun x => sign_neg_inf x)

def seqEval {α : Type*} [Semiring α] (k : α) : List (Polynomial α) → List α := List.map (eval k)

noncomputable def seqEvalSign (k : ℝ) : List (Polynomial ℝ) → List ℤ := List.map (fun a => sign (eval k a))

noncomputable def seqVar_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seqEval b P)

noncomputable def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b

noncomputable def seqVarAbove_a (P: List (Polynomial ℝ)) (a : ℝ) : ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seq_sign_pos_inf P)

noncomputable def seqVarBelow_b (P: List (Polynomial ℝ)) (b : ℝ) : ℤ :=
  (seqVar (seq_sign_neg_inf P) : Int) - seqVar (seqEval b P)

noncomputable def seqVarLine (P : List (Polynomial ℝ)) : ℤ :=
  (seqVar (seq_sign_neg_inf P) : Int) - seqVar (seq_sign_pos_inf P)

noncomputable def seqVarAboveSturm (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  seqVarAbove_a (sturmSeq p q) a

noncomputable def seqVarBelowSturm (p q : Polynomial ℝ) (b : ℝ) : ℤ :=
  seqVarBelow_b (sturmSeq p q) b

noncomputable def seqVarLineSturm (p q : Polynomial ℝ) : ℤ  :=
  seqVarLine (sturmSeq p q)

end RealPoly
