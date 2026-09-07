import Mathlib

open SignType

namespace List

variable {α : Type*} [Zero α] [LinearOrder α]

def signVariations (l : List α) : ℕ :=
  letI signs := l.map SignType.sign
  letI nonzero_signs := signs.filter (· ≠ 0)
  (nonzero_signs.destutter (· ≠ ·)).length - 1

lemma signVariations_nil :
    signVariations ([] : List α) = 0 := by
  trivial

lemma signVariations_singleton : ∀ (a : α),
    signVariations [a] = 0 := by
  intro a
  if ha: a = 0 then
    rw [ha]
    simp [signVariations]
  else
    simp [signVariations, ha]

lemma signVariations_zero_cons : ∀ (b : α) (as : List α),
    signVariations (0 :: b :: as) = signVariations (b :: as) := by
  simp [signVariations, filter]

lemma signVariations_cons_zero_cons : ∀ (a : α) (as : List α),
    signVariations (a :: 0 :: as) = signVariations (a :: as) := by
  simp [signVariations, filter]

lemma signVariations_cons_cons_of_ne_zero : ∀ (a b : α) (as : List α),
    a ≠ 0 → b ≠ 0 → signVariations (a :: b :: as) = (if sign a = sign b then 0 else 1) + signVariations (b :: as) := by
  intros a b as ha hb
  have ha' : sign a ≠ 0 := by rwa [ne_eq, sign_eq_zero_iff]
  have hb' : sign b ≠ 0 := by rwa [ne_eq, sign_eq_zero_iff]
  have hf1 : ((a :: b :: as).map sign).filter (· ≠ 0) = sign a :: sign b :: (as.map sign).filter (· ≠ 0) := by
    simp [ha', hb']
  have hf2 : ((b :: as).map sign).filter (· ≠ 0) = sign b :: (as.map sign).filter (· ≠ 0) := by
    simp [hb']
  have hne : ((sign b :: (as.map sign).filter (· ≠ 0)).destutter (· ≠ ·)).length ≠ 0 := by
    rw [ne_eq, length_eq_zero_iff, destutter_eq_nil]
    simp
  simp only [signVariations, hf1, hf2, destutter_cons_cons, ← destutter_cons']
  by_cases h : sign a = sign b
  · rw [if_neg (not_not.mpr h), if_pos h, h, zero_add]
  · rw [if_pos h, if_neg h, length_cons]
    omega

/-- `signVariations` only depends on the signs of the entries, so it is invariant under any
map that preserves signs (e.g. casts, or `sign` itself). -/
lemma signVariations_map {β : Type*} [Zero β] [LinearOrder β] {f : α → β}
    (hf : ∀ x, sign (f x) = sign x) (l : List α) :
    signVariations (l.map f) = signVariations l := by
  have : (l.map f).map sign = l.map sign := by
    rw [map_map]
    exact map_congr_left fun x _ => hf x
  simp only [signVariations, this]

end List

section RealPoly

open Polynomial

open Classical in
theorem termination_sturmSeq {α : Type*} [Field α] (f g : Polynomial α) (hf : f ≠ 0) :
    (if g = 0 then 0 else if -f % g = 0 then 1 else 2 + (-f % g).natDegree) <
    if f = 0 then 0 else if g = 0 then 1 else 2 + g.natDegree := by
  if g1: g = 0 then
    simp_all
  else if h : g ∣ f then
    simp_all
    refine lt_add_of_lt_of_nonneg ?_ (Nat.zero_le g.natDegree); simp
  else
    simp_all only [↓reduceIte, EuclideanDomain.mod_eq_zero, dvd_neg]
    have : (-f % g).natDegree < g.natDegree := by
      apply natDegree_lt_natDegree ?_ (degree_mod_lt (-f) g1)
      simp_all only [ne_eq, EuclideanDomain.mod_eq_zero, dvd_neg, not_false_eq_true]
    exact Nat.add_lt_add_left this 2

open Classical in
noncomputable def sturmSeq {α : Type*} [Field α] (f g : Polynomial α) : List (Polynomial α) :=
  if f = 0 then
    []
  else
    f::(sturmSeq g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + natDegree g
  decreasing_by exact termination_sturmSeq f g (by assumption)

noncomputable def sign_pos_inf (p : Polynomial ℝ) : ℤ :=
  sign p.leadingCoeff

noncomputable def sign_neg_inf (p : Polynomial ℝ) : ℤ :=
  if Even p.natDegree then sign p.leadingCoeff else - sign p.leadingCoeff

noncomputable def seq_sign_pos_inf : List (Polynomial ℝ) → List ℤ := List.map (fun x => sign_pos_inf x)

noncomputable def seq_sign_neg_inf : List (Polynomial ℝ) → List ℤ := List.map (fun x => sign_neg_inf x)

def seqEval {α : Type*} [Semiring α] (k : α) : List (Polynomial α) → List α := List.map (eval k)

noncomputable def seqEvalSign (k : ℝ) : List (Polynomial ℝ) → List ℤ := List.map (fun a => sign (eval k a))

noncomputable def signVariations_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (List.signVariations (seqEval a P) : Int) - List.signVariations (seqEval b P)

noncomputable def signVariationsSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  signVariations_ab (sturmSeq p q) a b

noncomputable def signVariationsAbove_a (P: List (Polynomial ℝ)) (a : ℝ) : ℤ :=
  (List.signVariations (seqEval a P) : Int) - List.signVariations (seq_sign_pos_inf P)

noncomputable def signVariationsBelow_b (P: List (Polynomial ℝ)) (b : ℝ) : ℤ :=
  (List.signVariations (seq_sign_neg_inf P) : Int) - List.signVariations (seqEval b P)

noncomputable def signVariationsLine (P : List (Polynomial ℝ)) : ℤ :=
  (List.signVariations (seq_sign_neg_inf P) : Int) - List.signVariations (seq_sign_pos_inf P)

noncomputable def signVariationsAboveSturm (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  signVariationsAbove_a (sturmSeq p q) a

noncomputable def signVariationsBelowSturm (p q : Polynomial ℝ) (b : ℝ) : ℤ :=
  signVariationsBelow_b (sturmSeq p q) b

noncomputable def signVariationsLineSturm (p q : Polynomial ℝ) : ℤ  :=
  signVariationsLine (sturmSeq p q)

end RealPoly
