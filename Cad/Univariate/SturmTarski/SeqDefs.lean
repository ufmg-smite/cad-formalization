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

/-! ### Facts about `SignType.sign` -/

@[simp] lemma SignType.sign_cast {β : Type*} [Ring β] [LinearOrder β] [IsStrictOrderedRing β]
    (s : SignType) : sign (s : β) = s := by
  cases s <;> simp [sign_neg]

lemma sign_intCast_sign {α : Type*} [Zero α] [LinearOrder α] (a : α) :
    sign ((sign a : SignType) : ℤ) = sign a :=
  SignType.sign_cast _

lemma sign_eq_sign_of_mul_nonneg {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : 0 ≤ x * y) :
    sign x = sign y := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · rw [sign_neg hx, sign_neg hy]
  · exact absurd h (not_le.mpr (mul_neg_of_neg_of_pos hx hy))
  · exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg hx hy))
  · rw [sign_pos hx, sign_pos hy]

/-- For nonzero reals, "same sign" versus "product negative", as `signVariations` uses the former
and the Sturm proofs reason with the latter. -/
lemma ite_sign_eq {R : Type*} [Zero R] [One R] {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (if sign x = sign y then (0 : R) else 1) = if x * y < 0 then 1 else 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · simp [sign_neg hx, sign_neg hy, le_of_lt (mul_pos_of_neg_of_neg hx hy)]
  · simp [sign_neg hx, sign_pos hy, mul_neg_of_neg_of_pos hx hy]
  · simp [sign_pos hx, sign_neg hy, mul_neg_of_pos_of_neg hx hy]
  · simp [sign_pos hx, sign_pos hy, le_of_lt (mul_pos hx hy)]

/-- Sign variations across a nonzero entry `t` sitting between `s` and `-s`: exactly one. -/
lemma signType_ite_add_ite (s t : SignType) (hs : s ≠ 0) (ht : t ≠ 0) :
    (if s = t then (0 : ℕ) else 1) + (if t = -s then 0 else 1) = 1 := by
  revert hs ht; revert s t; decide

section RealPoly

open Polynomial

theorem termination_sturmSeq {α : Type*} [Field α] [DecidableEq α] (f g : Polynomial α) (hf : f ≠ 0) :
    (if g = 0 then 0 else if -f % g = 0 then 1 else 2 + (-f % g).natDegree) <
    if f = 0 then 0 else if g = 0 then 1 else 2 + g.natDegree := by
  rw [if_neg hf]
  by_cases hg : g = 0
  · simp [hg]
  rw [if_neg hg, if_neg hg]
  by_cases hmod : -f % g = 0
  · rw [if_pos hmod]; omega
  rw [if_neg hmod]
  -- a nonzero constant divides everything, so `g` is not constant
  have hdeg : g.natDegree ≠ 0 := by
    intro h0
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp h0
    have hc : c ≠ 0 := by rintro rfl; simp at hg
    exact hmod (EuclideanDomain.mod_eq_zero.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd)
  have := natDegree_mod_lt (-f) hdeg
  omega

noncomputable def sturmSeq {α : Type*} [Field α] [DecidableEq α] (f g : Polynomial α) : List (Polynomial α) :=
  if f = 0 then
    []
  else
    f::(sturmSeq g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + natDegree g
  decreasing_by exact termination_sturmSeq f g (by assumption)

@[simp] lemma sturmSeq_zero {α : Type*} [Field α] [DecidableEq α] {q : Polynomial α} :
    sturmSeq 0 q = [] := by simp [sturmSeq]

lemma sturmSeq_cons {α : Type*} [Field α] [DecidableEq α] {p q : Polynomial α} (hp : p ≠ 0) :
    sturmSeq p q = p :: sturmSeq q (-p % q) := by
  conv_lhs => unfold sturmSeq
  simp [hp]

lemma sturmSeq_eq_nil_iff {α : Type*} [Field α] [DecidableEq α] {p q : Polynomial α} :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro hs
    by_contra hp
    rw [sturmSeq_cons hp] at hs
    exact List.cons_ne_nil _ _ hs
  · rintro rfl
    exact sturmSeq_zero

@[simp]
lemma sturmSeq_zero_right {α : Type*} [Field α] [DecidableEq α] (p : Polynomial α) :
    sturmSeq p 0 = if p = 0 then [] else [p] := by
  split_ifs with hp
  · exact sturmSeq_eq_nil_iff.mpr hp
  · rw [sturmSeq_cons hp, sturmSeq_zero]

lemma mem_sturmSeq_self {α : Type*} [Field α] [DecidableEq α] {p q : Polynomial α} (hp : p ≠ 0) :
    p ∈ sturmSeq p q := by
  rw [sturmSeq_cons hp]; exact List.mem_cons_self

lemma zero_notMem_sturmSeq {α : Type*} [Field α] [DecidableEq α] (p q : Polynomial α) : 0 ∉ sturmSeq p q := by
  induction p, q using sturmSeq.induct
  next q => simp [sturmSeq_zero]
  next p q hp ih =>
    rw [sturmSeq_cons hp]
    simp [Ne.symm hp, ih]

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
