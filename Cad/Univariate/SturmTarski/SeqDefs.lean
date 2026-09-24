import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.SignVariations
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Sign.Basic

open SignType

/-! ### Facts about `SignType.sign` -/

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

section SturmSeq

open Polynomial

variable {α : Type*} [Field α]

theorem mul_mod_mul_left (p q r : Polynomial α) (hr : r ≠ 0) :
    (r * p) % (r * q) = r * (p % q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have h1 : (r * p) % (r * q) = (r * (p % q)) % (r * q) :=
      mod_eq_of_dvd_sub ⟨p / q, by rw [← mul_sub, EuclideanDomain.mod_eq_sub_mul_div]; ring⟩
    rw [h1, mod_eq_self_iff (mul_ne_zero hr hq), degree_mul, degree_mul]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hr) (degree_mod_lt p hq)

lemma mod_minus (p q : Polynomial α) : -p % q = -(p % q) := by
  rw [mod_def, mod_def, neg_modByMonic]

variable [DecidableEq α]

theorem termination_sturmSeq (f g : Polynomial α) (hf : f ≠ 0) :
    (if g = 0 then 0 else if -f % g = 0 then 1 else 2 + (-f % g).natDegree) <
    if f = 0 then 0 else if g = 0 then 1 else 2 + g.natDegree := by
  rw [ite_eq_right hf]
  by_cases hg : g = 0
  · simp [hg]
  rw [ite_eq_right hg, ite_eq_right hg]
  by_cases hmod : -f % g = 0
  · rw [ite_eq_left hmod]; omega
  rw [ite_eq_right hmod]
  -- a nonzero constant divides everything, so `g` is not constant
  have hdeg : g.natDegree ≠ 0 := by
    intro h0
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp h0
    have hc : c ≠ 0 := by rintro rfl; simp at hg
    exact hmod (EuclideanDomain.mod_eq_zero.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd)
  have := natDegree_mod_lt (-f) hdeg
  omega

noncomputable def sturmSeq (f g : Polynomial α) : List (Polynomial α) :=
  if f = 0 then
    []
  else
    f::(sturmSeq g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + natDegree g
  decreasing_by exact termination_sturmSeq f g (by assumption)

@[simp] lemma sturmSeq_zero {q : Polynomial α} :
    sturmSeq 0 q = [] := by simp [sturmSeq]

lemma sturmSeq_cons {p q : Polynomial α} (hp : p ≠ 0) :
    sturmSeq p q = p :: sturmSeq q (-p % q) := by
  conv_lhs => unfold sturmSeq
  simp [hp]

lemma sturmSeq_eq_nil_iff {p q : Polynomial α} :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro hs
    by_contra hp
    rw [sturmSeq_cons hp] at hs
    exact List.cons_ne_nil _ _ hs
  · rintro rfl
    exact sturmSeq_zero

@[simp]
lemma sturmSeq_zero_right (p : Polynomial α) :
    sturmSeq p 0 = if p = 0 then [] else [p] := by
  split_ifs with hp
  · exact sturmSeq_eq_nil_iff.mpr hp
  · rw [sturmSeq_cons hp, sturmSeq_zero]

lemma mem_sturmSeq_self {p q : Polynomial α} (hp : p ≠ 0) :
    p ∈ sturmSeq p q := by
  rw [sturmSeq_cons hp]; exact List.mem_cons_self

lemma zero_notMem_sturmSeq (p q : Polynomial α) : 0 ∉ sturmSeq p q := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons hp]
    simp [Ne.symm hp, ih]

/-- The first entry of the Sturm sequence of a nonzero polynomial is the polynomial itself. -/
lemma head?_sturmSeq {p : Polynomial α} (hp : p ≠ 0) (q : Polynomial α) :
    (sturmSeq p q).head? = some p := by
  rw [sturmSeq_cons hp, List.head?_cons]

/-- Every common divisor of `p` and `q` divides every entry of their Sturm sequence. In
particular this holds for `gcd p q`. -/
lemma dvd_of_mem_sturmSeq {d p q s : Polynomial α} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  induction p, q using sturmSeq.induct
  next q => simp at hs
  next p q hp0 ih =>
    rw [sturmSeq_cons hp0, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hp
    · exact ih hq ((EuclideanDomain.dvd_mod_iff hq).mpr (dvd_neg.mpr hp)) hs

/-- Multiplying both arguments by a nonzero polynomial multiplies every entry of the Sturm
sequence by it. -/
lemma sturmSeq_mul_left {r : Polynomial α} (hr : r ≠ 0) (p q : Polynomial α) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons (mul_ne_zero hr hp), sturmSeq_cons hp, List.map_cons, mod_minus,
      mul_mod_mul_left _ _ _ hr, ← mul_neg, ← mod_minus, ih]

end SturmSeq

section RealPolynomial

open Polynomial

noncomputable def signPosInf (p : Polynomial ℝ) : SignType :=
  sign p.leadingCoeff

noncomputable def signNegInf (p : Polynomial ℝ) : SignType :=
  if Even p.natDegree then sign p.leadingCoeff else - sign p.leadingCoeff

noncomputable def seqSignPosInf :
    List (Polynomial ℝ) → List SignType := List.map (fun x => signPosInf x)

noncomputable def seqSignNegInf :
    List (Polynomial ℝ) → List SignType := List.map (fun x => signNegInf x)

def seqEval {α : Type*} [Semiring α] (k : α) : List (Polynomial α) → List α := List.map (eval k)

noncomputable def seqEvalSign (k : ℝ) :
    List (Polynomial ℝ) → List SignType := List.map (fun a => sign (eval k a))

noncomputable def signVariationsAb (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (List.signVariations (seqEval a P) : ℤ) - List.signVariations (seqEval b P)

noncomputable def signVariationsSturmAb (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  signVariationsAb (sturmSeq p q) a b

noncomputable def signVariationsAboveA (P: List (Polynomial ℝ)) (a : ℝ) : ℤ :=
  (List.signVariations (seqEval a P) : ℤ) - List.signVariations (seqSignPosInf P)

noncomputable def signVariationsBelowB (P: List (Polynomial ℝ)) (b : ℝ) : ℤ :=
  (List.signVariations (seqSignNegInf P) : ℤ) - List.signVariations (seqEval b P)

noncomputable def signVariationsLine (P : List (Polynomial ℝ)) : ℤ :=
  (List.signVariations (seqSignNegInf P) : ℤ) - List.signVariations (seqSignPosInf P)

noncomputable def signVariationsAboveSturm (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  signVariationsAboveA (sturmSeq p q) a

noncomputable def signVariationsBelowSturm (p q : Polynomial ℝ) (b : ℝ) : ℤ :=
  signVariationsBelowB (sturmSeq p q) b

noncomputable def signVariationsLineSturm (p q : Polynomial ℝ) : ℤ  :=
  signVariationsLine (sturmSeq p q)

end RealPolynomial
