/- import Mathlib -/
import Cad.DefinitionsOne

namespace Definitions

structure Lawful (p: CPolynomial) where
  zeroFree : 0 ∉ p.map (fun m => m.coef)
  sorted : (p.map (fun m => m.exp)).SortedGT

theorem lawful_tl (hd : CMonomial) (tl : CPolynomial) : Lawful (hd :: tl) → Lawful tl := by
  intro h
  obtain ⟨h1, h2⟩ := h
  constructor
  · simp_all only [List.map_cons, List.mem_cons, List.mem_map, not_or, not_exists, not_and,
    not_false_eq_true, implies_true]
  · grind

def CMonomial.qeval (m: CMonomial) (q: ℚ) : ℚ :=
  m.coef * q ^ m.exp

def CPolynomial.qeval (p: CPolynomial) (q: ℚ) : ℚ :=
  p.foldr (fun m acc => m.qeval q + acc) 0

-- TODO (TOMAZ): do we need both?
def CMonomial.reval (m: CMonomial) (r: ℝ) : ℝ :=
  m.coef * r ^ m.exp

def CPolynomial.reval (p: CPolynomial) (r: ℝ) : ℝ :=
  p.foldr (fun m acc => m.reval r + acc) 0

-- the polynomial X
def p1 : CPolynomial := [⟨1, 1⟩]
#eval p1.qeval (13 /2) -- 13 / 2

-- the polynomial X^2
def p2 : CPolynomial := [⟨1, 2⟩]
#eval p2.qeval (13 / 2) -- 169 / 4

-- the polynomial X^2 - x + 5
def p3 : CPolynomial := [⟨1, 2⟩, ⟨-1, 1⟩, ⟨5, 0⟩]
#eval p3.qeval (13 / 2) -- 163 / 4

-- the polynomial X^2 - 2
def p4: CPolynomial := [⟨1, 2⟩, ⟨-2, 0⟩]
#eval p4.qeval (13 / 2) -- 161 / 4

-- X^2 - 1
def p5: CPolynomial := [⟨1, 2⟩, ⟨-1, 0⟩]

-- the polynomial X + 1
def p6 : CPolynomial := [⟨1, 1⟩, ⟨1, 0⟩]

@[simp]
def degree (p : CPolynomial) : WithBot Nat :=
  match p with
  | [] => none
  | ⟨_, exp⟩ :: _ => some exp

def natDegree (p: CPolynomial) : Nat :=
  match p with
  | [] => 0
  | ⟨_, exp⟩ :: _ => exp

def leadingCoef (p : CPolynomial) : ℚ :=
  match p with
  | [] => 0
  | ⟨coef, _⟩ :: _ => coef

def CPolynomial.add (p q : CPolynomial) : CPolynomial :=
  match h_match: (p, q) with
  | ([], q) => q
  | (p, []) => p
  | (⟨coef1, exp1⟩ :: tl1, ⟨coef2, exp2⟩ :: tl2) =>
    if exp1 = exp2 then
      have : tl1.length + tl2.length < p.length + q.length := by grind
      if coef1 + coef2 ≠ 0 then
        ⟨coef1 + coef2, exp1⟩ :: add tl1 tl2
      else add tl1 tl2
    else if exp1 < exp2 then
      have : p.length + tl2.length < p.length + q.length := by grind
      ⟨coef2, exp2⟩ :: add p tl2
    else
      have : tl1.length + q.length < p.length + q.length := by grind
      ⟨coef1, exp1⟩ :: add tl1 q
  termination_by p.length + q.length

lemma gt_of_sortedGT {α : Type*} [Preorder α] (hd : α) (tl : List α) (h : (hd :: tl).SortedGT) : ∀ x ∈ tl, x < hd := by
  intros x hx
  simp [List.SortedGT, StrictAnti] at h
  obtain ⟨i, hi⟩ : ∃ i : Fin tl.length, tl[i] = x := List.mem_iff_get.mp hx
  have : 0 < i.succ := by grind
  have := h this
  simp at this
  simp_all only [Fin.getElem_fin, Fin.succ_pos]

lemma sortedGT_of_gt {α : Type*} [Preorder α] (hd : α) (tl : List α) (h : tl.SortedGT) (hhd : ∀ x ∈ tl, x < hd) : (hd :: tl).SortedGT := by
  simp [List.SortedGT, StrictAnti] at h ⊢
  intros a b hab
  have : b ≠ 0 := Fin.ne_zero_of_lt hab
  if ha: a = 0 then
    simp [ha]
    rw [ha] at hab
    obtain ⟨c, hc⟩ : ∃ c : Fin tl.length, b = c.succ := by
      use b.pred this
      norm_num
    rw [hc]
    simp
    simp_all only [Fin.succ_pos, ne_eq, Fin.succ_ne_zero, not_false_eq_true, List.getElem_mem]
  else
    obtain ⟨c, hc⟩ : ∃ c : Fin tl.length, b = c.succ := by
      use b.pred this
      norm_num
    obtain ⟨d, hd⟩ : ∃ d : Fin tl.length, a = d.succ := by
      use a.pred ha
      norm_num
    rw [hc, hd]
    simp
    simp_all only [Fin.succ_lt_succ_iff, ne_eq, Fin.succ_ne_zero, not_false_eq_true]

lemma add_zeroFree (p q : CPolynomial) (hp : 0 ∉ p.map (fun m => m.coef)) (hq : 0 ∉ q.map (fun m => m.coef)) : 0 ∉ (p.add q).map (fun m => m.coef) := by
  cases p
  next =>
    cases q
    next => simp [CPolynomial.add]
    next hdq tlq =>
      simp [CPolynomial.add]
      grind
  next hdp tlp =>
    cases q
    next =>
      simp [CPolynomial.add]
      grind
    next hdq tlq =>
      have IH := add_zeroFree tlp tlq (by grind) (by grind)
      simp only [List.mem_map, not_exists, not_and] at IH
      unfold CPolynomial.add
      if heq: hdp.exp = hdq.exp then
        if hz: hdp.coef + hdq.coef = 0 then
          simp [heq, hz]
          exact IH
        else
          simp [heq, hz]
          exact And.symm ⟨IH, fun a => hz (Eq.symm a)⟩
      else if hlt: hdp.exp < hdq.exp then
        simp [heq, hlt]
        have IH2 := add_zeroFree (hdp :: tlp) tlq (by grind) (by grind)
        simp_all only [List.map_cons, List.mem_cons, List.mem_map, not_or, not_exists, not_and,
          not_false_eq_true, implies_true, and_self]
      else
        simp [heq, hlt]
        have IH2 := add_zeroFree tlp (hdq :: tlq) (by grind) (by grind)
        simp_all only [List.map_cons, List.mem_cons, List.mem_map, not_or, not_exists, not_and,
          not_lt, not_false_eq_true, implies_true, and_self]
  termination_by p.length + q.length

lemma gt_each_gt_add (m: CMonomial) (p q: CPolynomial) : (∀ m' ∈ p, m'.exp < m.exp) → (∀ m' ∈ q, m'.exp < m.exp) → ∀ m' ∈ (p.add q), m'.exp < m.exp := by
  cases p
  next =>
    intros h1 h2 m' hm'
    simp at h1
    simp [CPolynomial.add] at hm'
    exact h2 m' hm'
  next hdp tlp =>
    cases q
    next =>
      intros h1 h2 m' hm'
      simp at h1 h2
      simp [CPolynomial.add] at hm'
      grind
    next hdq tlq =>
      intros h1 h2 m' hm'
      have IH := gt_each_gt_add m tlp tlq (by grind) (by grind)
      unfold CPolynomial.add at hm'
      split_ifs at hm'
      next H =>
        simp at hm'
        cases hm'
        next hm' => simp_all only [List.mem_cons, forall_eq_or_imp, true_or, true_and, ne_eq]
        next hm' => exact (IH m' hm')
      next H =>
        simp at hm'
        exact (IH m' hm')
      next H =>
        simp at hm'
        cases hm'
        next hm' => simp_all only [List.mem_cons, forall_eq_or_imp]
        next hm' =>
          have IH' := gt_each_gt_add m (hdp :: tlp) tlq (by grind) (by grind)
          exact (IH' m' hm')
      next H =>
        simp at hm'
        cases hm'
        next hm' => simp_all only [List.mem_cons, forall_eq_or_imp]
        next hm' =>
          have IH' := gt_each_gt_add m tlp (hdq :: tlq) (by grind) (by grind)
          exact (IH' m' hm')

lemma add_sorted (p q : CPolynomial) (hp : (p.map (fun m => m.exp)).SortedGT) (hq : (q.map (fun m => m.exp)).SortedGT) : ((p.add q).map (fun m => m.exp)).SortedGT := by
  cases p
  next =>
    simp [CPolynomial.add, hq]
  next hdp tlp =>
    cases q
    next => simp only [CPolynomial.add, hp]
    next hdq tlq =>
      have : tlp.length + tlq.length < (hdp :: tlp).length + (hdq :: tlq).length := by grind
      have IH := add_sorted tlp tlq (by grind) (by grind)
      unfold CPolynomial.add
      if heq: hdp.exp = hdq.exp then
        if h_zero: hdp.coef + hdq.coef = 0 then
          simp [heq, h_zero]
          exact IH
        else
          simp [heq, h_zero]
          apply sortedGT_of_gt _ _ IH
          have hQ := gt_of_sortedGT _ _ hq
          have hP := gt_of_sortedGT _ _ hp
          simp at hP hQ
          rw [heq] at hP
          have := gt_each_gt_add _ _ _ hP hQ
          grind
      else if hlt: hdp.exp < hdq.exp then
        simp [heq, hlt]
        have : (hdp :: tlp).length + tlq.length < (hdp :: tlp).length + (hdq :: tlq).length := by grind
        have IH' := add_sorted (hdp :: tlp) tlq (by grind) (by grind)
        apply sortedGT_of_gt _ _ IH'
        have hQ := gt_of_sortedGT _ _ hq
        have hP := gt_of_sortedGT _ _ hp
        simp at hP hQ
        have : ∀ a ∈ (hdp :: tlp), a.exp < hdq.exp := by
          intros a ha
          simp only [List.mem_cons] at ha
          grind
        have := gt_each_gt_add _ _ _ this hQ
        grind
      else
        simp [heq, hlt]
        have : tlp.length + (hdq :: tlq).length < (hdp :: tlp).length + (hdq :: tlq).length := by grind
        have IH' := add_sorted tlp (hdq :: tlq) (by grind) (by grind)
        apply sortedGT_of_gt _ _ IH'
        have hQ := gt_of_sortedGT _ _ hq
        have hP := gt_of_sortedGT _ _ hp
        simp at hP hQ
        have : ∀ a ∈ (hdq :: tlq), a.exp < hdp.exp := by
          intros a ha
          simp only [List.mem_cons] at ha
          grind
        have := gt_each_gt_add _ _ _ hP this
        grind
  termination_by p.length + q.length

theorem add_lawful (p q : CPolynomial) (hp: Lawful p) (hq: Lawful q) : Lawful (p.add q) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  constructor
  · exact add_zeroFree p q hp1 hq1
  · exact add_sorted p q hp2 hq2

def CPolynomial.neg (p: CPolynomial) : CPolynomial :=
  p.map (fun ⟨coef, exp⟩ => ⟨-coef, exp⟩)

theorem neg_lawful (p : CPolynomial) (hp : Lawful p) : Lawful p.neg := by
  obtain ⟨hp1, hp2⟩ := hp
  constructor
  · simp at hp1
    simp [CPolynomial.neg]
    exact hp1
  · unfold CPolynomial.neg
    grind

def CPolynomial.sub (p q : CPolynomial) : CPolynomial := add p (neg q)

theorem sub_lawful (p q : CPolynomial) (hp : Lawful p) (hq : Lawful q) : Lawful (p.sub q) := by
  have h1 : Lawful q.neg := neg_lawful q hq
  unfold CPolynomial.sub
  exact add_lawful p q.neg hp h1

def CMonomial.mul (m : CMonomial) (p : CPolynomial) : CPolynomial :=
  let ⟨coef, exp⟩ := m
  match p with
  | [] => []
  | ⟨coef', exp'⟩ :: tl =>
    if coef * coef' ≠ 0 then
      ⟨coef * coef', exp + exp'⟩ :: mul m tl
    else mul m tl

lemma monom_mul_lawful' (m : CMonomial) (hd : CMonomial) (tl : CPolynomial) :
    (∀ x ∈ List.map (fun m => m.exp) tl, x < hd.exp) →
    ∀ x ∈ List.map (fun m => m.exp) (m.mul tl), x < m.exp + hd.exp := by
  cases tl
  next => simp [CMonomial.mul]
  next hd_tl tl_tl =>
    intro H
    simp at ⊢ H
    obtain ⟨H1, H2⟩ := H
    simp [CMonomial.mul]
    split_ifs
    next =>
      simp [H1]
      intros a ha
      have IH := monom_mul_lawful' m hd tl_tl (by grind)
      simp_all only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    next H' =>
      intros a ha
      have IH := monom_mul_lawful' m hd tl_tl (by grind)
      simp_all only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem monom_mul_lawful (m : CMonomial) (p : CPolynomial) (hm : m.coef ≠ 0) (hp : Lawful p) : Lawful (m.mul p) := by
  cases p
  next => simp [CMonomial.mul, hp]
  next hd tl =>
    obtain ⟨IH1, IH2⟩ := monom_mul_lawful m tl hm (lawful_tl _ _ hp)
    constructor
    · simp [CMonomial.mul, hm]
      if hz: hd.coef = 0 then
        simp [hz]
        simp only [List.mem_map, not_exists, not_and] at IH1
        exact IH1
      else
        simp [hz]
        constructor
        · exact hm
        · have IH := monom_mul_lawful m tl hm (lawful_tl _ _ hp)
          simp at IH1
          exact IH1
    · obtain ⟨_, hp2⟩ := hp
      unfold CMonomial.mul
      simp
      split_ifs
      next H =>
        simp only [List.map_cons]
        apply sortedGT_of_gt _ _ IH2
        simp at hp2
        have := gt_of_sortedGT _ _ hp2
        exact fun x a => monom_mul_lawful' m hd tl this x a
      next H =>
        exact StrictAnti.sortedGT IH2

-- TODO (Tomaz): Fast Fourier Transform to do this in O(n log n)
def CPolynomial.mul (p q : CPolynomial) : CPolynomial :=
  match p with
  | [] => []
  | m :: tl =>
    let p' := m.mul q
    let rest := mul tl q
    add p' rest

theorem mul_lawful (p q : CPolynomial) (hp : Lawful p) (hq : Lawful q) : Lawful (p.mul q) := by
  cases p
  next =>
    simp [CPolynomial.mul, hp]
  next hdp tlp =>
    simp [CPolynomial.mul]
    have IH := mul_lawful tlp q (lawful_tl _ _ hp) hq
    obtain ⟨hp1⟩ := hp
    simp at hp1
    have hdp_ne_zero : hdp.coef ≠ 0 := Ne.symm hp1.1
    have := monom_mul_lawful hdp q hdp_ne_zero hq
    exact add_lawful (hdp.mul q) (CPolynomial.mul tlp q) this IH

def CPolynomial.zero : CPolynomial := [⟨0, 0⟩]

lemma deg_decreases (p q : CPolynomial) (hzp : Lawful p) (hzq : Lawful q) (hp : none < degree p) : leadingCoef p = leadingCoef q → degree p = degree q → degree (p.sub q) < degree p := by
  intros h1 h2
  cases p
  next => simp at hp
  next hd_p tl_p =>
    cases q
    next =>
      simp at h2
    next hd_q tl_q =>
      have h_exp : hd_p.exp = hd_q.exp :=  ENat.coe_inj.mp h2
      have h_coef : hd_p.coef + -hd_q.coef = 0 := add_neg_eq_zero.mpr h1
      unfold CPolynomial.sub CPolynomial.neg CPolynomial.add
      simp [h_exp, h_coef]
      obtain ⟨_, H2⟩ := hzq
      have := gt_each_gt_add hd_q tl_p (List.map (fun x => CMonomial.mk (-x.coef) x.exp) tl_q) (by admit) (by admit)
      admit

unsafe def CPolynomial.divRem (p q : CPolynomial) : CPolynomial × CPolynomial :=
  let deg_p := degree p
  let deg_q := degree q
  if deg_q ≤ deg_p then
    let lcoeff_p := leadingCoef p
    let lcoeff_q := leadingCoef q
    let z: CMonomial := ⟨lcoeff_p / lcoeff_q, natDegree p - natDegree q⟩
    let r := divRem (sub p (z.mul q)) q
    ⟨add [z] r.1, r.2⟩
  else ⟨zero, q⟩
  /- termination_by degree p -/
  /- decreasing_by -/
  /-   sorry -/

#eval CPolynomial.divRem p5 p6


-- The root of `p` in the interval `(l, r)`
structure AlgebraicNumber where
  p: CPolynomial
  l: Rat
  r: Rat

abbrev 𝔸 := AlgebraicNumber

def AlgebraicNumber.wellDefined (a: 𝔸) : Prop :=
  let ⟨p, l, r⟩ := a
  ∃! x : Real, p.reval x = 0 ∧ l < x ∧ x < r

def toSeq (a: 𝔸) : ℕ → ℚ := fun n =>
  let ⟨p, l, r⟩ := a
  match n with
  | 0 => (l + r) / 2
  | n + 1 =>
    let m := (l + r) / 2
    let a' :=
      if p.qeval l * p.qeval m ≤ 0 then
        ⟨p, l, m⟩
      else
        ⟨p, m, r⟩
    toSeq a' n

theorem toSeq_cauchy : ∀ a: 𝔸, a.wellDefined → IsCauSeq abs (toSeq a) := by
  intros a ha
  simp [IsCauSeq]
  intro ε hε
  admit

-- approximates Real.sqrt 2
def s := toSeq ⟨p4, 1, 2⟩

-- casting to an actual real number
lemma hs : IsCauSeq abs s := sorry
noncomputable def sr : ℝ := Real.ofCauchy (CauSeq.Completion.mk ⟨s, hs⟩)

-- this is definitely possible using Sturm's theorem
instance (a: 𝔸) : Decidable a.wellDefined := sorry

def AlgebraicNumber.toReal (a: 𝔸): ℝ :=
  if h: a.wellDefined then Real.ofCauchy (CauSeq.Completion.mk ⟨toSeq a, toSeq_cauchy a h⟩) else 0

end Definitions
