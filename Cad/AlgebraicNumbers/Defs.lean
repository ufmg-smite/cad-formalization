import Mathlib
import Cad.DefinitionsOne

namespace Definitions

def CMonomial.qeval (m: CMonomial) (q: ℚ) : ℚ :=
  m.coef * q ^ m.exp

def CPolynomial.qeval (p: CPolynomial) (q: ℚ) : ℚ :=
  p.foldr (fun m acc => m.qeval q + acc) 0

-- TODO (TOMAZ): do we need both?
def CMonomial.reval (m: CMonomial) (q: ℝ) : ℝ :=
  m.coef * q ^ m.exp

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

-- The root of `p` in the interval `(l, r)`
structure AlgebraicNumber where
  p: CPolynomial
  l: Rat
  r: Rat

abbrev 𝔸 := AlgebraicNumber

def AlgebraicNumber.wellDefined (a: 𝔸) : Prop :=
  let ⟨p, l, r⟩ := a
  ∃! x : Real, p.reval x = 0 ∧ l < x ∧ x < r

def degree (p : CPolynomial) : Nat :=
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
      ⟨coef1 + coef2, exp1⟩ :: add tl1 tl2
    else if exp1 < exp2 then
      have : p.length + tl2.length < p.length + q.length := by grind
      ⟨coef2, exp2⟩ :: add p tl2
    else
      have : tl1.length + q.length < p.length + q.length := by grind
      ⟨coef1, exp1⟩ :: add tl1 q
  termination_by p.length + q.length

def CPolynomial.neg (p: CPolynomial) : CPolynomial :=
  p.map (fun ⟨coef, exp⟩ => ⟨-coef, exp⟩)

def CPolynomial.sub (p q : CPolynomial) : CPolynomial := add p (neg q)

def CMonomial.mul (m : CMonomial) (p : CPolynomial) : CPolynomial :=
  let ⟨coef, exp⟩ := m
  match p with
  | [] => []
  | ⟨coef', exp'⟩ :: tl => ⟨coef * coef', exp + exp'⟩ :: mul m tl

-- TODO (Tomaz): Fast Fourier Transform to do this on O(n log n)
def CPolynomial.mul (p q : CPolynomial) : CPolynomial :=
  match p with
  | [] => []
  | m :: tl =>
    let p' := m.mul q
    let rest := mul tl q
    add p' rest

def CPolynomial.zero : CPolynomial := [⟨0, 0⟩]

def CPolynomial.divRem (p q : CPolynomial) : CPolynomial × CPolynomial :=
  let deg_p := degree p
  let deg_q := degree q
  if deg_q ≤ deg_p then
    let lcoeff_p := leadingCoef p
    let lcoeff_q := leadingCoef q
    let z: CMonomial := ⟨lcoeff_p / lcoeff_q, deg_p - deg_q⟩
    let r := divRem (sub p (z.mul q)) q
    ⟨add [z] r.1, r.2⟩
  else ⟨zero, q⟩
  termination_by degree p
  decreasing_by
    sorry


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
