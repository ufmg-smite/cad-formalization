import Cad

open CompPoly
open CPolynomial

namespace t1

def p : CPolynomial Rat := CPolynomial.X ^ 2 - 2
def r1 : AlgebraicNumber.Raw := .interval p 1.4 1.5
def a1 : AlgebraicNumber.AlgNum := by lift_alg_num r1
def r2 : AlgebraicNumber.Raw := .interval p (-1.49) (-1.4)
def a2 : AlgebraicNumber.AlgNum := by lift_alg_num r2

def b : Rat := 3/2

lemma l (x : Real) : x ^ 2 < 2 → x > 3/2 → False := by
  intros h1 h2
  univ_cad x, [h1, h2] [a2, a1, b]

#print axioms l

end t1

namespace t2

def a : Rat := -9
def b : Rat := 0
def c : Rat := 10

lemma ex1 (x : Real) (h1 : x ≥ -9) (h2 : x < 10) (h3 : x * x * x * x > 0) (h4: (x * x * x * x * x * x * x * x ≤ 0)) : False := by
  univ_cad x , [h1,h2,h3,h4] [a,b,c]

#print axioms ex1

end t2

namespace t3

def p2 : CPolynomial Rat := X - 3/2
def r3 : AlgebraicNumber.Raw := .interval p2 (7/5) 2
def R3 : AlgebraicNumber.AlgNum := by lift_alg_num r3

abbrev R3' : Rat := 3 / 2

def p1 : CPolynomial Rat := 10 • X ^ 2 + 2 • X + -15

def r1 : AlgebraicNumber.Raw := .interval p1 (-3/2) (-5/4)
def R1 : AlgebraicNumber.AlgNum := by lift_alg_num r1

def r2 : AlgebraicNumber.Raw := .interval p1 1 (5/4)
def R2 : AlgebraicNumber.AlgNum := by lift_alg_num r2

lemma exemplo (a : Real) (h1 : ¬ -1 * a ≥ -3 / 2) (h2 : a = 15 / 2 + -5 * (a * a)) : False := by
  univ_cad a, [h1, h2] [R1, R2, R3']

#print axioms exemplo

end t3

def zero_p : CPolynomial Rat := X
def zero_r : AlgebraicNumber.Raw := .interval zero_p (-1) 1
def zero : AlgebraicNumber.AlgNum := by lift_alg_num zero_r

example (x : Real) (h1 : x * x * x * x * x > 0) (h2 : x * x * x < 0) : False := by
  univ_cad x, [h1, h2] [zero]

namespace t4

-- Separating `zero` (isolating interval `(-1, 1)`) from the rational `1/2`
-- forces a refinement whose midpoint 0 is exactly the root, so the
-- representation collapses to the rational 0 inside the tactic pipeline.
def half : Rat := 1/2

example (x : Real) (h1 : x ≥ 1/2) (h2 : x * x * x ≤ 0) : False := by
  univ_cad x, [h1, h2] [zero, half]

end t4
