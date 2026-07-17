import Lean
import Mathlib
import CompPoly
import Cad.AlgebraicNumbers.AlgNum
import Cad.Univariate.SturmTarski.Decidable

open Qq Lean Elab Tactic Meta
open CompPoly
open AlgebraicNumber

/-
This file defines a metaprogram that receives the data of an algebraic number
(`AlgebraicNumber.Raw`) and lifts it into an `AlgNum`, assuming it is well defined.
-/

theorem wellDefined_iff_rootsInInterval (p : CPolynomial ℚ) (l r : ℚ)
    (hp : p.toPoly.map ratToRealHom ≠ 0) :
    (Raw.interval p l r).wellDefined ↔
      Finset.card (rootsInInterval (p.toPoly.map ratToRealHom) ↑l ↑r) = 1 := by
  have mem_iff : ∀ x : ℝ, x ∈ rootsInInterval (p.toPoly.map ratToRealHom) ↑l ↑r ↔
      (Raw.interval p l r).represents x := by
    intro x
    simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots',
      Polynomial.IsRoot.def, Set.mem_Ioo, Raw.represents_interval, toPolyReal]
    constructor
    · rintro ⟨⟨-, hroot⟩, h1, h2⟩
      exact ⟨hroot, h1, h2⟩
    · rintro ⟨hroot, h1, h2⟩
      exact ⟨⟨hp, hroot⟩, h1, h2⟩
  unfold Raw.wellDefined
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨x, hx, hx_unique⟩
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_singleton, mem_iff]
    constructor
    · intro hy
      exact hx_unique y hy
    · rintro rfl
      exact hx
  · rintro ⟨x, hx_eq⟩
    have hx : (Raw.interval p l r).represents x :=
      (mem_iff x).mp (hx_eq ▸ Finset.mem_singleton_self x)
    refine ⟨x, hx, fun y hy => ?_⟩
    have hy_mem := (mem_iff y).mpr hy
    rw [hx_eq] at hy_mem
    exact Finset.mem_singleton.mp hy_mem

lemma sturm_l_r_cpoly (p : CPolynomial ℚ) (l r : ℚ) (hl : p.eval l ≠ 0) (hr : p.eval r ≠ 0) (hlr : l < r) :
    seqVarSturmC_ab' p p.derivative l r = (rootsInInterval (p.toPoly.map ratToRealHom) l r).card := by
  rw [<- seqVarSturmC_ab_equiv]
  have : p.derivative = p.derivative * 1 := by norm_num
  rw [this, seqVarABEquivSturm p 1]
  have hl0 : Polynomial.eval (↑l) (Polynomial.map ratToRealHom p.toPoly) ≠ 0 := by
    rw [<- cpolynomial_map_cast l p]
    finiteness
  have hr0 : Polynomial.eval (↑r) (Polynomial.map ratToRealHom p.toPoly) ≠ 0 := by
    rw [<- cpolynomial_map_cast r p]
    finiteness
  have sturm_l_r := Theorem.sturm_interval l r (p.toPoly.map ratToRealHom) (Real.ratCast_lt.mpr hlr) hl0 hr0
  have : (Polynomial.derivative (Polynomial.map ratToRealHom p.toPoly) * Polynomial.map ratToRealHom (CPolynomial.toPoly 1))
       = (Polynomial.derivative (Polynomial.map ratToRealHom p.toPoly)) := by
    rw [CPolynomial.toPoly_one, Polynomial.map_one ratToRealHom]
    norm_num
  unfold toPolyReal
  rw [this, sturm_l_r]

theorem Raw.sgnDiff_of_sgn (a : Raw) (hsgn : a.p.eval a.l * a.p.eval a.r < 0) : a.sgnDiff := by
  cases a with
  | rat x => trivial
  | interval p l r => exact hsgn

theorem Raw.wellDefined_of_sturm (a : Raw) (hlr : a.l < a.r)
    (hsgn : a.p.eval a.l * a.p.eval a.r < 0)
    (h_int : seqVarSturmC_ab' a.p a.p.derivative a.l a.r = 1) : a.wellDefined := by
  cases a with
  | rat x => exact absurd hlr (lt_irrefl x)
  | interval p l r =>
    have hlr' : l < r := hlr
    have hsgn' : p.eval l * p.eval r < 0 := hsgn
    have hl : p.eval l ≠ 0 := by
      intro h
      rw [h] at hsgn'
      simp at hsgn'
    have hr : p.eval r ≠ 0 := by
      intro h
      rw [h] at hsgn'
      simp at hsgn'
    have hp : p ≠ 0 := by
      intro h
      apply hl
      rw [h, CPolynomial.eval_toPoly, CPolynomial.toPoly_zero]
      simp
    have h0 : p.toPoly.map ratToRealHom ≠ 0 := Polynomial.map_ne_zero (toPoly_ne0_of_poly_ne0 p hp)
    have h_roots : Finset.card (rootsInInterval (p.toPoly.map ratToRealHom) ↑l ↑r) = 1 := by
      zify
      rw [<- sturm_l_r_cpoly p l r hl hr hlr']
      exact h_int
    exact (wellDefined_iff_rootsInInterval p l r h0).mpr h_roots

def AlgNum.mk
    (a : Raw)
    (hlr : a.l < a.r)
    (hsgn : a.p.eval a.l * a.p.eval a.r < 0)
    (h_int : seqVarSturmC_ab' a.p a.p.derivative a.l a.r = 1) : AlgNum :=
  ⟨a, And.intro (Raw.wellDefined_of_sturm a hlr hsgn h_int) (Raw.sgnDiff_of_sgn a hsgn)⟩

instance (a : Raw) : Decidable a.sgnDiff :=
  match a with
  | .rat _ => .isTrue trivial
  | .interval p l r => inferInstanceAs (Decidable (p.eval l * p.eval r < 0))

syntax (name := lift_alg_num) "lift_alg_num" term : tactic

def Raw.lift (r : Q(Raw)) : MetaM Q(AlgNum) := do
  let g1 : Q(Prop) := q((Raw.l $r) < (Raw.r $r))
  let pf1 : Q($g1) ← mkDecideProof g1
  let g2 : Q(Prop) := q((Raw.p $r).eval (Raw.l $r) * (Raw.p $r).eval (Raw.r $r) < 0)
  let pf2 : Q($g2) ← mkDecideProof g2
  let g3 : Q(Prop) := q(seqVarSturmC_ab' (Raw.p $r) (Raw.p $r).derivative (Raw.l $r) (Raw.r $r) = 1)
  let pf3 : Q($g3) ← mkDecideProof g3
  return q(AlgNum.mk $r $pf1 $pf2 $pf3)

@[tactic lift_alg_num] def evalLiftAlgNum : Tactic := fun stx => withMainContext do
  let r: Q(Raw) ← elabTerm stx[1] none
  let a: Q(AlgNum) ← Raw.lift r
  closeMainGoal .anonymous a

namespace tests

def p : CPolynomial Rat := CPolynomial.X + CPolynomial.C 1
def r : Raw := .interval p (-5) 5

-- <10*x^2 + 2*x + (-15), (-3/2, -5/4)>
open CPolynomial
def p' : CPolynomial Rat := (-15) + 3 * X + 10  * (X)^2
def r': Raw := .interval p' (-3/2) (-5/4)

def a : AlgNum := by lift_alg_num r
def a' : AlgNum := by lift_alg_num r'

end tests
