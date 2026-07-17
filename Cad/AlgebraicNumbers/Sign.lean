import Lean
import Mathlib
import CompPoly
import Cad.AlgebraicNumbers.DeriveWellDefined
import Cad.Univariate.RootVal
import Cad.Univariate.SturmTarski.Decidable

open AlgebraicNumber
open CompPoly

lemma represents_refineN (α : AlgNum) (x : ℝ) (hx : α.val.represents x) (n : ℕ) :
    (AlgNum.refine^[n] α).val.represents x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Raw.refine_represents _ (AlgNum.refine^[n] α).prop.1 (AlgNum.refine^[n] α).prop.2 ih

lemma root_in_refineN (α : AlgNum) (x : ℝ) (hx : α.val.represents x) (n : ℕ) :
    ↑(AlgNum.refine^[n] α).l ≤ x ∧ x ≤ ↑(AlgNum.refine^[n] α).r :=
  Raw.represents_bounds (represents_refineN α x hx n)

lemma toReal_in_refineN (α : AlgNum) (n : ℕ) :
    ↑(AlgNum.refine^[n] α).l ≤ α.toReal ∧ α.toReal ≤ ↑(AlgNum.refine^[n] α).r := by
  have key : α.toReal = (AlgNum.refine^[n] α).toReal := by
    induction n with
    | zero => simp
    | succ n ih => rw [ih, Function.iterate_succ', Function.comp, refine_toReal]
  rw [key]
  exact toReal_bounds _

lemma wellDefined_root (α : AlgNum) (x : ℝ) (hx : α.val.represents x) : α.toReal = x := by
  by_contra hne
  have hne' : α.toReal - x ≠ 0 := sub_ne_zero.mpr hne
  have habs_pos : |α.toReal - x| > 0 := abs_pos.mpr hne'
  have hlr := α.lr
  have hwidth_nn : (0 : ℝ) ≤ (↑α.r : ℝ) - ↑α.l := by
    have : (↑α.l : ℝ) ≤ ↑α.r := by exact_mod_cast hlr
    linarith
  suffices ∀ n : ℕ, |α.toReal - x| ≤ ((↑α.r : ℝ) - ↑α.l) / 2 ^ n by
    rcases eq_or_lt_of_le hwidth_nn with heq | hlt
    · specialize this 0
      simp only [pow_zero, div_one] at this
      linarith [heq.symm]
    · have hdiv_pos : 0 < |α.toReal - x| / ((↑α.r : ℝ) - ↑α.l) := div_pos habs_pos hlt
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hdiv_pos (show (1:ℝ)/2 < 1 by norm_num)
      have h := this N
      have h2pos : (0 : ℝ) < 2 ^ N := pow_pos (by norm_num : (0:ℝ) < 2) N
      have key : ((↑α.r : ℝ) - ↑α.l) / 2 ^ N < |α.toReal - x| := by
        have hmul := mul_lt_mul_of_pos_left hN hlt
        rw [mul_div_cancel₀ _ (ne_of_gt hlt)] at hmul
        rwa [one_div, inv_pow, ← div_eq_mul_inv] at hmul
      linarith
  intro n
  have h_toReal := toReal_in_refineN α n
  have h_x : ↑(AlgNum.refine^[n] α).l ≤ x ∧ x ≤ ↑(AlgNum.refine^[n] α).r :=
    root_in_refineN α x hx n
  have h_width := refineN_width α n
  have h_width_real : (↑(AlgNum.refine^[n] α).r : ℝ) - ↑(AlgNum.refine^[n] α).l ≤
      ((↑α.r : ℝ) - ↑α.l) / 2 ^ n := by
    exact_mod_cast h_width
  rw [abs_le]
  constructor <;> linarith [h_toReal.1, h_toReal.2, h_x.1, h_x.2]

lemma toReal_root (α : AlgNum) : (toPolyReal α.p).eval α.toReal = 0 := by
  obtain ⟨x, hx_rep, -⟩ := α.isWellDefined
  rw [wellDefined_root α x hx_rep]
  exact Raw.represents_root hx_rep

lemma toReal_in_rootsInInterval (α : AlgNum) (hpl : α.p.eval α.l ≠ 0) (_hpr : α.p.eval α.r ≠ 0) :
    α.toReal ∈ rootsInInterval (toPolyReal α.p) α.l α.r := by
  obtain ⟨x, hx_rep, -⟩ := α.isWellDefined
  have hxr := wellDefined_root α x hx_rep
  have hstrict : ((α.l : ℝ) < x ∧ x < (α.r : ℝ)) := Raw.represents_strict hx_rep hpl
  simp [toPolyReal, rootsInInterval]
  refine And.intro (And.intro ?_ ?_) (And.intro ?_ ?_)
  · intro abs
    have : α.p = 0 := poly_eq0_of_toPoly_eq0 α.p abs
    rw [this] at hpl
    exact false_of_ne hpl
  · exact toReal_root α
  · rw [hxr]
    exact hstrict.1
  · rw [hxr]
    exact hstrict.2

lemma toReal_only_root (α : AlgNum) (hpl: α.p.eval α.l ≠ 0) (hpr: α.p.eval α.r ≠ 0) :
    rootsInInterval (toPolyReal α.p) α.l α.r = {α.toReal} := by
  set S := rootsInInterval (toPolyReal α.p) α.l α.r
  have h1 : α.toReal ∈ S := toReal_in_rootsInInterval α hpl hpr
  have h2 : ∀ y ∈ S, y = α.toReal := by
    intros y hy
    simp [S, rootsInInterval] at hy
    obtain ⟨⟨_, h_root⟩, ⟨hyl, hyr⟩⟩ := hy
    have hrep : α.val.represents y := Raw.represents_of_root h_root hyl hyr
    exact (wellDefined_root α y hrep).symm
  grind

lemma sgn_eval_alg (q : CPolynomial Rat) (α : AlgNum) (hpl: α.p.eval α.l ≠ 0) (hpr: α.p.eval α.r ≠ 0) :
    sgn ((toPolyReal q).eval α.toReal) =
    ∑ x ∈ rootsInInterval (toPolyReal α.p) α.l α.r, sgn ((toPolyReal q).eval x) := by
  rw [toReal_only_root α hpl hpr]
  simp

lemma AlgNum.lr' (α : AlgNum) (hl : α.p.eval α.l ≠ 0) : α.l < α.r := by
  obtain ⟨x, hx_rep, -⟩ := α.isWellDefined
  have hstrict := Raw.represents_strict hx_rep hl
  have : (α.l : ℝ) < (α.r : ℝ) := lt_trans hstrict.1 hstrict.2
  exact_mod_cast this

lemma sgn_eval_alg_sturm_seq (q : CPolynomial Rat) (α : AlgNum) (hpl: α.p.eval α.l ≠ 0) (hpr: α.p.eval α.r ≠ 0) :
    sgn ((toPolyReal q).eval α.toReal) = seqVarSturmC_ab' α.p (α.p.derivative * q) α.l α.r := by
  rw [sgn_eval_alg q α hpl hpr]
  have :
    ∑ x ∈ rootsInInterval (toPolyReal α.p) ↑α.l ↑α.r, sgn (Polynomial.eval x (toPolyReal q)) =
    tarskiQuery (toPolyReal α.p) (toPolyReal q) α.l α.r := by simp [tarskiQuery]
  rw [this, cauchyIndex_poly_taq, <- cauchyIndex_sturmSeq]
  · rw [<- seqVarABEquivSturm α.p q α.l α.r]
    exact seqVarSturmC_ab_equiv α.p (α.p.derivative * q) α.l α.r
  · rw [CPolynomial.eval_toPoly, <- (Rat.cast_ne_zero (α := Real)), eval_comm_map] at hpl
    exact hpl
  · rw [CPolynomial.eval_toPoly, <- (Rat.cast_ne_zero (α := Real)), eval_comm_map] at hpr
    exact hpr
  · have := AlgNum.lr' α hpl
    exact Real.ratCast_lt.mpr this

open Qq Lean Elab Tactic Meta

syntax (name := compute_sign) "compute_sign" term "," term : tactic

lemma minus_one (a : Int) : a = -1 → a < 0 := by
  intro h
  simp_all only [Int.reduceNeg, Int.neg_neg_iff_pos, zero_lt_one]

lemma plus_one (a : Int) : a = 1 → a > 0 := by
  intro h
  positivity

lemma eval_neg (a : Rat) (p : CPolynomial Rat) (h_eval : p.eval a < 0) : (toPolyReal p).eval (ratToReal a) < 0 := by
  unfold toPolyReal ratToReal
  rw [CPolynomial.eval_toPoly] at h_eval
  have : (↑(p.toPoly.eval a) : Real) < 0 := by simp_all only [Rat.cast_lt_zero]
  rw [eval_comm_map] at this
  unfold ratToRealHom at this ⊢
  finiteness

lemma eval_zero (a : Rat) (p : CPolynomial Rat) (h_eval : p.eval a = 0) : (toPolyReal p).eval (ratToReal a) = 0 := by
  unfold toPolyReal ratToReal
  rw [CPolynomial.eval_toPoly] at h_eval
  have : (↑(p.toPoly.eval a) : Real) = 0 := by simp_all only [Rat.cast_zero]
  rw [eval_comm_map] at this
  unfold ratToRealHom at this ⊢
  finiteness

lemma eval_pos (a : Rat) (p : CPolynomial Rat) (h_eval : p.eval a > 0) : (toPolyReal p).eval (ratToReal a) > 0 := by
  unfold toPolyReal ratToReal
  rw [CPolynomial.eval_toPoly] at h_eval
  have : (↑(p.toPoly.eval a) : Real) > 0 := by positivity
  rw [eval_comm_map] at this
  unfold ratToRealHom at this ⊢
  finiteness

/- Sign computation for an `AlgNum` whose interval collapsed to a rational
(`Raw.rat`, characterized by `l = r`): just evaluate at that rational. -/

lemma eval_neg_alg_rat (p : CPolynomial Rat) (α : AlgNum) (h : α.l = α.r)
    (h_eval : p.eval α.l < 0) : (toPolyReal p).eval α.toReal < 0 := by
  rw [AlgNum.toReal_of_l_eq_r α h]
  exact eval_neg α.l p h_eval

lemma eval_zero_alg_rat (p : CPolynomial Rat) (α : AlgNum) (h : α.l = α.r)
    (h_eval : p.eval α.l = 0) : (toPolyReal p).eval α.toReal = 0 := by
  rw [AlgNum.toReal_of_l_eq_r α h]
  exact eval_zero α.l p h_eval

lemma eval_pos_alg_rat (p : CPolynomial Rat) (α : AlgNum) (h : α.l = α.r)
    (h_eval : p.eval α.l > 0) : (toPolyReal p).eval α.toReal > 0 := by
  rw [AlgNum.toReal_of_l_eq_r α h]
  exact eval_pos α.l p h_eval

def getSignProof (p : Q(CPolynomial Rat)) (p_native : CPolynomial Rat) (a : RootVal) : MetaM (Expr × Int) := do
  match a with
  | .rat ea va =>
    let ea : Q(Rat) := ea
    let val := sgnC (p_native.eval va)
    let pf ← do
      if val < 0 then
        let goal := q(CPolynomial.eval $ea $p < 0)
        let pf_rat ← mkDecideProof goal
        mkAppM ``eval_neg #[ea, p, pf_rat]
      else if val = 0 then
        let goal := q(CPolynomial.eval $ea $p = 0)
        let pf_rat ← mkDecideProof goal
        mkAppM ``eval_zero #[ea, p, pf_rat]
      else
        let goal := q(CPolynomial.eval $ea $p > 0)
        let pf_rat ← mkDecideProof goal
        mkAppM ``eval_pos #[ea, p, pf_rat]
    return (pf, val)
  | .alg (ea : Q(AlgNum)) va =>
    match va with
    | .rat v =>
      -- the isolating interval collapsed to a rational: evaluate directly
      let hlr : Q(Prop) := q(AlgNum.l $ea = AlgNum.r $ea)
      let pf_lr ← mkDecideProof hlr
      let val := sgnC (p_native.eval v)
      let pf ← do
        if val < 0 then
          let goal := q(CPolynomial.eval (AlgNum.l $ea) $p < 0)
          let pf_rat ← mkDecideProof goal
          mkAppM ``eval_neg_alg_rat #[p, ea, pf_lr, pf_rat]
        else if val = 0 then
          let goal := q(CPolynomial.eval (AlgNum.l $ea) $p = 0)
          let pf_rat ← mkDecideProof goal
          mkAppM ``eval_zero_alg_rat #[p, ea, pf_lr, pf_rat]
        else
          let goal := q(CPolynomial.eval (AlgNum.l $ea) $p > 0)
          let pf_rat ← mkDecideProof goal
          mkAppM ``eval_pos_alg_rat #[p, ea, pf_lr, pf_rat]
      return (pf, val)
    | .interval _ _ _ =>
      let h1 : Q(Prop) := q(«$ea».p.eval «$ea».l ≠ 0)
      let p1 : Q($h1) ← mkDecideProof h1
      let h2 : Q(Prop) := q(«$ea».p.eval «$ea».r ≠ 0)
      let p2 : Q($h2) ← mkDecideProof h2
      let sign_sturm_pf := q(sgn_eval_alg_sturm_seq $p $ea $p1 $p2)
      let sign : Int := seqVarSturmC_ab' va.p (va.p.derivative * p_native) va.l va.r
      let sign_eq : Q(Prop) := q(seqVarSturmC_ab' «$ea».p («$ea».p.derivative * $p) «$ea».l «$ea».r = $sign)
      let sign_reflection ← mkDecideProof sign_eq
      let sign_pf : Q(sgn ((toPolyReal $p).eval «$ea».toReal) = $sign) ← mkAppM ``Eq.trans #[sign_sturm_pf, sign_reflection]
      if sign = -1 then
        let sign_neg_pf : Q(sgn ((toPolyReal $p).eval «$ea».toReal) < 0) ← mkAppM ``minus_one #[q(sgn ((toPolyReal $p).eval «$ea».toReal)), sign_pf]
        return (q((sgn_sgn_neg ((toPolyReal $p).eval «$ea».toReal)).mp $sign_neg_pf), sign)
      else if sign = 0 then
        let sign_pf : Q(sgn ((toPolyReal $p).eval «$ea».toReal) = 0) := sign_pf
        return (q((sgn_sgn_zero ((toPolyReal $p).eval «$ea».toReal)).mp $sign_pf), sign)
      else
        let sign_pos_pf : Q(sgn ((toPolyReal $p).eval «$ea».toReal) > 0) ← mkAppM ``plus_one #[q(sgn ((toPolyReal $p).eval «$ea».toReal)), sign_pf]
        return (q((sgn_sgn_pos ((toPolyReal $p).eval «$ea».toReal)).mp $sign_pos_pf), sign)

@[tactic compute_sign] def evalComputeSign : Tactic := fun stx => withMainContext do
  let p : Q(CPolynomial Rat) ← elabTerm stx[1] none
  let p_native ← unsafe evalExpr (CPolynomial Rat) q(CPolynomial Rat) p
  let a ← elabTerm stx[3] none
  let ta ← inferType a
  let v ← if ta == .const ``AlgNum [] then
    let a : Q(AlgNum) := a
    getSignProof p p_native (.alg a (← unsafe evalExpr Raw q(Raw) q(Subtype.val $a)))
  else
    let a : Q(Rat) := a
    getSignProof p p_native (.rat a (← unsafe evalExpr Rat q(Rat) a))
  closeMainGoal .anonymous v.1

namespace tests_sgn

open CPolynomial in
def P1 : CPolynomial Rat := X ^ 3 - 3 * X ^ 2 + X - 5

open CPolynomial in
def Q : CPolynomial Rat := X ^ 2 - 2
def r : Raw := .interval Q 1 2
def α : AlgNum := by lift_alg_num r -- sqrt(2)

example : (toPolyReal P1).eval α.toReal < 0 := by
  compute_sign P1 , α

open CPolynomial in
def P2 : CPolynomial Rat := X ^ 3 - 3 * X ^ 2 + X + 5

example : (toPolyReal P2).eval α.toReal > 0 := by
  compute_sign P2 , α

example : (toPolyReal Q).eval α.toReal = 0 := by
  compute_sign Q , α

def r1 : Rat := 27 / 3
example : (toPolyReal Q).eval (ratToReal r1) > 0 := by
  compute_sign Q , r1

def Pr : CPolynomial Rat := 2 * CPolynomial.X - 3
def r2 : Rat := 3 / 2

example : (toPolyReal Pr).eval (ratToReal r2) = 0 := by
  compute_sign Pr , r2

-- an AlgNum whose refinement collapses to the exact rational root
def Px : CPolynomial Rat := CPolynomial.X
def rzero : Raw := .interval Px (-1) 1
def zero : AlgNum := by lift_alg_num rzero

example : (toPolyReal Pr).eval zero.refine.toReal < 0 := by
  compute_sign Pr , zero.refine

example : (toPolyReal Px).eval zero.refine.toReal = 0 := by
  compute_sign Px , zero.refine

end tests_sgn
