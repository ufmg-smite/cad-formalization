import Mathlib
import Cad.SturmBasu.SturmSeq
import Cad.SturmBasu.Utils
import CompPoly
import Cad.SturmBasu.Theorem
open Polynomial

open CompPoly
open CPolynomial
open Theorem
noncomputable def toPolyReal (p : CPolynomial Rat) : Polynomial Real := p.toPoly.map (Rat.castHom Real)

open CompPoly in
lemma toPolyReal_zero (p : CPolynomial Rat) : p ≠ 0 → toPolyReal p ≠ 0 := by
  intros h
  exact Polynomial.map_ne_zero (gneg_imp_gtopoly_neg p h)

lemma toPolyReal_ne_zero : toPolyReal 0 = 0 := by
  rw[toPolyReal]
  simp only [CPolynomial.toPoly_zero, Polynomial.map_zero]

--#check eval_comm_map_real

lemma eval_comm_map_real (p : Polynomial ℚ) (l : ℚ) : ((p.eval l : ℚ) : Real) = (p.map (Rat.castHom ℝ)).eval ((l : ℚ) : Real) := by

  sorry

-- Helper: polynomial evaluation commutes with casting
lemma poly_eval_cast (p : Polynomial ℚ) (x : ℚ) : ((p.eval x : ℚ) : Real) = (p.map (Rat.castHom ℝ)).eval ((x : ℚ) : Real) :=
  eval_comm_map_real p x

-- Helper lemma: sign is preserved under Rat to Real casting
lemma sgn_rat_cast (r : ℚ) : sgn ((r : ℝ)) = sgn r := by
  unfold sgn
  split_ifs <;> decide

-- Map Rat to Real preserves evaluations in list form
lemma seqEval_toPolyReal_helper (k : ℚ) (ps : List (CPolynomial ℚ)) :
    seqEval ((k : ℝ)) (List.map toPolyReal ps) =
    List.map (fun (x : ℚ) => (x : ℝ)) (seqEval_CPolynomial k ps) := by
  induction ps with
  | nil => rfl
  | cons p ps IH =>
    unfold seqEval seqEval_CPolynomial toPolyReal
    simp only [List.map_cons]
    congr 1
    · have hp := CPolynomial.eval_toPoly k p
      simp only [hp]
      exact (poly_eval_cast p.toPoly k).symm

-- seqVarSturm_ab_CPolynomial p (CPolynomial.derivative (p) * q) a b = seqVarSturm_ab_Rat p.toPoly (derivative p.toPoly * q.toPoly) a b := by
theorem equiv_for_Realsturm_tarski_interval (a b : ℚ) (p q : CPolynomial ℚ) :
    seqVarSturm_ab_CPolynomial p (CPolynomial.derivative (p) * q) a b = seqVarSturm_ab (toPolyReal p) ((toPolyReal p).derivative * (toPolyReal q)) a b := by
  rw[seqVarSturm_ab_CPolynomial, seqVar_ab_CPolynomial, seqEval_CPolynomial.eq_def, sturmSeq_CPolynomial]--
  rw[seqVarSturm_ab, sturmSeq, seqVar_ab, seqEval.eq_def]

  if h : p = 0 then
    have : toPolyReal p = 0 := by
      rw[h];
      apply toPolyReal_ne_zero
    simp_all
    rw[seqEval_CPolynomial, seqEval]; simp_all
  else
    have : ¬ toPolyReal p = 0 := by
      apply toPolyReal_zero p h
    simp_all
    let k := (CPolynomial.eval a p)
    have : (k : Real)= (Polynomial.eval (a:Real) (toPolyReal p)) := by
      unfold k
      have := CPolynomial.eval_toPoly a p
      rw[this]
      unfold toPolyReal
      exact poly_eval_cast p.toPoly a

    rw[← this]; unfold k

    sorry
  --  simp only [derivative_equiv]
  --  simp only [seq_eval_equiv]
  --  have : -p.toPoly % (p.derivative * q).toPoly = (-p % (p.derivative*q)).toPoly := by
  --    have : (-p % (p.derivative * q)).toPoly = (toPoly (-p)) % (toPoly (p.derivative * q))  := by
  --      apply fg_mod_eq
  --    simp_all
  --    have : (-p).toPoly = -p.toPoly := by apply CPolynomial.toPoly_neg
  --    simp_all
  --  simp_all
  --  simp only [sturm_seq_equiv]
  --  have : toPolyList (p :: sturmSeq_CPolynomial (p.derivative * q) (-p % (p.derivative * q))) = p.toPoly::toPolyList (sturmSeq_CPolynomial (p.derivative * q) (-p % (p.derivative * q))) := by
  --    rw[toPolyList]
  --  simp_all
  --sorry
