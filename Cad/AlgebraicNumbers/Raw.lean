import CompPoly
import Cad.Univariate.SturmTarski.Theorem
import Cad.Univariate.SturmTarski.SeqDefs

open CompPoly

lemma sgns_3 {a b c : Rat} : 0 < a * b → a * c < 0 → b * c < 0 := by
  intros h1 h2
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : b < 0 := by nlinarith
    have hc : 0 < c := by nlinarith
    nlinarith
  · rw [ha] at h1
    simp at h1
  · have hb : 0 < b := by nlinarith
    have hc : c < 0 := by nlinarith
    nlinarith

lemma eval_comm_map (p : Polynomial Rat) (l : Rat) : (p.eval l) = (p.map ratToRealHom).eval (l : Real) := by
  simp [Polynomial.eval_eq_sum_range]

namespace AlgebraicNumber

/-- An algebraic number: either the unique root of `p` in the open interval
`(l, r)`, or exactly the rational number `x`. -/
inductive Raw where
  | interval (p : CPolynomial Rat) (l r : Rat) : Raw
  | rat (x : Rat) : Raw

instance : ToString Raw where
  toString a :=
    match a with
    | .interval p l r =>
      let p' : Array Rat := p
      "( " ++ toString p' ++ ", " ++ toString l ++ ", " ++ toString r ++ " )"
    | .rat x => "( " ++ toString x ++ " )"

namespace Raw

/-- The defining polynomial; a rational `x` is the root of `X - x`. -/
def p : Raw → CPolynomial Rat
  | .interval q _ _ => q
  | .rat x => CPolynomial.X - CPolynomial.C x

/-- The lower bound of the isolating interval (`x` itself for a rational). -/
def l : Raw → Rat
  | .interval _ lo _ => lo
  | .rat x => x

/-- The upper bound of the isolating interval (`x` itself for a rational). -/
def r : Raw → Rat
  | .interval _ _ hi => hi
  | .rat x => x

@[simp] lemma p_interval {q : CPolynomial Rat} {lo hi : Rat} : (interval q lo hi).p = q := rfl
@[simp] lemma l_interval {q : CPolynomial Rat} {lo hi : Rat} : (interval q lo hi).l = lo := rfl
@[simp] lemma r_interval {q : CPolynomial Rat} {lo hi : Rat} : (interval q lo hi).r = hi := rfl
@[simp] lemma p_rat {x : Rat} : (rat x).p = CPolynomial.X - CPolynomial.C x := rfl
@[simp] lemma l_rat {x : Rat} : (rat x).l = x := rfl
@[simp] lemma r_rat {x : Rat} : (rat x).r = x := rfl

/-- The real number that `a` stands for is `x`. -/
def represents (a : Raw) (x : Real) : Prop :=
  match a with
  | .interval q lo hi => (toPolyReal q).eval x = 0 ∧ lo < x ∧ x < hi
  | .rat v => x = v

@[simp] lemma represents_interval {q : CPolynomial Rat} {lo hi : Rat} {x : Real} :
    (interval q lo hi).represents x ↔ (toPolyReal q).eval x = 0 ∧ ↑lo < x ∧ x < ↑hi := Iff.rfl

@[simp] lemma represents_rat {v : Rat} {x : Real} : (rat v).represents x ↔ x = ↑v := Iff.rfl

def wellDefined (a : Raw) : Prop :=
  ∃! x : Real, a.represents x

-- This is also guaranteed by libpoly; this is necessary for `refine_wellDefined`.
def sgnDiff (a : Raw) : Prop :=
  match a with
  | .interval q lo hi => q.eval lo * q.eval hi < 0
  | .rat _ => True

@[simp] lemma sgnDiff_interval {q : CPolynomial Rat} {lo hi : Rat} :
    (interval q lo hi).sgnDiff ↔ q.eval lo * q.eval hi < 0 := Iff.rfl

@[simp] lemma sgnDiff_rat {v : Rat} : (rat v).sgnDiff := trivial

/-- Halve the isolating interval. If the root happens to be exactly the
midpoint, the representation collapses to that rational number. -/
def refine (a : Raw) : Raw :=
  match a with
  | .rat x => .rat x
  | .interval q lo hi =>
    let m := (lo + hi) / 2
    if q.eval m = 0 then
      .rat m
    else if q.eval lo * q.eval m < 0 then
      .interval q lo m
    else
      .interval q m hi

lemma eval_cast_zero {q : CPolynomial Rat} {a : Rat} (h : q.eval a = 0) :
    (toPolyReal q).eval (a : Real) = 0 := by
  unfold toPolyReal
  rw [← cpolynomial_map_cast]
  exact_mod_cast h

lemma eval_mul_cast (q : CPolynomial Rat) (a b : Rat) (h : q.eval a * q.eval b < 0) :
    (toPolyReal q).eval (a : Real) * (toPolyReal q).eval (b : Real) < 0 := by
  unfold toPolyReal
  rw [← cpolynomial_map_cast, ← cpolynomial_map_cast]
  exact_mod_cast h

lemma eval_p_rat_self (v : Rat) : (rat v).p.eval ((rat v).l) = 0 := by
  show (CPolynomial.X - CPolynomial.C v).eval v = 0
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simp

lemma represents_bounds {a : Raw} {x : Real} (h : a.represents x) :
    (a.l : Real) ≤ x ∧ x ≤ (a.r : Real) := by
  cases a with
  | interval q lo hi =>
    have h' : (toPolyReal q).eval x = 0 ∧ (lo : Real) < x ∧ x < (hi : Real) := h
    exact ⟨le_of_lt h'.2.1, le_of_lt h'.2.2⟩
  | rat v =>
    have h' : x = (v : Real) := h
    simp [h']

lemma represents_strict {a : Raw} {x : Real} (h : a.represents x) (hl : a.p.eval a.l ≠ 0) :
    (a.l : Real) < x ∧ x < (a.r : Real) := by
  cases a with
  | interval q lo hi =>
    have h' : (toPolyReal q).eval x = 0 ∧ (lo : Real) < x ∧ x < (hi : Real) := h
    exact h'.2
  | rat v => exact absurd (eval_p_rat_self v) hl

lemma represents_root {a : Raw} {x : Real} (h : a.represents x) :
    (toPolyReal a.p).eval x = 0 := by
  cases a with
  | interval q lo hi =>
    have h' : (toPolyReal q).eval x = 0 ∧ (lo : Real) < x ∧ x < (hi : Real) := h
    exact h'.1
  | rat v =>
    have h' : x = (v : Real) := h
    subst h'
    exact eval_cast_zero (eval_p_rat_self v)

lemma represents_of_root {a : Raw} {y : Real} (h_root : (toPolyReal a.p).eval y = 0)
    (h_l : (a.l : Real) < y) (h_r : y < (a.r : Real)) : a.represents y := by
  cases a with
  | interval q lo hi => exact ⟨h_root, h_l, h_r⟩
  | rat v =>
    exfalso
    have h_l' : (v : Real) < y := h_l
    have h_r' : y < (v : Real) := h_r
    linarith

lemma lr_wellDefined : ∀ a : Raw, a.wellDefined → a.l ≤ a.r := by
  intro a h
  obtain ⟨x, hx, -⟩ := h
  have hb := represents_bounds hx
  exact_mod_cast le_trans hb.1 hb.2

lemma sgn_second_half {q : CPolynomial Rat} {lo hi m : Rat}
    (hsgn : q.eval lo * q.eval hi < 0) (hm : q.eval m ≠ 0)
    (hsplit : ¬ q.eval lo * q.eval m < 0) : q.eval m * q.eval hi < 0 := by
  have hl : q.eval lo ≠ 0 := by
    intro h
    rw [h] at hsgn
    simp at hsgn
  have hpos : 0 < q.eval lo * q.eval m :=
    lt_of_le_of_ne (not_lt.mp hsplit) (Ne.symm (mul_ne_zero hl hm))
  exact sgns_3 hpos hsgn

lemma refine_represents_iff (a : Raw) (hwd : a.wellDefined) (hsgn : a.sgnDiff) (x : Real) :
    a.refine.represents x ↔ a.represents x := by
  obtain ⟨y, hy, hy_unique⟩ := hwd
  cases a with
  | rat v => exact Iff.rfl
  | interval q lo hi =>
    have hy' : (toPolyReal q).eval y = 0 ∧ (lo : Real) < y ∧ y < (hi : Real) := hy
    obtain ⟨hy_root, hy_l, hy_r⟩ := hy'
    have hlr : lo < hi := by exact_mod_cast lt_trans hy_l hy_r
    have hlm : lo < (lo + hi) / 2 := by linarith
    have hmr : (lo + hi) / 2 < hi := by linarith
    have hlm' : (lo : Real) < (((lo + hi) / 2 : Rat) : Real) := by exact_mod_cast hlm
    have hmr' : (((lo + hi) / 2 : Rat) : Real) < (hi : Real) := by exact_mod_cast hmr
    simp only [refine]
    split_ifs with hm hsplit
    · -- the root is exactly the midpoint: collapse to a rational
      have hm_root : (toPolyReal q).eval (((lo + hi) / 2 : Rat) : Real) = 0 := eval_cast_zero hm
      have hym : ((((lo + hi) / 2 : Rat)) : Real) = y := hy_unique _ ⟨hm_root, hlm', hmr'⟩
      constructor
      · intro hx
        have hx' : x = ((((lo + hi) / 2 : Rat)) : Real) := hx
        rw [hx', hym]
        exact ⟨hy_root, hy_l, hy_r⟩
      · intro hx
        show x = ((((lo + hi) / 2 : Rat)) : Real)
        exact (hy_unique x hx).trans hym.symm
    · -- the root is in the left half
      obtain ⟨R, hR_gt, hR_lt, hR_root⟩ :=
        exists_root_ioo_mul (le_of_lt hlm') (eval_mul_cast q lo ((lo + hi) / 2) hsplit)
      have hRy : R = y := hy_unique R ⟨hR_root, hR_gt, lt_trans hR_lt hmr'⟩
      constructor
      · rintro ⟨hx_root, hx_l, hx_m⟩
        exact ⟨hx_root, hx_l, lt_trans hx_m hmr'⟩
      · rintro ⟨hx_root, hx_l, hx_r⟩
        refine ⟨hx_root, hx_l, ?_⟩
        have hxy : x = y := hy_unique x ⟨hx_root, hx_l, hx_r⟩
        rw [hxy, ← hRy]
        exact hR_lt
    · -- the root is in the right half
      have hmr_sgn : q.eval ((lo + hi) / 2) * q.eval hi < 0 := sgn_second_half hsgn hm hsplit
      obtain ⟨R, hR_gt, hR_lt, hR_root⟩ :=
        exists_root_ioo_mul (le_of_lt hmr') (eval_mul_cast q ((lo + hi) / 2) hi hmr_sgn)
      have hRy : R = y := hy_unique R ⟨hR_root, lt_trans hlm' hR_gt, hR_lt⟩
      constructor
      · rintro ⟨hx_root, hx_m, hx_r⟩
        exact ⟨hx_root, lt_trans hlm' hx_m, hx_r⟩
      · rintro ⟨hx_root, hx_l, hx_r⟩
        refine ⟨hx_root, ?_, hx_r⟩
        have hxy : x = y := hy_unique x ⟨hx_root, hx_l, hx_r⟩
        rw [hxy, ← hRy]
        exact hR_gt

lemma refine_represents (a : Raw) (hwd : a.wellDefined) (hsgn : a.sgnDiff) {x : Real}
    (hx : a.represents x) : a.refine.represents x :=
  (refine_represents_iff a hwd hsgn x).mpr hx

lemma refine_wellDefined : ∀ a : Raw, a.wellDefined → a.sgnDiff → a.refine.wellDefined := by
  intro a hwd hsgn
  exact (existsUnique_congr (refine_represents_iff a hwd hsgn)).mpr hwd

lemma refine_sgnDiff : ∀ a : Raw, a.sgnDiff → a.refine.sgnDiff := by
  intro a hsgn
  cases a with
  | rat v => trivial
  | interval q lo hi =>
    simp only [refine]
    split_ifs with hm hsplit
    · trivial
    · exact hsplit
    · exact sgn_second_half hsgn hm hsplit

lemma refine_bounds_l : ∀ a : Raw, a.wellDefined → a.l ≤ a.refine.l := by
  intro a h
  have hlr := lr_wellDefined a h
  cases a with
  | rat v => exact le_refl v
  | interval q lo hi =>
    have hlr' : lo ≤ hi := hlr
    simp only [refine]
    split_ifs <;> simp only [l_interval, l_rat] <;> linarith

lemma refine_bounds_r : ∀ a : Raw, a.wellDefined → a.refine.r ≤ a.r := by
  intro a h
  have hlr := lr_wellDefined a h
  cases a with
  | rat v => exact le_refl v
  | interval q lo hi =>
    have hlr' : lo ≤ hi := hlr
    simp only [refine]
    split_ifs <;> simp only [r_interval, r_rat] <;> linarith

lemma refine_width (a : Raw) (h : a.wellDefined) : a.refine.r - a.refine.l ≤ (a.r - a.l) / 2 := by
  have hlr := lr_wellDefined a h
  cases a with
  | rat v => simp [refine]
  | interval q lo hi =>
    have hlr' : lo ≤ hi := hlr
    simp only [refine]
    split_ifs <;> simp only [l_interval, l_rat, r_interval, r_rat] <;> linarith

end Raw

end AlgebraicNumber
