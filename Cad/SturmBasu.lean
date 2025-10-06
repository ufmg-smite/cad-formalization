<<<<<<< Updated upstream
import Cad.SturmBasu.Theorem
=======
import Mathlib

open Polynomial
open Set
open Filter
open Classical

example (p q: ℝ -> Prop): (∃x:ℝ, (p x = q x))-> ((∃x:ℝ, p x) = (∃x:ℝ, q x)) := by
  simp_all only [eq_iff_iff]    


noncomputable section
def sturmSeq (f g : Polynomial ℝ) : List (Polynomial ℝ) :=
  if f = 0 then
    []
  else
    f::(sturmSeq g (-f%g))
  termination_by if f=0 then 0 else if g=0 then 1 else 2 + degree g
  decreasing_by
    simp_all
    if g1: g = 0 then
      simp_all
    else if h : g ∣ f then
      simp_all
      have gnatdeg : g.degree ≥ 0 := by exact zero_le_degree_iff.mpr g1
      refine lt_add_of_lt_of_nonneg ?_ gnatdeg; simp
    else
      simp_all
      have :(-f % g).degree < g.degree := by
        refine degree_lt_degree ?_; refine natDegree_mod_lt (-f) ?_
        have : g.natDegree = 0 → g ∣ f := by
          intro hg
          have : ∃ c : ℝ, C c = g := by
            exact natDegree_eq_zero.mp hg
          rcases this with ⟨c, rfl⟩; use C c⁻¹ * f
          have hds : c ≠ 0 := by
            intro abs; rw [abs] at hg; simp at g1; exact g1 abs
          ext x; simp; field_simp
        have : g.natDegree ≠ 0 := by intro abs; exact h (this abs)
        exact this
      refine WithBot.add_lt_add_left ?_ this; simp_all
-- Considerando só os não nulos
def seqVar : List ℝ → ℕ
| [] => 0
| _::[] => 0
| a::(b::as) =>
  if b == 0 then
    seqVar (a::as)
  else if a * b < 0 then
    1 + seqVar (b::as)
  else
    seqVar (b::as)

def seqEval (k : ℝ) : List (Polynomial ℝ) → List ℝ
| [] => []
| a::as => (eval k a)::(seqEval k as)

def seqVar_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seqEval b P)

def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b

def sgn (k : ℝ) : ℤ  :=
  if k > 0 then 1
  else if k = 0 then 0
  else -1

def rootsInInterval (f : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  f.roots.toFinset.filter (fun x => x ∈ Ioo a b)

def tarskiQuery (f g : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval f a b, sgn (g.eval x)

def rightNear (x : ℝ) : Filter ℝ := nhdsWithin x (Set.Ioi x)

def eventually_at_right (x : ℝ) (P : Real → Prop) : Prop :=
  Filter.Eventually P (rightNear x)

-- P(x + eps) > 0 for all sufficiently small eps
def sign_r_pos (x : ℝ) (p : Polynomial ℝ) : Prop :=
  Filter.Eventually (fun a => eval a p > 0) (rightNear x)

theorem eventually_at_right_def (x: ℝ) (P: ℝ -> Prop) : eventually_at_right x P = Filter.Eventually P (rightNear x) := by rfl
theorem eventually_at_right_equiv {x : Real} {P : Real -> Prop} : eventually_at_right x P ↔ (∃ b : Real, (b > x) ∧ (∀ y : Real, x < y ∧ y < b → P y)) := by
  constructor
  · intro hev
    simp [eventually_at_right] at hev
    exact mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  · intro h
    simp [eventually_at_right]
    exact mem_nhdsGT_iff_exists_Ioo_subset.mpr h

-- We should define sign_r_pos in terms of eventually_at_right
theorem eventually_at_right_equiv' {x : Real} {p : Polynomial Real} : sign_r_pos x p ↔ (∃ b : Real, (b > x) ∧ (∀ y : Real, x < y ∧ y < b → 0 < eval y p)) := by
  constructor
  · intro hev
    simp [eventually_at_right] at hev
    exact mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  · intro h
    simp [sign_r_pos, eventually_at_right]
    exact mem_nhdsGT_iff_exists_Ioo_subset.mpr h

theorem eventually_subst (P Q: ℝ → Prop) (F: Filter ℝ) (h: Filter.Eventually (fun a => P a  = Q a) F) :
                         (Filter.Eventually P F = Filter.Eventually Q F) := by
    simp only [eq_iff_iff] at h ⊢
    constructor
    · intro hev
      exact (eventually_congr h).mp hev
    · intro hev'
      exact (eventually_congr h).mpr hev'
-- 1 if p / q goes from -inf to +inf in x, -1 if goes from +inf to -inf
-- 0 otherwise
def jump_val (p q : Polynomial ℝ) (x : ℝ) : ℤ :=
  let orderP := rootMultiplicity x p
  let orderQ := rootMultiplicity x q
  let oddOrder := Odd (orderP - orderQ)
  if p ≠ 0 ∧ q ≠ 0 ∧ oddOrder then
    -- note that p * q > 0 is the same as p / q > 0
    if sign_r_pos x (p * q) then 1 else -1
  else 0

-- Corresponde a Ind(Q/P; a, b)
def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jump_val p q x

lemma rootsInIntervalZero (a b : ℝ) : rootsInInterval 0 a b = ∅ := by
  simp [rootsInInterval]

lemma next_non_root_interval (p : Polynomial Real) (lb : Real) (hp : p ≠ 0) :
    ∃ ub : Real, lb < ub ∧ (∀ z ∈ Ioc lb ub, eval z p ≠ 0) := by
  cases Classical.em (∃ r : Real, eval r p = 0 ∧ r > lb)
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w > lb)
    if hS: Finset.Nonempty S then

      obtain ⟨lr, hlr⟩ := Finset.min_of_nonempty hS
      have : lr ∈ S := Finset.mem_of_min hlr
      simp [S] at this
      have H1 : lb < lr := by linarith
      have H2 : ∀ z ∈ Ioo lb lr, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.not_mem_of_lt_min hz2 hlr
        simp [S] at this
        have := this hp abs
        linarith
      use (lb + lr) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo lb lr := by
          simp
          constructor
          · exact hz1
          · linarith
        have := H2 z this
        exact this abs
    else
      use lb + 1
      simp
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, hp, abs, hz1]
      have : Finset.Nonempty S := by simp_all only [ne_eq, gt_iff_lt, Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty, S]
      exact hS this
  next hr =>
    push_neg at hr
    use lb + 1
    simp
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

lemma last_non_root_interval (p : Polynomial Real) (ub : Real) (hp : p ≠ 0) :
    ∃ lb : Real, lb < ub ∧ (∀ z ∈ Ico lb ub, eval z p ≠ 0) := by
  cases Classical.em (∃ r : Real, eval r p = 0 ∧ r < ub)
  next hr =>
    obtain ⟨r, hr1, hr2⟩ := hr
    let S := p.roots.toFinset.filter (fun w => w < ub)
    if hS: Finset.Nonempty S then
      obtain ⟨mr, hmr⟩ := Finset.max_of_nonempty hS
      have : mr ∈ S := Finset.mem_of_max hmr
      simp [S] at this
      have H1 : mr < ub := by linarith
      have H2 : ∀ z ∈ Ioo mr ub, eval z p ≠ 0 := by
        intros z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        intro abs
        have : z ∉ S := Finset.not_mem_of_max_lt hz1 hmr
        simp [S] at this
        have := this hp abs
        linarith
      use (mr + ub) / 2
      simp
      constructor
      · linarith
      · intros z hz1 hz2 abs
        have : z ∈ Ioo mr ub := by
          simp
          constructor
          · linarith
          · exact hz2
        have := H2 z this
        exact this abs
    else
      use ub - 1
      simp
      intros z hz1 hz2 abs
      have : z ∈ S := by simp [S, abs, hz2, hp]
      have : Finset.Nonempty S := by simp_all only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty, S]
      exact hS this
  next hr =>
    push_neg at hr
    use ub - 1
    simp
    intros z hz1 hz2 abs
    have := hr z abs
    linarith

theorem exists_root_interval : ∀ p: Polynomial Real, ∀ (a b : ℝ), a <= b → eval a p <= 0 → 0 <= eval b p -> ∃ r: ℝ, r >= a ∧ r <= b ∧ eval r p = 0 := by
  intros p a b hab ha hb
  have p_continuous : ContinuousOn p.eval (Set.Icc a b) := p.continuousOn
  have poly_mathlib_root : ∃ r: ℝ, r >= a ∧ r <= b ∧ p.IsRoot r := by
    have intermediate_value_app := intermediate_value_Icc hab p_continuous
    have zero_in_image : 0 ∈ p.eval '' Set.Icc a b := by
      have zab : 0 ∈ Set.Icc (p.eval a) (p.eval b) := by
        simp
        aesop
      exact Set.mem_of_mem_of_subset zab intermediate_value_app
    obtain ⟨x, ⟨hxa, hxb⟩, hx_root⟩ := zero_in_image
    exact Exists.intro x ⟨hxa, hxb, hx_root⟩
  obtain ⟨r, hra, hrb, hr_root⟩ := poly_mathlib_root
  use r
  exact ⟨hra, hrb, hr_root⟩

lemma not_eq_pos_or_neg_iff_1 (p : Polynomial Real) (lb ub : Real) :
    (∀ z ∈ Ioc lb ub, eval z p ≠ 0) ↔ ((∀ z ∈ Ioc lb ub, eval z p < 0) ∨ (∀ z ∈ Ioc lb ub, 0 < eval z p)) := by
  by_contra!
  cases this
  next H =>
    obtain ⟨H₁, ⟨z₁, hz₁, hz₁'⟩, ⟨z₂, hz₂, hz₂'⟩⟩ := H
    have z1Neq0 : eval z₁ p ≠ 0 := by aesop
    have z2Neq0 : eval z₂ p ≠ 0 := by aesop
    have z1Pos : 0 < eval z₁ p := lt_of_le_of_ne hz₁' (id (Ne.symm z1Neq0))
    have z2Neg : eval z₂ p < 0 := lt_of_le_of_ne hz₂' (H₁ z₂ hz₂)
    have : z₁ ≠ z₂ := by
      intro abs
      rw [abs] at  hz₁'
      have : eval z₂ p = 0 := by linarith
      exact H₁ z₂ hz₂ this
    cases Classical.em (z₁ < z₂)
    next hle =>
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_interval (-p) z₁ z₂ (le_of_lt hle) (by simp; exact hz₁') (by simp; exact hz₂')
      simp at hr₃
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor
        · linarith
        · linarith
      exact H₁ r this hr₃
    next hge =>
      push_neg at hge
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := exists_root_interval p z₂ z₁ hge (le_of_lt z2Neg) (le_of_lt z1Pos)
      have : r ∈ Set.Ioc lb ub := by
        simp at hz₁ hz₂ ⊢
        constructor
        · linarith
        · linarith
      exact H₁ r this hr₃
  next H =>
    obtain ⟨⟨z, hz1, hz2⟩, H₂⟩ := H
    cases H₂
    next H₂ =>
      have := H₂ z hz1
      linarith
    next H₂ =>
      have := H₂ z hz1
      linarith

lemma exists_deriv_eq_slope_poly (a b : Real) (hab : a < b) (p : Polynomial Real) :
    ∃ c : Real, c > a ∧ c < b ∧
                eval b p - eval a p = (b - a) * eval c (derivative p) := by
  obtain ⟨c, hc1, hc2⟩ :=
    exists_deriv_eq_slope (a := a) (b := b) (fun x => eval x p) hab
      (Polynomial.continuousOn_aeval p) (Polynomial.differentiableOn_aeval p)
  simp at hc1
  obtain ⟨hc_low, hc_high⟩ := hc1
  use c
  refine ⟨hc_low, hc_high, ?_⟩
  rw [Polynomial.deriv] at hc2
  rw [hc2]
  have : (b - a) ≠ 0 := by linarith
  field_simp

lemma derivative_ne_0 (p : Polynomial Real) (x : Real) (hev : eval x p = 0) (hp : p ≠ 0) : derivative p ≠ 0 := by
  intro abs
  have := natDegree_eq_zero_of_derivative_eq_zero abs
  obtain ⟨c, hc⟩  := (natDegree_eq_zero.mp this)
  have : c ≠ 0 := by
    intro abs2
    rw [abs2] at hc
    rw [<- hc] at hp
    simp at hp
  rw [<- hc] at hev
  simp at hev
  exact this hev

lemma sign_r_pos_rec (p : Polynomial Real) (x : Real) (hp : p ≠ 0) :
    sign_r_pos x p = if eval x p = 0 then sign_r_pos x (derivative p) else eval x p > 0 := by
  if hev : eval x p = 0 then
    have H1 : sign_r_pos x (derivative p) → sign_r_pos x p := by
      by_contra!
      obtain ⟨H1, H2⟩ := this
      obtain ⟨b, hb1, hb2⟩  := eventually_at_right_equiv'.mp H1
      have HF := (iff_false_right H2).mp (Iff.symm eventually_at_right_equiv')
      push_neg at HF
      obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := HF b hb1
      obtain ⟨z', hz1', hz2', hz3'⟩ := exists_deriv_eq_slope_poly x z hz1 p
      have abs1 : eval z' (derivative p) ≤ 0 := by
        rw [hev] at hz3'
        have foo : eval z p ≤ 0 := hz3
        simp at hz3'
        have : 0 < z - x := by linarith
        clear * - hz3' this hz3
        simp_all only [ge_iff_le]
        exact nonpos_of_mul_nonpos_right hz3 this
      have abs2 := hb2 z' ⟨hz1', lt_trans hz2' hz2⟩
      linarith
    have H2 : sign_r_pos x p → sign_r_pos x (derivative p) := by
      intro H
      have : derivative p ≠ 0 := derivative_ne_0 p x hev hp
      obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval (derivative p) x this
      have H1 := (not_eq_pos_or_neg_iff_1 (derivative p) x ub).mp hub2
      simp at H1
      have : ¬ (∀ z : Real, x < z → z ≤ ub → eval z (derivative p) < 0) := by
        intro abs
        rw [eventually_at_right_equiv'] at H
        obtain ⟨ub', hub1', hub2'⟩ := H
        let T := (x + (min ub ub')) / 2
        have hx1 : 2 * x < (x + ub) := by linarith
        have hx2 : 2 * x < (x + ub') := by linarith
        have hx3 : 2 * x < min (x + ub) (x + ub') := lt_min hx1 hx2
        have hx4 : min (x + ub) (x + ub') = x + min ub ub' := min_add_add_left x ub ub'
        have : x < T := by
          simp only [T]
          rw [<- hx4]
          linarith
        obtain ⟨z', hz1', hz2', hz3'⟩ := exists_deriv_eq_slope_poly x T this p
        clear hx1 hx2 hx3 hx4
        have hT : 0 < eval T p := by
          refine hub2' T ⟨this, ?_⟩
          simp [T]
          if Hub : ub < ub' then
            rw [min_eq_left_of_lt Hub]
            linarith
          else
            push_neg at Hub
            rw [min_eq_right Hub]
            linarith
        have : 0 < T - x := by linarith
        rw [hev] at hz3'
        simp at hz3'
        have : 0 < eval z' (derivative p) := by
          clear * -  this hz3' hT
          have foo : 0 < (T - x) * eval z' (derivative p) := lt_of_lt_of_eq hT hz3'
          exact (pos_iff_pos_of_mul_pos foo).mp this
        have foo : z' ≤ ub := by
          simp [T] at hz2'
          if Hub : ub < ub' then
            rw [min_eq_left_of_lt Hub] at hz2'
            linarith
          else
            push_neg at Hub
            rw [min_eq_right Hub] at hz2'
            linarith
        have := abs z' hz1' foo
        linarith
      have : ∀ z : Real, x < z → z ≤ ub → 0 < eval z (derivative p) := by
        cases H1
        next H1 => exact False.elim (this H1)
        next H1 => exact H1
      rw [eventually_at_right_equiv']
      use ub
      refine ⟨hub1, ?_⟩
      rintro y ⟨hy1, hy2⟩
      exact this y hy1 (le_of_lt hy2)
    simp [hev]
    exact ⟨H2, H1⟩
  else
    simp [hev]
    have : sign_r_pos x p → 0 < eval x p := by
      by_contra!
      obtain ⟨h1, h2⟩ := this
      obtain ⟨ub, hub1, hub2⟩  : ∃ ub : Real, x < ub ∧ (∀ z : Real, z > x ∧ z < ub → 0 < eval z p) := by
        obtain ⟨ub, hub1, hub2⟩  := eventually_at_right_equiv'.mp h1
        use ub
      have H : 0 < eval ((ub + x) / 2) p := by
        have h1 : ((ub + x) / 2) > x := by linarith
        have h2 : ((ub + x) / 2) < ub := by linarith
        exact hub2 ((ub + x) / 2) ⟨h1, h2⟩
      have H2 : eval x p < 0 := lt_of_le_of_ne h2 hev
      obtain ⟨r, hr1, hr2, hr3⟩ := exists_root_interval p x ((ub + x) / 2) (by linarith) (le_of_lt H2) (le_of_lt H)
      have : r ≠ x := by
        intro abs
        rw [<- abs] at hev
        exact hev hr3
      have : x < r := lt_of_le_of_ne hr1 (Ne.symm this)
      have := hub2 r ⟨this, by linarith⟩
      linarith
    have : 0 < eval x p → sign_r_pos x p := by
      intro H
      rw [eventually_at_right_equiv']
      obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval p x hp
      have := (not_eq_pos_or_neg_iff_1 p x ub).mp hub2
      cases this
      next H1 =>
        clear hub2
        apply False.elim
        have : eval ub p < 0 := H1 ub (by simp; exact hub1)
        obtain ⟨r, hr1, hr2, hr3⟩ :=
          exists_root_interval (-p) x ub (le_of_lt hub1) (by simp; exact le_of_lt H) (by simp; exact le_of_lt this)
        simp at hr3
        cases Classical.em (x = r)
        next heq =>
          rw [<- heq] at hr3
          rw [hr3] at H
          simp at H
        next hneq =>
          have : x < r := lt_of_le_of_ne hr1 hneq
          have : r ∈ Ioc x ub := by simp; aesop
          have := H1 r this
          rw [hr3] at this
          simp at this
      next H1 =>
        use ub
        refine ⟨hub1, ?_⟩
        rintro y ⟨hy1, hy2⟩
        simp at H1
        exact H1 y hy1 (le_of_lt hy2)
    aesop

lemma sign_r_pos_minus (x : ℝ) (p : Polynomial ℝ) : p ≠ 0 → (sign_r_pos x p ↔ (¬ sign_r_pos x (-p))) := by
  intro hp
  have : sign_r_pos x p ∨ sign_r_pos x (-p) := by
    obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval p x hp
    have := (not_eq_pos_or_neg_iff_1 p x ub).mp hub2
    cases this
    next H =>
      right
      rw [eventually_at_right_equiv']
      use ub
      refine ⟨hub1, ?_⟩
      rintro y ⟨hy1, hy2⟩
      simp at H ⊢
      exact H y hy1 (le_of_lt hy2)
    next H =>
      left
      rw [eventually_at_right_equiv']
      use ub
      refine ⟨hub1, ?_⟩
      rintro y ⟨hy1, hy2⟩
      simp at H
      exact H y hy1 (le_of_lt hy2)
  have : sign_r_pos x p → ¬ (sign_r_pos x (-p)) := by
    intros H abs
    rw [eventually_at_right_equiv'] at H abs
    obtain ⟨b, hb1, hb2⟩ := H
    obtain ⟨c, hc1, hc2⟩ := abs
    let s := min b c
    have xs : x < s := lt_min hb1 hc1
    let y := (x + s) / 2
    have xy : x < y := left_lt_add_div_two.mpr xs
    have ys : y < s := add_div_two_lt_right.mpr xs
    have sb : s ≤ b := min_le_left b c
    have yb : y < b := gt_of_ge_of_gt sb ys
    have sc : s ≤ c := min_le_right b c
    have yc : y < c := gt_of_ge_of_gt sc ys
    have h1 := hb2 y ⟨xy, yb⟩
    have h2 := hc2 y ⟨xy, yc⟩
    simp at h2
    linarith
  aesop

lemma eval_non_zero(p: Polynomial ℝ) (x: ℝ) (h: eval x p ≠ 0) : p ≠ 0 := by aesop


lemma eval_mod (p q: Polynomial ℝ) (x: ℝ) (h: eval x q = 0) : eval x (p % q) = eval x p := by
 have : eval x (p % q) = eval x (p / q * q) + eval x (p % q) := by simp; exact Or.inr h
 rw [<- eval_add, EuclideanDomain.div_add_mod'] at this; exact this

lemma sign_r_pos_add (p q: Polynomial ℝ) (hp_eval: eval x p = 0) (hq_eval: eval x q ≠ 0) :
                     (sign_r_pos x (p + q) = sign_r_pos x q) := by
  rcases Classical.em (eval x (p + q) = 0) with ht | hf
  · aesop
  · have h_pq : p + q ≠ 0 := by exact eval_non_zero (p + q) x hf
    have h: sign_r_pos x (p + q) = (eval x q > 0) := by
      have := sign_r_pos_rec (p + q) x h_pq
      simp [hf, hp_eval, hq_eval] at this; simp [this]
    have : sign_r_pos x q = (eval x q > 0) := by
      have := sign_r_pos_rec q x (eval_non_zero q x hq_eval)
      simp [hq_eval] at this; simp [this]
    simp [this, h]

lemma sign_r_pos_mod (p q: Polynomial ℝ) (hp_eval: eval x p = 0) (hq_eval: eval x q ≠ 0) :
                                         sign_r_pos x (q % p) = sign_r_pos x q := by
  have h : eval x (q / p * p) = 0 := by simp; exact Or.inr hp_eval
  have h' : eval x (q % p) ≠ 0 := by
    rw [eval_mod q p x hp_eval]; exact hq_eval
  nth_rw 2 [<-EuclideanDomain.div_add_mod q p]; rw[sign_r_pos_add]
  simp; exact Or.inl hp_eval
  exact h'

lemma sign_r_pos_smult (p: Polynomial ℝ) (x c: ℝ) : ¬(c = 0) -> ¬(p = 0) ->
  sign_r_pos x (Polynomial.C c * p) = if c > 0 then sign_r_pos x p else ¬ sign_r_pos x p := by
  intros hc hp
  simp only [<- ne_eq] at hc hp
  rcases Classical.em (c > 0) with ht | hf
  · simp [sign_r_pos, ht]
  · simp [hf]
    simp at hf hc
    have hcltz : c < 0 := by exact lt_of_le_of_ne hf hc
    have hy : ∀y: ℝ, ((0 < eval y (C c * p)) = (0 < eval y (-p) )) := by
      simp_all
      intro y
      constructor
      · exact fun a => neg_of_mul_pos_right a hf
      · exact fun a => mul_pos_of_neg_of_neg hcltz a
    have heq : sign_r_pos x (C c * p) = sign_r_pos x (-p) := by
      simp [sign_r_pos, hc]
      aesop
    have : sign_r_pos x p = (¬ sign_r_pos x (-p)) := by simp only [sign_r_pos_minus x p hp]
    aesop

set_option maxHeartbeats 500000
lemma sign_r_pos_mult (p q : Polynomial Real) (x : Real) (hp : p ≠ 0) (hq : q ≠ 0) :
    sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
  obtain ⟨ub, hub1, hub2⟩ : ∃ ub : ℝ , x < ub ∧ ((∀ z ∈ Ioo x ub, 0 < eval z p) ∨ (∀ z ∈ Ioo x ub, eval z p < 0)) := by
    obtain ⟨ub, hub1, hub2⟩ := next_non_root_interval p x hp
    have := (not_eq_pos_or_neg_iff_1 p x ub).mp hub2
    replace this : (∀ z ∈ Set.Ioo x ub, eval z p < 0) ∨ (∀ z ∈ Set.Ioo x ub, 0 < eval z p) := by
      cases this
      next H =>
        left
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
      next H =>
        right
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
    use ub
    exact ⟨hub1, (Or.symm this)⟩
  obtain ⟨ub', hub1', hub2'⟩ : ∃ ub' : ℝ , x < ub' ∧ ((∀ z ∈ Ioo x ub', 0 < eval z q) ∨ (∀ z ∈ Ioo x ub', eval z q < 0)) := by
    obtain ⟨ub', hub1', hub2'⟩ := next_non_root_interval q x hq
    have := (not_eq_pos_or_neg_iff_1 q x ub').mp hub2'
    replace this : (∀ z ∈ Set.Ioo x ub', eval z q < 0) ∨ (∀ z ∈ Set.Ioo x ub', 0 < eval z q) := by
      cases this
      next H =>
        left
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
      next H =>
        right
        simp_all only [ne_eq, mem_Ioc, and_imp, mem_Ioo]
        intros z hz1 hz2
        exact H z hz1 (le_of_lt hz2)
    use ub'
    exact ⟨hub1', (Or.symm this)⟩
  have H1 : (∀ z ∈ Ioo x ub, 0 < eval z p) → (∀ z ∈ Ioo x ub', 0 < eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x p := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      aesop
    have sign_r_pos_q : sign_r_pos x q := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      aesop
    have : Filter.Eventually (fun z => 0 < eval z p ∧ 0 < eval z q) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z p ∧ 0 < eval z q) (q := fun z => 0 < eval z (p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      exact Left.mul_pos hx₁ hx₂
    aesop
  have H2 : (∀ z ∈ Ioo x ub, 0 < eval z p) → (∀ z ∈ Ioo x ub', 0 > eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x p := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      aesop
    have sign_r_pos_q : sign_r_pos x (-q) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      aesop
    have : Filter.Eventually (fun z => 0 < eval z p ∧ 0 < eval z (-q)) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (- p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z p ∧ 0 < eval z (-q)) (q := fun z => 0 < eval z (-p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      have hp : eval x (-p) < 0 := by simp; exact hx₁
      have hq : eval x q < 0 := by simp at hx₂; exact hx₂
      exact mul_pos_of_neg_of_neg hp hq
    have : ¬ sign_r_pos x (p * q) := by
      have eq : p * q = - (-p * q) := by
        clear * -
        simp_all only [neg_mul, neg_neg]
      rw [eq]
      have neq0 : p * q ≠ 0 := (mul_ne_zero_iff_right hq).mpr hp
      have neq0' : -p * q ≠ 0 := by
        clear * - neq0
        simp_all only [ne_eq, mul_eq_zero, not_or, neg_mul, neg_eq_zero, or_self, not_false_eq_true]
      exact (sign_r_pos_minus x (-p * q) neq0').mp this
    have sign_r_pos_q' : ¬ sign_r_pos x q := by
      clear * -  sign_r_pos_q hq
      have := sign_r_pos_minus x q hq
      aesop
    clear * - this sign_r_pos_p sign_r_pos_q'
    aesop
  have H3 : (∀ z ∈ Ioo x ub, 0 > eval z p) → (∀ z ∈ Ioo x ub', 0 < eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x (-p) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      aesop
    have sign_r_pos_q : sign_r_pos x q := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      aesop
    have : Filter.Eventually (fun z => 0 < eval z (-p) ∧ 0 < eval z q) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (- p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z (-p) ∧ 0 < eval z q) (q := fun z => 0 < eval z (-p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      have hp : eval x p < 0 := by simp at hx₁; exact hx₁
      have hq : eval x (-q) < 0 := by simp; exact hx₂
      exact Left.mul_pos hx₁ hx₂
    have : ¬ sign_r_pos x (p * q) := by
      have eq : p * q = - (-p * q) := by
        clear * -
        simp_all only [neg_mul, neg_neg]
      rw [eq]
      have neq0 : p * q ≠ 0 := (mul_ne_zero_iff_right hq).mpr hp
      have neq0' : -p * q ≠ 0 := by
        clear * - neq0
        simp_all only [ne_eq, mul_eq_zero, not_or, neg_mul, neg_eq_zero, or_self, not_false_eq_true]
      exact (sign_r_pos_minus x (-p * q) neq0').mp this
    have sign_r_pos_p' : ¬ sign_r_pos x p := by
      clear * -  sign_r_pos_p hp
      have := sign_r_pos_minus x p hp
      aesop
    clear * - this sign_r_pos_p' sign_r_pos_q
    aesop
  have H4 : (∀ z ∈ Ioo x ub, 0 > eval z p) → (∀ z ∈ Ioo x ub', 0 > eval z q) → sign_r_pos x (p * q) = (sign_r_pos x p ↔ sign_r_pos x q) := by
    intros hzp hzq
    have sign_r_pos_p : sign_r_pos x (-p) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub
      aesop
    have sign_r_pos_q : sign_r_pos x (-q) := by
      unfold sign_r_pos
      apply eventually_at_right_equiv.mpr
      use ub'
      aesop
    have : Filter.Eventually (fun z => 0 < eval z (-p) ∧ 0 < eval z (-q)) (rightNear x) := Eventually.and sign_r_pos_p sign_r_pos_q
    have : sign_r_pos x (p * q) := by
      unfold sign_r_pos
      apply Eventually.mono (p := fun z => 0 < eval z (-p) ∧ 0 < eval z (-q)) (q := fun z => 0 < eval z (p * q)) this
      rintro x ⟨hx₁, hx₂⟩
      rw [eval_mul]
      simp at hx₁
      simp at hx₂
      exact mul_pos_of_neg_of_neg hx₁ hx₂
    clear * - this sign_r_pos_p sign_r_pos_q hp hq
    have : ¬ sign_r_pos x p := by
      have := sign_r_pos_minus x p hp
      aesop
    have : ¬ sign_r_pos x q := by
      have := sign_r_pos_minus x q hq
      aesop
    aesop
  aesop

lemma sign_r_pos_deriv (p : Polynomial Real) (x : Real) (hp : p ≠ 0) (hev : eval x p = 0) : sign_r_pos x (derivative p * p) := by
  have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
  suffices sign_r_pos x (derivative p) = sign_r_pos x p by
    rw [sign_r_pos_mult (derivative p) p x deriv_ne_0 hp]
    exact Eq.to_iff this
  rw [sign_r_pos_rec p]
  · simp [hev]
  · exact hp
  
example (a b: ℝ) (h: a^2 > 0): ((a^2 * b > 0) = (b > 0)) := by simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]
lemma jump_poly_mult {p q p': Polynomial ℝ} {x: ℝ} (hp': p' ≠ 0) :
                    jump_val (p' * p) (p'* q) x = jump_val p q x := by
  cases Classical.em (q = 0 ∨ p = 0)
  next H => 
    unfold jump_val; simp only;
    cases H <;> simp_all
  next H =>
  rw [not_or] at H; obtain ⟨hp, hq⟩ := H
  have h_sign : sign_r_pos x (p' * q * (p' * p)) = sign_r_pos x (q * p) := by
    have ⟨b, h_b⟩ : ∃b, b > x ∧ (∀z, x < z ∧ z < b -> eval z (p' * p') > 0)  := by
      rcases Classical.em (∃z, eval z p' = 0 ∧ z > x) with ⟨z, hz⟩ | hf
      · have roots_fin : {r: ℝ | eval r p' = 0 ∧ r > x}.Finite := by
          have := finite_setOf_isRoot hp'
          unfold IsRoot at this; exact Finite.sep this fun a => a > x
        let roots_x : Finset ℝ := Finite.toFinset roots_fin
        have : roots_x.Nonempty := by 
          unfold roots_x; simp [roots_fin]; exact Set.nonempty_of_mem hz
        let lr := Finset.min' (roots_x) this
        have h_eval_nz: (∀z: ℝ, x < z ∧ z < lr -> eval z p' ≠ 0) ∧ lr > x := by
          have : lr > x := by
            unfold lr; unfold roots_x;
            simp [roots_fin] 
          simp only [this, and_true]
          intros z hz; unfold lr roots_x at hz
          have hz_n : z ∉ roots_x := by
            by_contra!
            simp [roots_x, roots_fin] at this hz
            simp [this] at hz; have h_contra := hz z this.1 this.2
            exact (lt_self_iff_false z).mp h_contra
          simp [roots_x, roots_fin, hz] at hz_n; exact hz_n 
        have h_eval_gz : ∀z: ℝ, x < z ∧ z < lr ->  eval z (p' * p') > 0 := by
          intros z hz; simp; exact h_eval_nz.1 z hz
        use lr; exact ⟨h_eval_nz.2, h_eval_gz⟩
      · have h_eval_nz: ∀z:ℝ, x < z ∧ z < x + 1 -> eval z p' ≠ 0 := by
          intros z hz; simp at hf
          have := (hf z)
          contrapose this; simp at this ⊢
          exact ⟨this, hz.1⟩
        have h_eval_gz: ∀z:ℝ, x < z ∧ z < x + 1 -> eval z (p' * p') > 0 := by
          intros z hz; simp; exact h_eval_nz z hz
        have h_trivial : x + 1 > x := by exact lt_add_one x
        use x+1 
    have h_bb : ∃b, b > x ∧ ∀z: ℝ, x < z ∧ z < b -> ((0 < eval z (p' * q * (p' * p))) = (0 < eval z (q * p))) := by 
        use b; simp only [h_b, true_and];
        intros z hz; simp; have := h_b.2 z hz
        simp only [eval_mul] at this; ring_nf at this ⊢
        simp [gt_iff_lt] at this
        have ans := mul_pos_iff_of_pos_left (b := eval z q * eval z p) this
        ring_nf at ans; exact ans
    simp only [eventually_at_right_equiv']
    have := eventually_subst (fun a => eval a (p' * q * (p' * p)) > 0)  (fun a => eval a (q * p) > 0) (rightNear x) 
    simp only [<-eventually_at_right_def, eventually_at_right_equiv] at this 
    exact this h_bb
  have h_odd : Odd (rootMultiplicity x (p' * p) - rootMultiplicity x (p' * q)) =
              Odd (rootMultiplicity x p - rootMultiplicity x q) := by
    have hp'p : p' * p ≠ 0 := by exact (mul_ne_zero_iff_right hq).mpr hp'
    have hp'q : p' * q ≠ 0 := by exact (mul_ne_zero_iff_right hp).mpr hp'
    simp [rootMultiplicity_mul hp'q, rootMultiplicity_mul hp'p]
    rw [Nat.add_sub_add_left]
  have h_iff : p' * q ≠ 0 ↔ q ≠ 0 := by exact mul_ne_zero_iff_left hp'
  unfold jump_val; simp_all
  rw [mul_comm, h_sign, mul_comm]

lemma jump_poly_mod (p q: Polynomial ℝ) (x: ℝ) : jump_val p q x = jump_val p (q % p) x := by
  rcases Classical.em (p = 0 ∨ q = 0) with ht | hf
  · aesop
  · simp [<- ne_eq] at hf 
    let n := min (rootMultiplicity x q) (rootMultiplicity x p)
    have ⟨q', hq'⟩ : ∃q', q = (X - C x)^n * q' := by
      have  : (X - C x)^n ∣ q := by
        rw [<- le_rootMultiplicity_iff]
        exact Nat.min_le_left (rootMultiplicity x q) (rootMultiplicity x p)
        exact hf.2
      exact this
    have ⟨p', hp'⟩ : ∃p', p = (X - C x)^n * p' := by
      have : (X - C x)^n ∣ p := by
        rw [<- le_rootMultiplicity_iff]
        exact Nat.min_le_right (rootMultiplicity x q) (rootMultiplicity x p)
        exact hf.1
      exact this
    have hz' : q' ≠ 0 ∧ p' ≠ 0:= by
      have := hf
      rw [hq', hp'] at this
      constructor
      exact right_ne_zero_of_mul this.2
      exact right_ne_zero_of_mul this.1
    have hrm: rootMultiplicity x q' = 0 ∨ rootMultiplicity x p' = 0 := by
      if H: n = rootMultiplicity x q then
        have : ¬(X - C x)^1 ∣ q' := by
         simp
         have hbound := rootMultiplicity_le_iff hf.2 x n
         simp [H] at hbound
         by_contra!
         have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
         rw [hf] at hq'
         rw [mul_comm, mul_assoc, mul_comm, <- pow_succ'] at hq'
         have hcontra : (X - C x)^(n + 1) ∣ q := by
           simp [hq']
         rw [H] at hcontra
         exact hbound hcontra
        rw [<- rootMultiplicity_le_iff hz'.1 x 0] at this
        omega
      else
        have H : n = rootMultiplicity x p := by omega
        have : ¬(X - C x)^1 ∣ p' := by
          simp
          have hbound := rootMultiplicity_le_iff hf.1 x n
          simp [H] at hbound
          by_contra!
          have ⟨f, hf⟩ := exists_eq_mul_left_of_dvd this
          rw [hf, mul_comm, mul_assoc, mul_comm, <- pow_succ'] at hp'
          have hcontra : (X - C x)^(n + 1) ∣ p := by
            simp [hp']
          rw [H] at hcontra
          exact hbound hcontra
        rw [<- rootMultiplicity_le_iff hz'.2 x 0] at this
        omega
    have hcond: q' ≠ 0 ∧ Odd (rootMultiplicity x p' - rootMultiplicity x q') =
               ((q' % p' ≠ 0) ∧ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p'))) := by
        rcases Classical.em (rootMultiplicity x p' = 0) with htt | hff
        · simp [htt, hz']
        · rw [<-ne_eq] at hff
          rcases hrm with hok | hcontra
          · have hq_ndvd: ¬ ((X - C x)^1 ∣ q') := by
              apply (rootMultiplicity_le_iff hz'.1 x 0).mp
              linarith
            have hp_dvd : (X - C x) ∣ p' := by
              have : rootMultiplicity x p' >= 1:= by omega
              apply (le_rootMultiplicity_iff hz'.2).mp at this
              simp at this; exact this
            have hq_mod_ndvd : ¬ ((X - C x)^1 ∣ q' % p') := by
              simp
              simp at hq_ndvd
              simp [EuclideanDomain.dvd_mod_iff hp_dvd]; exact hq_ndvd
            have : rootMultiplicity x (q' % p') = 0 ∧ q' % p' ≠ 0 := by
              simp at hq_mod_ndvd hq_ndvd
              have : q' % p' ≠ 0 := by
                simp [EuclideanDomain.mod_zero]
                by_contra!
                have := dvd_trans hp_dvd this; exact hq_ndvd this
              constructor
              · apply Nat.le_zero.mp; apply (rootMultiplicity_le_iff this x 0).mpr
                simp;  exact hq_mod_ndvd
              · exact this
            simp [hz', this, hok]
          · exfalso; exact hff hcontra
    have h_imp : q' % p' ≠ 0 -> eval x p' = 0 -> sign_r_pos x (q' * p') = sign_r_pos x (q' % p' * p') := by
      intros h_mod_z h_eval_z
      have : eval x q' ≠ 0 := by
        simp_all [<- IsRoot.def, rootMultiplicity_eq_zero_iff]
      have : sign_r_pos x q' = sign_r_pos x (q' % p') := by exact Eq.symm (sign_r_pos_mod p' q' h_eval_z this)
      rw [sign_r_pos_mult, sign_r_pos_mult];
      simp at this ⊢ <;> trivial
    have h: q' % p' = 0 ∨ eval x p' ≠ 0 -> jump_val p' q' x = jump_val p' (q' % p') x := by
      intros h_or
      if h_modz: (q' % p' = 0) then unfold jump_val; simp [*]
      else
        have : ¬ Odd (rootMultiplicity x p' - rootMultiplicity x q') ∧
               ¬ Odd (rootMultiplicity x p' - rootMultiplicity x (q' % p')) := by
          have h': eval x p' ≠ 0 := by exact Or.resolve_left h_or h_modz
          simp [*] at hcond;
          have : rootMultiplicity x p' = 0 := by exact rootMultiplicity_eq_zero h'
          have : ¬ Odd (rootMultiplicity x p' - rootMultiplicity x q') := by simp [this]
          simp [this] at hcond ⊢; exact hcond
        unfold jump_val; simp [*]
    have h_ult : jump_val p' q' x = jump_val p' (q' % p') x := by
      if h': (q' % p' ≠ 0 ∧ eval x p' = 0) then
      · have := (h_imp h'.1) h'.2
        unfold jump_val
        if hpz: (p' = 0) then simp [hpz] else
          simp only; split
          next H =>
            simp only [eq_iff_iff] at hcond; simp [(hcond.2.mp H.2.2), hpz]
            rw [mul_comm, this, mul_comm]; 
          next H =>
            simp only [Lean.Grind.not_and] at H;
            rcases H with ha | hb | hc <;> simp_all [<-Nat.not_odd_iff_even]
       else
         simp only [Lean.Grind.not_and, ne_eq, not_not, <-ne_eq] at h'
         exact h h'
    clear *- h_ult hq' hp' hz'
    have h_mon_z :  (X - C x) ^ n ≠ 0:= by
      exact pow_ne_zero n (X_sub_C_ne_zero x)
    rw [hp', hq']
    simp [jump_poly_mult h_mon_z]
    
    
lemma mul_C_eq_root_multiplicity (p: Polynomial ℝ) (c r: ℝ) (hc: ¬ c = 0):
                                        (rootMultiplicity r p = rootMultiplicity r (C c * p)) := by
  simp only [<-count_roots]
  rw [roots_C_mul]
  exact hc

lemma jump_poly_smult_1 (p q: Polynomial ℝ) (c x: ℝ) :
                        jump_val p (Polynomial.C c * q) x = (sgn c) * jump_val p q x := by
  rcases Classical.em (c = 0 ∨ q = 0)  with ht|hf
  · unfold jump_val
    simp [ht]
    split
    · have hc: c = 0 := by aesop
      unfold sgn
      simp [hc]
    · rfl
  · simp at hf
    unfold jump_val
    if hpz : p = 0 then
      simp [hpz]
    else
      have h := sign_r_pos_smult (p * q) x c hf.1
      simp [hf, hpz] at h
      simp [hpz, hf]
      unfold sgn
      have := mul_C_eq_root_multiplicity q c x hf.1
      rw [mul_left_comm, this]
      if hc : c > 0 then
        simp [hc] at h ⊢
        rw [h]
     else
       simp [hc, hf.1] at h ⊢
       simp only [h, ite_not]

lemma jump_poly_sign (p q : Polynomial ℝ) (x : ℝ) :
    p ≠ 0 → p.eval x = 0 → jump_val p (derivative p * q) x = sgn (q.eval x) := by
  intros hp hev
  if hq : q = 0 then
    rw [hq]
    simp [sgn, jump_val]
  else
    have deriv_ne_0 : derivative p ≠ 0 := derivative_ne_0 p x hev hp
    have elim_p_order : rootMultiplicity x p - rootMultiplicity x (derivative p * q) = 1 - rootMultiplicity x q := by
      rw [Polynomial.rootMultiplicity_mul]
      · rw [derivative_rootMultiplicity_of_root hev]
        have : 1 ≤ rootMultiplicity x p := by
          apply (le_rootMultiplicity_iff hp).mpr
          simp
          exact dvd_iff_isRoot.mpr hev
        omega
      · exact (mul_ne_zero_iff_right hq).mpr deriv_ne_0
    have elim_sgn_r_pos_p : sign_r_pos x ((derivative p * q) * p) = sign_r_pos x q := by
      have : sign_r_pos x ((derivative p * q) * p) = (sign_r_pos x (derivative p * p) ↔ sign_r_pos x q) := by
        rw [mul_comm, <- mul_assoc]
        have := sign_r_pos_mult (p * derivative p) q x ((mul_ne_zero_iff_right deriv_ne_0).mpr hp) hq
        nth_rw 2 [mul_comm p (derivative p)] at this
        exact this
      rw [this]
      have := sign_r_pos_deriv p x hp hev
      aesop
    unfold jump_val
    admit

lemma B_2_57 (p q : Polynomial ℝ) (a b : ℝ) (hab : a < b)  :
    tarskiQuery p q a b = cauchyIndex p (derivative p * q) a b := by
  if hp : p = 0 then
    rw [hp]
    simp [tarskiQuery, cauchyIndex]
    rw [rootsInIntervalZero]
    simp
  else
    unfold tarskiQuery
    unfold cauchyIndex
    apply Finset.sum_congr rfl
    intros x hx
    have : p.eval x = 0 := by
      simp [rootsInInterval] at hx
      exact hx.1.2
    rw [jump_poly_sign p q x hp this]

-- Talvez usar reais extendidos para a e b seja a tradução mais imediata do enunciado.
-- Por enquanto, podemos seguir desconsiderando esse caso.
theorem B_2_58 (p q: Polynomial ℝ) (hp: p != Polynomial.C 0) (a b: ℝ) (hab : a < b) :
    seqVarSturm_ab p q a b = cauchyIndex p q a b :=
  sorry

def sigma (b : ℝ) (f : Polynomial ℝ) : ℤ :=
  sgn (eval b f)

-- Mesma definição presente em Isabelle
def variation (x y: ℝ) : ℤ :=
  if x * y >= 0 then 0 else if x < y then 1 else -1
def cross (p: Polynomial ℝ) (a b: ℝ): ℤ :=
  variation (eval a p) (eval b p)

lemma cauchyIndex_poly_mod (p q: Polynomial ℝ) (a b: ℝ) : cauchyIndex p q a b = cauchyIndex p (q % p) a b := by
  simp [cauchyIndex]
  apply Finset.sum_congr rfl
  intros x hx
  exact jump_poly_mod p q x

  -- apply jump_poly_mod p q x
lemma cauchyIndex_inverse_add (p q: Polynomial ℝ) (hpq: IsCoprime p q) :
    cauchyIndex q p a b + cauchyIndex p q a b = cauchyIndex (Polynomial.C 1) (q * p) a b:= by sorry
lemma cauchyIndex_inverse_add_cross (p q: Polynomial ℝ) (a b: ℝ) (hab: a < b)
                          (ha: eval a (p * q) != 0) (hb: eval b (p * q) != 0) :
     (cauchyIndex p q a b) + (cauchyIndex q p a b) =  cross (p * q) a b := by sorry

lemma cauchyIndex_poly_smult_1 (p q : Polynomial ℝ) (a b c: ℝ) :
     cauchyIndex p (Polynomial.C c * q) a b = (sgn c) * cauchyIndex p q a b := by sorry

-- para o else, precisamos usar ha e hb para mostrar que σ(a) * σ(b) != 0 (e pela definição de sgn, excluir todos outros inteiros).
-- Talvez seja possível expressar isso de alguma forma melhor.
-- Decidi alterar e utilizar o mesmo enunciado equivalente para a demonstração em Isabelle.
-- A definição de cross nos dá mais recursos operacionais para provar coisas.
lemma B_2_60 (p q: Polynomial ℝ)  (a b: ℝ) (hab: a < b)
             (hpqa : eval a (p * q) != 0)
             (hpqb : eval b (p * q) != 0):
      cauchyIndex p q a b = cross (p * q) a b + cauchyIndex q (-(p % q)) a b := by
  have hq_zero: q != Polynomial.C 0 := by aesop
  have h_cross := cauchyIndex_inverse_add_cross p q a b hab hpqa hpqb
  have h: - cauchyIndex q p a b = cauchyIndex q (-(p % q)) a b := by
   have h_minus := cauchyIndex_poly_smult_1 q (p % q) a b (-1 : ℝ)
   have h_trivial: ¬ ((1: ℝ) < 0) := by simp
   simp [sgn, h_trivial] at h_minus
   rw [<- cauchyIndex_poly_mod q p a b] at h_minus
   exact Eq.symm h_minus
  rw [<- eq_sub_iff_add_eq, sub_eq_add_neg, h] at h_cross
  exact h_cross

lemma seqVar_sign_change {x y : ℝ} {xs : List ℝ} (hy : y ≠ 0) :
  seqVar (x :: (y :: xs)) = (if x * y < 0 then 1 else 0) + seqVar (y :: xs) := by
    simp_all
    rw[seqVar]
    simp [hy]
    split_ifs; simp_all
    simp

lemma sigma_eq_def (a : ℝ) (p q : Polynomial ℝ) : sigma a (p*q) = sgn (eval a p * eval a q) := by rw[sigma]; simp

theorem L_2_59_1 (a b : ℝ) (p q : Polynomial ℝ) (hprod : sigma b (p*q) * sigma a (p*q) = -1) (hq : q ≠ 0) (hp : p ≠ 0) (hj : ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ ( ∀p' ∈ sturmSeq p q, ¬IsRoot p' b))):
      seqVarSturm_ab p q a b
      =  sigma b (p*q) + seqVarSturm_ab q (-p%q) a b := by
  rw [seqVarSturm_ab, seqVar_ab];  rcases hj with ⟨ha, hb⟩
  have sigma_a_ne_zero : sigma a (p*q) ≠ 0 := by
    intro H
    have : sigma b (p*q) * 0 = -1 := by rw [H] at hprod; exact hprod
    simp at this
  have eval_a_ne_zero : eval a (p*q) ≠ 0 := by
    intro Heval
    have : sigma a (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_a_ne_zero this)
  have eval_a_q_ne_zero : eval a q ≠ 0 := by
    have : eval a p * eval a q ≠ 0 := by rw [eval_mul] at eval_a_ne_zero; exact eval_a_ne_zero
    exact right_ne_zero_of_mul this
  have sigma_b_ne_zero : sigma b (p*q) ≠ 0 := by
    intro H
    have : 0 * sigma a (p*q) = -1 := by rw [H] at hprod; exact hprod
    simp at this
  have eval_b_ne_zero : eval b (p*q) ≠ 0 := by
    intro Heval
    have : sigma b (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_b_ne_zero this)
  have eval_b_q_ne_zero : eval b q ≠ 0 := by
    have : eval b p * eval b q ≠ 0 := by rw [eval_mul] at eval_b_ne_zero; exact eval_b_ne_zero
    exact right_ne_zero_of_mul this
  have h1a : sigma a (p*q) = 1 ∨ sigma a (p*q) = -1 := by
    rw[sigma, sgn]
    if hpos : eval a (p*q) > 0 then
      left; split_ifs; rfl
    else right; split_ifs; rfl
  have hseqEval : seqEval a (sturmSeq p q) = eval a p :: seqEval a (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  have hseqEvalb : seqEval b (sturmSeq p q) = eval b p :: seqEval b (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  if hsigmaa : sigma a (p*q) = -1 then
    have h2_1 : sigma b (p*q) = 1 := by
      rw [hsigmaa] at hprod
      simp at hprod; exact hprod
    have h2_2a : seqVar (seqEval a (sturmSeq p q)) = 1 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      rw[hseqEval]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_a_q_ne_zero
        _ = 1 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval a p * eval a q < 0 := by
            rw[sigma_eq_def, sgn] at hsigmaa; simp at hsigmaa
            by_cases hpos : eval a p * eval a q > 0
            · simp [hpos] at hsigmaa
            by_cases heq : eval a p * eval a q = 0
            · simp [heq] at hsigmaa; exfalso
              have contra : eval a p * eval a q ≠ 0 := mul_ne_zero (And.left hsigmaa) (And.right hsigmaa)
              exact contra heq
            have hle : eval a p * eval a q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval a p * eval a q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          exact haqsgn
    have h2_2b : seqVar (seqEval b (sturmSeq p q))= seqVar (seqEval b (sturmSeq q (-p%q))) := by
      rw[hseqEvalb]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]
            apply seqVar_sign_change eval_b_q_ne_zero
        _ = 0 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          simp [hprod]
          have hbsgn : eval b p * eval b q > 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            split_ifs at h2_1
            assumption
            linarith
          linarith
      linarith
    rw[h2_2a, h2_2b, h2_1]; simp
    rw [seqVarSturm_ab, seqVar_ab]
    linarith
  else
    have hsa_pos : sigma a (p*q) = 1 := by
      have : sigma a (p*q) = -1 → False := by
        intro H; apply (by simp [H] at hsigmaa)
      rcases h1a with hpos | hneg
      · exact hpos
      · exfalso; exact this hneg
    have h2_1 : sigma b (p*q) = -1 := by rw [hsa_pos] at hprod; simp at hprod; exact hprod
    have h2_2a : seqVar (seqEval a (sturmSeq p q))
      = seqVar (seqEval a (sturmSeq q (-p%q))) := by
      have : seqEval a (sturmSeq p q) = eval a p :: seqEval a (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
      rw[this]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]
            apply seqVar_sign_change eval_a_q_ne_zero
        _ = 0 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval a p * eval a q > 0 := by
            rw[sigma_eq_def, sgn] at hsa_pos
            split_ifs at hsa_pos
            assumption
            linarith
          linarith
      linarith
    have h2_2b : seqVar (seqEval b (sturmSeq p q))
      = 1 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      have : seqEval b (sturmSeq p q) = eval b p :: seqEval b (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
      rw[this]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]
            apply seqVar_sign_change eval_b_q_ne_zero
        _ = 1 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          simp [hprod]
          have hbsgn : eval b p * eval b q < 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            simp at h2_1
            by_cases hpos : eval b p * eval b q > 0
            · simp [hpos] at h2_1
            by_cases heq : eval b p * eval b q = 0
            · simp [heq] at h2_1
              exfalso
              have contra : eval b p * eval b q ≠ 0 :=
                mul_ne_zero (And.left h2_1) (And.right h2_1)
              exact contra heq
            have hle : eval b p * eval b q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval b p * eval b q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          exact hbsgn
    rw[h2_2a, h2_2b, h2_1]; simp
    rw [seqVarSturm_ab, seqVar_ab]
    linarith

theorem L_2_59_2 (a b : ℝ) (p q : Polynomial ℝ) (hprod : sigma b (p*q) * sigma a (p*q) = 1) (hq : q ≠ 0) (hp : p ≠ 0) (hj : ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ (∀p' ∈ sturmSeq p q, ¬IsRoot p' b))):
      seqVarSturm_ab p q a b =  seqVarSturm_ab q (-p%q) a b := by
  rw [seqVarSturm_ab, seqVar_ab]; rcases hj with ⟨ha, hb⟩
  have sigma_a_ne_zero : sigma a (p*q) ≠ 0 := by
    intro H
    have : sigma b (p*q) * 0 = 1 := by
      rw [H] at hprod; exact hprod
    simp at this
  have eval_a_ne_zero : eval a (p*q) ≠ 0 := by
    intro Heval
    have : sigma a (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_a_ne_zero this)
  have eval_a_q_ne_zero : eval a q ≠ 0 := by
    have : eval a p * eval a q ≠ 0 := by rw [eval_mul] at eval_a_ne_zero; exact eval_a_ne_zero
    exact right_ne_zero_of_mul this
  have sigma_b_ne_zero : sigma b (p*q) ≠ 0 := by
    intro H
    have : 0 * sigma a (p*q) = 1 := by
      rw [H] at hprod; exact hprod
    simp at this
  have eval_b_ne_zero : eval b (p*q) ≠ 0 := by
    intro Heval
    have : sigma b (p*q) = 0 := by simp [sigma, sgn, Heval]
    exact (sigma_b_ne_zero this)
  have eval_b_q_ne_zero : eval b q ≠ 0 := by
    have : eval b p * eval b q ≠ 0 := by rw [eval_mul] at eval_b_ne_zero; exact eval_b_ne_zero
    exact right_ne_zero_of_mul this
  have h1a : sigma a (p*q) = 1 ∨ sigma a (p*q) = -1 := by
    rw[sigma, sgn]
    if hpos : eval a (p*q) > 0 then
      left; split_ifs; rfl
    else right; split_ifs; rfl
  have hseqEval : seqEval a (sturmSeq p q) = eval a p :: seqEval a (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  have hseqEvalb : seqEval b (sturmSeq p q) = eval b p :: seqEval b (sturmSeq q (-p % q)) := by rw[sturmSeq, seqEval.eq_def]; simp at hp; simp[hp]
  if hsigmaa : sigma a (p*q) = 1 then
    have h2_1 : sigma b (p*q) = 1 := by
      rw [hsigmaa] at hprod
      simp at hprod; exact hprod
    have h2_2a : seqVar (seqEval a (sturmSeq p q)) = 0 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      rw[hseqEval]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_a_q_ne_zero
        _ = 0 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval a p * eval a q > 0 := by
            rw[sigma_eq_def, sgn] at hsigmaa
            split_ifs at hsigmaa
            assumption
            linarith
          linarith
    simp at hsigmaa
    simp at h2_2a
    have h2_2b : seqVar (seqEval b (sturmSeq p q)) = 0 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      rw[hseqEvalb]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_b_q_ne_zero
        _ = 0 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          simp [hprod]
          have haqsgn : eval b p * eval b q > 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            split_ifs at h2_1
            assumption
            linarith
          linarith
    simp at h2_1; simp at h2_2b; rw[h2_2a, h2_2b]
    rw [seqVarSturm_ab, seqVar_ab]
  else
    have hsa_neg : sigma a (p*q) = -1 := by
      have : sigma a (p*q) = 1 → False := by
        intro H; apply (by simp [H] at hsigmaa)
      rcases h1a with hpos | hneg
      · exfalso; exact this hpos
      · exact hneg
    have h2_1 : sigma b (p*q) = -1 := by rw [hsa_neg] at hprod; simp at hprod; linarith
    have h2_2a : seqVar (seqEval a (sturmSeq p q)) = 1 + seqVar (seqEval a (sturmSeq q (-p%q))) := by
      rw[hseqEval]
      calc
        seqVar (eval a p :: seqEval a (sturmSeq q (-p % q)))
          = (if eval a p * eval a q < 0 then 1 else 0) + seqVar (seqEval a (sturmSeq q (-p % q))) := by
            have : seqEval a (sturmSeq q (-p % q)) = eval a q :: seqEval a (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_a_q_ne_zero
        _ = 1 + seqVar (seqEval a (sturmSeq q (-p % q))) := by
          simp [hprod]
          have hbsgn : eval a p * eval a q < 0 := by
            rw[sigma_eq_def, sgn] at hsa_neg
            simp at hsa_neg
            by_cases hpos : eval a p * eval a q > 0
            · simp [hpos] at hsa_neg
            by_cases heq : eval a p * eval a q = 0
            · simp [heq] at hsa_neg
              exfalso
              have contra : eval a p * eval a q ≠ 0 :=
                mul_ne_zero (And.left hsa_neg) (And.right hsa_neg)
              exact contra heq
            have hle : eval a p * eval a q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval a p * eval a q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          exact hbsgn
    have h2_2b : seqVar (seqEval b (sturmSeq p q)) = 1 + seqVar (seqEval b (sturmSeq q (-p%q))) := by
      rw[hseqEvalb]
      calc
        seqVar (eval b p :: seqEval b (sturmSeq q (-p % q)))
          = (if eval b p * eval b q < 0 then 1 else 0) + seqVar (seqEval b (sturmSeq q (-p % q))) := by
            have : seqEval b (sturmSeq q (-p % q)) = eval b q :: seqEval b (sturmSeq (-p % q) (-q%(-p % q))) := by
              rw[sturmSeq, seqEval.eq_def]; simp at hq; simp[hq]
            rw [this]; apply seqVar_sign_change eval_b_q_ne_zero
        _ = 1 + seqVar (seqEval b (sturmSeq q (-p % q))) := by
          have haqsgn : eval b p * eval b q < 0 := by
            rw[sigma_eq_def, sgn] at h2_1
            by_cases hpos : eval b p * eval b q > 0
            · simp [hpos] at h2_1
            by_cases heq : eval b p * eval b q = 0
            · simp [heq] at h2_1
            have hle : eval b p * eval b q ≤ 0 := le_of_not_gt hpos
            have : 0 ≠ eval b p * eval b q := by intro Haux; exact heq Haux.symm
            exact lt_of_le_of_ne hle (Ne.symm this)
          simp_all
    simp at h2_1; simp at h2_2a; simp at h2_2b; rw[h2_2a, h2_2b]; simp_all; ring_nf
    rw [seqVarSturm_ab, seqVar_ab]

/-
def seqVar_ab (P: List (Polynomial ℝ)) (a b: ℝ): ℤ :=
  (seqVar (seqEval a P) : Int) - seqVar (seqEval b P)

def seqVarSturm_ab (p q: (Polynomial ℝ)) (a b : ℝ) : ℤ :=
  seqVar_ab (sturmSeq p q) a b
-/
theorem L_2_59 (a b : ℝ) (p q : Polynomial ℝ) (hq : q ≠ 0) (hp : p ≠ 0):
      ((∀p' ∈ sturmSeq p q, ¬IsRoot p' a) ∧ (∀p' ∈ sturmSeq p q, ¬IsRoot p' b))
      → if hprod : sigma b (p*q) * sigma a (p*q) = 1 then (seqVarSturm_ab p q a b)
      =  seqVarSturm_ab q (-p%q) a b else seqVarSturm_ab p q a b
      =  sigma b (p*q) + seqVarSturm_ab q (-p%q) a b := by
  intro h
  if hprod : sigma b (p*q) * sigma a (p*q) = 1 then
    simp_all
    exact L_2_59_2 a b p q hprod hq hp h
  else
    simp_all
    have hneg : sigma b (p*q) * sigma a (p*q) = -1 := by
      have : sigma b (p*q) * sigma a (p*q) ≠ 1 := by intro H; exact hprod H
      have : sigma b (p*q) * sigma a (p*q) ≠ 0 := by
        intro H
        have : sigma b (p*q) ≠ 0 := by
          intro Haux; rw[sigma, sgn] at Haux; simp_all
          have : eval b (p*q) ≠ 0 := by
            intro Heval
            have aux := And.right h
            have : ¬ eval b p = 0 := by
              apply aux p; rw[sturmSeq]; simp; exact hp
            have : ¬ eval b q = 0 := by
              apply aux q; rw[sturmSeq]; simp;
              sorry
            sorry
          sorry
        sorry
      sorry
    exact L_2_59_1 a b p q hneg hq hp h

theorem Tarski (f g : Polynomial ℝ) (hf : f ≠ C 0) (a b : ℝ) (h : a < b) :
      seqVarSturm_ab f (derivative f * g) a b
      = tarskiQuery f g a b
      := by
  rw [B_2_57 _ _ _ _ h]
  rw [<- B_2_58 _ _ _ _ _ h]
  simp [hf]
  simp_all only [map_zero, ne_eq, not_false_eq_true]
>>>>>>> Stashed changes
