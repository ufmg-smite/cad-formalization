import Mathlib

open Polynomial

abbrev RPoly := Polynomial Complex

noncomputable def sgcd' : List RPoly → RPoly := fun ps =>
  match ps with
  | [] => Polynomial.C 0
  | p1 :: ps' => gcd p1 (sgcd' ps')

noncomputable def sgcd : Finset RPoly → RPoly := fun ps =>
  sgcd' ps.toList

theorem aux (a b c : RPoly) : Dvd.dvd b a → Dvd.dvd (gcd c b) a := by
  intro h
  have : Dvd.dvd (gcd c b) b := gcd_dvd_right c b
  apply dvd_trans this h

theorem aux0 (ps : List RPoly) (a : RPoly) (h : a ∈ ps) : (Dvd.dvd (sgcd' ps) a) :=
  match h2: ps with
  | [] => by simp at h
  | p1::ps' => by
      if h3: a ∈ ps' then
        have ih := aux0 ps' a h3
        simp [sgcd']
        apply aux
        exact ih
      else
        have : a = p1 ∨ a ∈ ps' := List.mem_cons.mp h
        have hap1 : a = p1 := by aesop
        rw [hap1]
        simp [sgcd']
        exact gcd_dvd_left p1 (sgcd' ps')

theorem aux1 (ps : List RPoly) : ∀ p ∈ ps , ∃ q : RPoly , q * sgcd' ps = p := by
  intro p hp
  obtain ⟨q, hq⟩ := aux0 ps p hp
  use q
  rw [mul_comm] at hq
  exact hq.symm

theorem dvd_trans_list (q : RPoly) (ps : List RPoly) : (∀ p ∈ ps , Dvd.dvd q p) → Dvd.dvd q (sgcd' ps) :=
  match ps with
  | [] => by intro h; simp [sgcd']
  | p1 :: ps' => by
    intro h
    have ih := dvd_trans_list q ps'
    simp at h
    obtain ⟨h1, h2⟩ := h
    have ih' := ih h2
    simp [sgcd']
    exact dvd_gcd h1 (ih h2)

theorem root_gcd (ps : List RPoly) (a : Complex) :
    IsRoot (sgcd' ps) a ↔ ∀ p ∈ ps , IsRoot p a := by
  constructor
  · intros h p hp
    obtain ⟨q, hq⟩ := aux1 ps p hp
    have : IsRoot (q * sgcd' ps) a  := root_mul_left_of_isRoot q h
    rw [hq] at this
    assumption
  · intros h
    have : ∀ p ∈ ps , Dvd.dvd (X - C a) p := by
      intros p hp
      have := h p hp
      exact dvd_iff_isRoot.mpr (h p hp)
    have := dvd_trans_list (X - C a) ps this
    exact dvd_iff_isRoot.mp this

noncomputable def rpoly_prod (ps : List RPoly) : RPoly :=
  match ps with
  | [] => C 1
  | p::ps' => p * rpoly_prod ps'

theorem dvd_poly_prod {q : RPoly} (ps : List RPoly) (p : RPoly) (hp : p ∈ ps) (hp2 : Dvd.dvd q p) : Dvd.dvd q (rpoly_prod ps) :=
  match ps with
  | [] => by simp at hp
  | p'::ps' =>
    match List.mem_cons.mp hp with
    | Or.inl pp' => by simp [rpoly_prod]; rw[pp'] at hp2; apply Dvd.dvd.mul_right hp2
    | Or.inr pps' =>
      by simp [rpoly_prod]
         apply Dvd.dvd.mul_left
         exact dvd_poly_prod ps' p pps' hp2



theorem neg_dvd_poly_prod (ps : List RPoly) (a : Complex) (h : IsRoot (rpoly_prod ps) a) (h2 : ∀ p ∈ ps , ¬ (IsRoot p a)) : False :=
  match ps with
  | [] => by simp [rpoly_prod] at h
  | p'::ps' => by
    have : ¬ IsRoot p' a := by apply h2; exact List.mem_cons_self p' ps'
    have : ¬ (Dvd.dvd (X - C a) p') := by intro abs; have abs' := dvd_iff_isRoot.mp abs; exact this abs'
    have ⟨_, _, hp3⟩  : Prime (X - C a) := Polynomial.prime_X_sub_C a
    cases Classical.em (IsRoot (rpoly_prod ps') a) with
    | inl ht =>
      have h2' : ∀ p ∈ ps' , ¬ (IsRoot p a) := by intros hp1 hp2; apply h2; exact List.mem_cons_of_mem p' hp2
      apply False.elim
      exact neg_dvd_poly_prod ps' a ht h2'
    | inr hf =>
      have := dvd_iff_isRoot.mpr h
      simp [rpoly_prod] at this
      have : ¬ IsRoot p' a := by apply h2; exact List.mem_cons_self p' ps'
      simp only [rpoly_prod] at h
      have : ¬ Dvd.dvd (X - C a) p' := by (expose_names; exact this_2)
      have : ¬ Dvd.dvd (X - C a) (rpoly_prod ps') := by
        intro h
        apply hf
        exact dvd_iff_isRoot.mp h
      have dvd : Dvd.dvd (X - C a) (p' * rpoly_prod ps') := by (expose_names; exact this_3)
      expose_names
      have := hp3 p' (rpoly_prod ps') dvd
      aesop


theorem prod_root : ∀ (x : Complex) (ps : List RPoly),
    (∀ p ∈ ps , (¬ IsRoot p x)) ↔ (¬ IsRoot (rpoly_prod ps) x) :=
  by intros a ps
     constructor
     · contrapose!
       intro h
       apply Classical.byContradiction
       intro h2
       push_neg at h2
       have ⟨_, _, hp3⟩  : Prime (X - C a) := Polynomial.prime_X_sub_C a
       exact neg_dvd_poly_prod ps a h h2
     · contrapose!
       rintro ⟨p, ⟨pps, hp⟩⟩
       have : Dvd.dvd (X - C a) p := dvd_iff_isRoot.mpr hp
       have : Dvd.dvd (X - C a) (rpoly_prod ps) := dvd_poly_prod ps p pps this
       exact dvd_iff_isRoot.mp this

noncomputable def exp' (q : RPoly) (p : RPoly) :=
  if p = C 0 then C 0 else q ^ p.natDegree

theorem roots.dvd_of_le (p q : RPoly) (hp : p ≠ 0) : p.roots ≤ q.roots → p ∣ q :=
  Polynomial.Splits.dvd_of_roots_le_roots (p := p) (q := q) (IsAlgClosed.splits p) hp

theorem roots_deg (p : RPoly) (hp : p ≠ 0) : ∀ c ∈ p.roots , p.roots.count c ≤ p.natDegree := sorry

theorem roots_pow (n : Nat) (p : RPoly) : ∀ c ∈ p.roots , p.roots.count c = n * (p^n).roots.count c := sorry

theorem roots_subset (p q : RPoly) : (∀ c ∈ p.roots , p.roots.count c ≤ q.roots.count c) → p.roots ≤ q.roots := sorry

theorem gcd_of_dvd (p q : RPoly) : Dvd.dvd p q → gcd p q = normalize p := sorry

theorem root_gcd_exp₁ (p q : RPoly) : p ≠ 0 → (∀ c ∈ p.roots , c ∈ q.roots) → gcd p (exp' q p) = normalize p := by
  intros hp hr
  if hdeg: p.natDegree = 0 then
    simp [exp', hp, hdeg]
    have foo := degree_eq_natDegree hp
    have bar : p.degree = 0 := by rw [foo]; exact congrArg Nat.cast hdeg
    have := Polynomial.isUnit_iff_degree_eq_zero.mpr bar
    exact (normalize_eq_one.mpr this).symm
  else
    if hq: q = 0 then
      simp [hq, exp', hp]
      rw [zero_pow hdeg, gcd_zero_right p]
    else
      apply gcd_of_dvd p (exp' q p)
      apply roots.dvd_of_le p (exp' q p) hp
      apply roots_subset p (exp' q p)
      intros c hc
      have hqc : c ∈ q.roots := hr c hc
      have hqc' : q.roots.count c ≥ 1 := Multiset.one_le_count_iff_mem.mpr hqc
      have : rootMultiplicity c q ≥ 1 := by rw [<- count_roots]; exact hqc'
      have hqc'' : (exp' q p).roots.count c ≥ p.natDegree := by
        simp [exp', hp]
        exact Nat.le_mul_of_pos_right (natDegree p) this
      have count_c_deg_p := roots_deg p hp c hc
      linarith

theorem root_gcd_exp (p q : RPoly) (h : p ≠ 0) : (∀ c ∈ p.roots , c ∈ q.roots) ↔ gcd p (exp' q p) = normalize p := by
  constructor
  · exact root_gcd_exp₁ p q h
  · intros hgcd c cr
    rw [<- roots_normalize] at cr
    have : IsRoot (normalize p) c := isRoot_of_mem_roots cr
    have : Dvd.dvd (X - C c) (normalize p) := dvd_iff_isRoot.mpr this
    have := gcd_dvd_right p (exp' q p)
    rw [hgcd] at this
    have : Dvd.dvd (X - C c) (exp' q p) := by (expose_names; exact dvd_trans this_2 this)
    simp [exp', h] at this
    -- provavelmente tem que separar o caso que natDegree p = 0
    admit

