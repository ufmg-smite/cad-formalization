import Mathlib

open Polynomial

abbrev CPoly := Polynomial Complex

noncomputable def sgcd : List CPoly → CPoly := fun ps =>
  match ps with
  | [] => C 0
  | p1 :: ps' => gcd p1 (sgcd ps')

theorem aux (a b c : CPoly) : Dvd.dvd b a → Dvd.dvd (gcd c b) a := by
  intro h
  have : Dvd.dvd (gcd c b) b := gcd_dvd_right c b
  apply dvd_trans this h

theorem aux0 (ps : List CPoly) (a : CPoly) (h : a ∈ ps) : (Dvd.dvd (sgcd ps) a) :=
  match h2: ps with
  | [] => by simp at h
  | p1::ps' => by
      if h3: a ∈ ps' then
        have ih := aux0 ps' a h3
        simp [sgcd]
        apply aux
        exact ih
      else
        have : a = p1 ∨ a ∈ ps' := List.mem_cons.mp h
        have hap1 : a = p1 := by aesop
        rw [hap1]
        simp [sgcd]
        exact gcd_dvd_left p1 (sgcd ps')

theorem aux1 (ps : List CPoly) : ∀ p ∈ ps , ∃ q : CPoly , q * sgcd ps = p := by
  intro p hp
  obtain ⟨q, hq⟩ := aux0 ps p hp
  use q
  rw [mul_comm] at hq
  exact hq.symm

theorem dvd_trans_list (q : CPoly) (ps : List CPoly) : (∀ p ∈ ps , Dvd.dvd q p) → Dvd.dvd q (sgcd ps) :=
  match ps with
  | [] => by intro h; simp [sgcd]
  | p1 :: ps' => by
    intro h
    have ih := dvd_trans_list q ps'
    simp at h
    obtain ⟨h1, h2⟩ := h
    have ih' := ih h2
    simp [sgcd]
    exact dvd_gcd h1 (ih h2)

theorem root_gcd (ps : List CPoly) (a : Complex) :
    IsRoot (sgcd ps) a ↔ ∀ p ∈ ps , IsRoot p a := by
  constructor
  · intros h p hp
    obtain ⟨q, hq⟩ := aux1 ps p hp
    have : IsRoot (q * sgcd ps) a  := root_mul_left_of_isRoot q h
    rw [hq] at this
    assumption
  · intros h
    have : ∀ p ∈ ps , Dvd.dvd (X - C a) p := by
      intros p hp
      have := h p hp
      exact dvd_iff_isRoot.mpr (h p hp)
    have := dvd_trans_list (X - C a) ps this
    exact dvd_iff_isRoot.mp this

noncomputable def cpoly_prod (ps : List CPoly) : CPoly :=
  match ps with
  | [] => C 1
  | p::ps' => p * cpoly_prod ps'

theorem dvd_poly_prod {q : CPoly} (ps : List CPoly) (p : CPoly) (hp : p ∈ ps) (hp2 : Dvd.dvd q p) : Dvd.dvd q (cpoly_prod ps) :=
  match ps with
  | [] => by simp at hp
  | p'::ps' =>
    match List.mem_cons.mp hp with
    | Or.inl pp' => by simp [cpoly_prod]; rw[pp'] at hp2; apply Dvd.dvd.mul_right hp2
    | Or.inr pps' =>
      by simp [cpoly_prod]
         apply Dvd.dvd.mul_left
         exact dvd_poly_prod ps' p pps' hp2

theorem neg_dvd_poly_prod (ps : List CPoly) (a : Complex) (h : IsRoot (cpoly_prod ps) a) (h2 : ∀ p ∈ ps , ¬ (IsRoot p a)) : False :=
  match ps with
  | [] => by simp [cpoly_prod] at h
  | p'::ps' => by
    have : ¬ IsRoot p' a := by apply h2; exact List.mem_cons_self p' ps'
    have : ¬ (Dvd.dvd (X - C a) p') := by intro abs; have abs' := dvd_iff_isRoot.mp abs; exact this abs'
    have ⟨_, _, hp3⟩  : Prime (X - C a) := Polynomial.prime_X_sub_C a
    cases Classical.em (IsRoot (cpoly_prod ps') a) with
    | inl ht =>
      have h2' : ∀ p ∈ ps' , ¬ (IsRoot p a) := by intros hp1 hp2; apply h2; exact List.mem_cons_of_mem p' hp2
      apply False.elim
      exact neg_dvd_poly_prod ps' a ht h2'
    | inr hf =>
      have := dvd_iff_isRoot.mpr h
      simp [cpoly_prod] at this
      have : ¬ IsRoot p' a := by apply h2; exact List.mem_cons_self p' ps'
      simp only [cpoly_prod] at h
      have : ¬ Dvd.dvd (X - C a) p' := by (expose_names; exact this_2)
      have : ¬ Dvd.dvd (X - C a) (cpoly_prod ps') := by
        intro h
        apply hf
        exact dvd_iff_isRoot.mp h
      have dvd : Dvd.dvd (X - C a) (p' * cpoly_prod ps') := by (expose_names; exact this_3)
      expose_names
      have := hp3 p' (cpoly_prod ps') dvd
      aesop

theorem prod_root : ∀ (x : Complex) (ps : List CPoly),
    (∀ p ∈ ps , (¬ IsRoot p x)) ↔ (¬ IsRoot (cpoly_prod ps) x) :=
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
       have : Dvd.dvd (X - C a) (cpoly_prod ps) := dvd_poly_prod ps p pps this
       exact dvd_iff_isRoot.mp this

noncomputable def exp' (q : CPoly) (p : CPoly) :=
  if p = C 0 then C 0 else q ^ p.natDegree

theorem roots.dvd_of_le (p q : CPoly) (hp : p ≠ 0) : p.roots ≤ q.roots → p ∣ q :=
  Polynomial.Splits.dvd_of_roots_le_roots (p := p) (q := q) (IsAlgClosed.splits p) hp

theorem roots_deg (p : CPoly) (hp : p ≠ 0) : ∀ c ∈ p.roots , p.roots.count c ≤ p.natDegree := by
  intros r hr
  have := Multiset.count_le_card r p.roots
  exact le_trans this (Polynomial.card_roots' p)

theorem roots_pow (n : Nat) (p : CPoly) : ∀ c ∈ p.roots , (p^n).roots.count c = n * p.roots.count c := by simp

theorem roots_subset (p q : CPoly) : (∀ c ∈ p.roots , p.roots.count c ≤ q.roots.count c) → p.roots ≤ q.roots := by
  intros h
  apply Multiset.le_iff_count.mpr
  intro a
  cases Decidable.em (a ∈ p.roots) with
  | inl ht =>
    exact h a ht
  | inr ht =>
    have : Multiset.count a (roots p) = 0 := Multiset.count_eq_zero.mpr ht
    rw [this]
    exact Nat.zero_le (Multiset.count a (roots q))

theorem gcd_of_dvd (p q : CPoly) : Dvd.dvd p q → gcd p q = normalize p := by
  intro h
  rw [<- normalize_gcd]
  apply normalize_eq_normalize
  · exact gcd_dvd_left p q
  · exact dvd_gcd (dvd_of_eq rfl) h

theorem root_gcd_exp₁ (p q : CPoly) : p ≠ 0 → (∀ c ∈ p.roots , c ∈ q.roots) → gcd p (exp' q p) = normalize p := by
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

noncomputable def qpowdegp (p q : CPoly): List CPoly := List.replicate p.natDegree q

theorem no_roots (p : CPoly)  (h : p ≠ 0): natDegree (normalize p) = 0 → (normalize p).roots = ∅ := by
      intro hndp
      have h2 : (normalize p) ≠ 0 ↔ p ≠ 0 := by
        refine not_congr ?_
        exact normalize_eq_zero
      rw [← h2] at h
      have no_divisionX_c : ∀ a : Complex, ¬ Dvd.dvd (X - C a) (normalize p) := by
        intro a hdiv
        have hdeg := natDegree_le_of_dvd hdiv
        rw [natDegree_X_sub_C, hndp] at hdeg
        exact Nat.not_succ_le_zero 0 (hdeg h)
      apply Multiset.eq_zero_of_forall_not_mem
      intro a ha
      have t1 : IsRoot (normalize p) a ↔ X - C a ∣ (normalize p) := by exact Iff.symm dvd_iff_isRoot
      have t2 : IsRoot (normalize p) a ↔ a ∈ roots (normalize p) := by exact Iff.symm (mem_roots h)
      rw [← t2, t1] at ha
      apply no_divisionX_c a at ha
      exact ha

theorem def_exp_polyprod (p q : CPoly) (h : p ≠ 0) : (exp' q p) = cpoly_prod (qpowdegp p q) := by
  unfold exp' cpoly_prod
  rw[if_neg, qpowdegp]
  induction p.natDegree with
  | zero =>
    have tq : q ^ 0 =  1 := by rfl
    rw[tq]
    have : List.replicate 0 q = [] := by exact rfl
    rw[this]
    exact tq
  | succ n ih =>
    have : q * q ^ n = q ^ (n + 1) := by exact Eq.symm (pow_succ' q n)
    rw [← this, List.replicate_succ, ih]
    match List.replicate n q with
    | [] =>
      simp [h, cpoly_prod]
    | g::gs' =>
      simp [cpoly_prod]
  simp [C]
  exact h

theorem probably_already_exists (q : CPoly) (hq : q ≠ 0) (c : Complex): X - C c ∣ q ↔ c ∈ roots q := by
  constructor
  · intro hx
    refine (mem_roots hq).mpr ?_
    exact dvd_iff_isRoot.mp hx
  · intro hc
    refine dvd_iff_isRoot.mpr ?_
    exact isRoot_of_mem_roots hc

-- roots 0 = ∅, mas (gcd p 0 = normalize p)
theorem root_gcd_exp (p q : CPoly) (h : p ≠ 0) (h2 : q ≠ 0) : (∀ c ∈ p.roots , c ∈ q.roots) ↔ gcd p (exp' q p) = normalize p := by
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
    -- mudanças:
    if hyp : natDegree (normalize p) ≠ 0 then
      have aux : natDegree (normalize p) ≠ 0 → (normalize p).natDegree > 0 := by
        exact fun a => Nat.zero_lt_of_ne_zero hyp
      -- q ^ natDegree p = exp' q p
      have tq2 : q ^ natDegree p = exp' q p := by
        unfold exp'
        simp [h]
      have tq3 : q ^ natDegree p = cpoly_prod (qpowdegp p q) := by
        rw[tq2]
        exact def_exp_polyprod p q h
      have tq4 : X - C c ∣ cpoly_prod (qpowdegp p q) := by
        rw [tq3] at this
        exact this
      have tq5 : X - C c ∣ q ^ natDegree p ↔ X - C c ∣ q := by
        constructor
        · intro hx
          apply Prime.dvd_of_dvd_pow -- X - C c é primo
          {exact prime_X_sub_C c}
          {exact hx}
        · intro hx
          apply dvd_pow
          exact hx
          have equiv2 : (normalize p).natDegree = p.natDegree := by
            have :(normalize p).degree = p.degree := by exact degree_normalize
            exact Eq.symm (natDegree_eq_of_degree_eq (id (Eq.symm this)))
          rw[equiv2] at hyp
          exact hyp
      rw [tq3] at tq5
      rw [tq5] at tq4
      rw [← probably_already_exists q h2]
      exact tq4
    else
      have equiv : ¬(normalize p).natDegree ≠ 0 ↔ (normalize p).natDegree = 0 := by simp
      have help : roots (normalize p) = ∅ := by
        apply no_roots p h
        rw[← equiv]
        exact hyp
      rw [help] at cr
      have : c ∈ (∅ : Multiset ℂ) → c ∈ q.roots := by simp
      exact this cr

theorem cpoly_prod_replicate_const : ∀ (n : Nat) , cpoly_prod (List.replicate n 1) = 1 := fun n =>
  match n with
  | 0 => by simp [cpoly_prod]
  | n' + 1 => by
    have IH := cpoly_prod_replicate_const n'
    simp [List.replicate, cpoly_prod]
    exact IH

theorem cpoly_prod_replicate_const_zero : ∀ (n : Nat) , cpoly_prod (List.replicate (n + 1) 0) = 0 := fun n =>
  match n with
  | 0 => by simp [cpoly_prod]
  | n' + 1 => by simp [List.replicate, cpoly_prod]

theorem prod_zero : ∀ (ps : List CPoly) , cpoly_prod ps = 0 ↔ 0 ∈ ps := by
  intro ps
  constructor
  · cases' ps with p' ps'
    · intro abs
      simp [cpoly_prod] at abs
    · intro h
      simp [cpoly_prod] at h
      cases' h with hl hr
      · rw [hl]
        exact List.mem_cons_self 0 ps'
      · have IH := (prod_zero ps').mp hr
        exact List.mem_cons_of_mem p' IH
  · intro h0
    cases' h0 with h1 h2 h3 h4
    · simp [cpoly_prod]
    · have IH := (prod_zero h3).mpr h4
      simp [cpoly_prod, IH]

theorem cpoly_prod_pow : ∀ (ps : List CPoly) (q : CPoly) , q ≠ 0 →
    (cpoly_prod (List.map (fun p => exp' p q) ps)) = (exp' (cpoly_prod ps) q) := fun ps q hq =>
  match ps with
  | [] => by
    simp [cpoly_prod, exp', hq]
  | p'::ps' => by
    cases' Classical.em (q = 0) with ht hf
    · simp [cpoly_prod, exp', ht]
    · simp [cpoly_prod, exp', hf]
      have IH := cpoly_prod_pow ps' q hq
      simp [cpoly_prod, exp', hf] at IH
      cases' Classical.em (p' = 0) with ht hf
      · simp [ht]
        cases' q.natDegree with n
        · simp
          rw [cpoly_prod_replicate_const ps'.length]
        · simp
      · cases' Classical.em (cpoly_prod ps' = 0) with ht2 hf2
        · rw [ht2]
          simp
          cases' q.natDegree with n
          · simp
            rw [cpoly_prod_replicate_const ps'.length]
          · have foo := (prod_zero ps').mp ht2
            have bar : (0 : CPoly) ^ (n + 1) = 0 := by simp
            have : 0 ^ (n + 1) ∈ List.map (fun p => p ^ (n + 1)) ps' := List.mem_map_of_mem (fun x => x ^ (n + 1)) foo
            rw [bar] at this
            have := (prod_zero (List.map (fun x => x ^ (n + 1)) ps')).mpr this
            rw [this]
            simp
        · rw [mul_pow, IH]

theorem sgcd_normalize (ps : List CPoly) : sgcd ps = normalize (sgcd ps) :=
  match ps with
  | [] => by simp [sgcd]
  | p :: ps' => by simp [sgcd]

def basic_set_prop (ps : List CPoly) (qs : List CPoly) (x : Complex) : Prop :=
  (∀ p ∈ ps, IsRoot p x) ∧ (∀ q ∈ qs, ¬ IsRoot q x)

def deg_prop (ps qs : List CPoly) : Prop :=
    (gcd (sgcd ps) (cpoly_prod (List.map (fun q => exp' q (sgcd ps)) qs))).natDegree ≠
    (sgcd ps).natDegree

theorem gcd_zero (ps : List CPoly) : sgcd ps = 0 → (∀ p ∈ ps , p = 0) := by
  intro h
  cases' ps with p ps
  · intros p hp; simp at hp
  · intros p' hp'
    simp [sgcd] at h
    have : p' = p ∨ p' ∈ ps := List.mem_cons.mp hp'
    cases' this with h1 h2
    · aesop
    · have IH := gcd_zero ps h.2
      aesop

theorem l_1_14 (ps qs : List CPoly) (hq : 0 ∉ qs) :
    (∃ x : Complex , basic_set_prop ps qs x) ↔ deg_prop ps qs := by
  constructor
  · admit
  · intro h
    simp [deg_prop] at h
    simp [basic_set_prop]
    cases' Classical.em (sgcd ps = 0) with ht hf
    · have all_zeroes := gcd_zero ps ht
      rw [ht] at h
      simp [exp'] at h
      cases' qs with q' qs'
      · use 42
        simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
        intros p hp
        rw [all_zeroes p hp]
        exact eval_zero
      · simp only [List.length_cons] at h
        rw [cpoly_prod_replicate_const_zero _] at h
        simp at h
    · rw [cpoly_prod_pow qs (sgcd ps) hf] at h
      have imp : gcd (sgcd ps) (exp' (cpoly_prod qs) (sgcd ps)) ≠ (sgcd ps) := fun a => h (congrArg natDegree a)
      have foo : sgcd ps = normalize (sgcd ps) := sgcd_normalize ps
      nth_rw 3 [foo] at imp
      have := root_gcd_exp (sgcd ps) (cpoly_prod qs) hf (fun abs => hq ((prod_zero qs).mp abs))
      have : ¬ (∀ c ∈ roots (sgcd ps), c ∈ roots (cpoly_prod qs)) := fun abs => imp (this.mp abs)
      push_neg at this
      obtain ⟨c, hc1, hc2⟩ := this
      use c
      constructor
      · have := (root_gcd ps c).mp (isRoot_of_mem_roots hc1)
        exact fun p a => this p a
      · apply (prod_root c qs).mpr
        intro hr
        have : cpoly_prod qs ≠ 0 := fun abs => hq ((prod_zero qs).mp abs)
        have : c ∈ roots (cpoly_prod qs) := (mem_roots_iff_aeval_eq_zero this).mpr hr
        exact hc2 this
