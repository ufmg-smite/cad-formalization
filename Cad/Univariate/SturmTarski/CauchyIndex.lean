import Cad.Univariate.SturmTarski.JumpPoly
import Mathlib.RingTheory.Polynomial.Content

noncomputable section

open Polynomial SignType

-- Corresponde a Ind(Q/P; a, b)
def cauchyIndex (p q : Polynomial ℝ) (a b : ℝ) : ℤ :=
  ∑ x ∈ rootsInInterval p a b, jumpVal p q x

/-- Sign change of a pair: `1` if the pair goes from negative to positive, `-1` if it goes from
positive to negative, and `0` otherwise (in particular whenever one entry is zero). -/
def variation (a b : ℝ) : ℤ :=
  if a * b < 0 then sign b else 0

def cross (p : Polynomial ℝ) (a b : ℝ) : ℤ :=
  variation (p.eval a) (p.eval b)

lemma cross_no_root {a b: ℝ} {p: Polynomial ℝ} (hab: a < b) (hxnroot: rootsInInterval p a b = ∅) :
      (cross p a b = 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [cross, variation]
  have hnr : 0 ≤ eval a p * eval b p := by
    by_contra! hneg
    obtain ⟨r, har, hrb, hr⟩ := exists_root_ioo_mul (le_of_lt hab) hneg
    have : r ∈ rootsInInterval p a b := mem_rootsInInterval.mpr ⟨⟨hp0, hr⟩, har, hrb⟩
    rw [hxnroot] at this
    exact Finset.notMem_empty r this
  simp [cross, variation, hnr]

lemma cauchyIndex_poly_mod (p q : Polynomial ℝ) (a b : ℝ) :
    cauchyIndex p q a b = cauchyIndex p (q % p) a b := by
  unfold cauchyIndex
  have := jump_poly_mod p q
  exact Finset.sum_congr rfl fun x a => this x

lemma cauchyIndex_smult_1 (p q : Polynomial ℝ) (a b c : ℝ) :
    cauchyIndex p (C c * q) a b = sign c * cauchyIndex p q a b := by
  unfold cauchyIndex
  have : sign c * ∑ x ∈ rootsInInterval p a b, jumpVal p q x =
         ∑ x ∈ rootsInInterval p a b, sign c * (jumpVal p q x) :=
           Finset.mul_sum (rootsInInterval p a b) (jumpVal p q) (sign c)
  rw [this]
  congr
  ext x
  exact jump_poly_smult_1 p q c x

lemma mul_neg_iff_of_pos_left {c b : ℝ} (hc : 0 < c) : c * b < 0 ↔ b < 0 :=
  ⟨fun h => neg_of_mul_neg_right h hc.le, fun h => mul_neg_of_pos_of_neg hc h⟩

theorem variation_mult_pos1 (c x y : ℝ) (hc : 0 < c) : variation (c*x) y = variation x y := by
  simp only [variation, mul_assoc, mul_neg_iff_of_pos_left hc]

theorem variation_mult_pos2 (c x y : ℝ) (hc : 0 < c) : variation x (c*y) = variation x y := by
  simp only [variation, mul_left_comm x c y, mul_neg_iff_of_pos_left hc, sign_mul, sign_pos hc,
    one_mul]

theorem variation_mult_pos (c d x y : ℝ) (hc : 0 < c) (hd : 0 < d) :
    variation (c * x) (d * y) = variation x y := by
  rw [variation_mult_pos1 c x (d * y) hc, variation_mult_pos2 d x y hd]

lemma variation_eq_of_ne_zero {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    variation u v = (if u < 0 then 1 else 0) - (if v < 0 then 1 else 0) := by
  rcases lt_or_gt_of_ne hu with hu | hu <;> rcases lt_or_gt_of_ne hv with hv | hv
  · simp [variation, le_of_lt (mul_pos_of_neg_of_neg hu hv), hu, hv]
  · simp [variation, mul_neg_of_neg_of_pos hu hv, sign_pos hv, hu, not_lt.mpr (le_of_lt hv)]
  · simp [variation, mul_neg_of_pos_of_neg hu hv, sign_neg hv, not_lt.mpr (le_of_lt hu), hv]
  · simp [variation, le_of_lt (mul_pos hu hv), not_lt.mpr (le_of_lt hu), not_lt.mpr (le_of_lt hv)]

/-- The sign change of a product pair, in terms of sign (dis)agreement within each pair: this is
the form in which `variation` meets `List.signVariations`. -/
lemma variation_mul_eq {x y x' y' : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hx' : x' ≠ 0) (hy' : y' ≠ 0) :
    variation (x * y) (x' * y') =
      (if sign x = sign y then 0 else 1) - (if sign x' = sign y' then 0 else 1) := by
  rw [variation_eq_of_ne_zero (mul_ne_zero hx hy) (mul_ne_zero hx' hy'), ite_sign_eq hx hy,
    ite_sign_eq hx' hy']

lemma variation_mult_neg_1 (c x y : ℝ) (hc : c < 0) :
    variation (c*x) y = variation x y + if y = 0 then 0 else sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy
  · simp [variation, le_of_lt (mul_pos_of_neg_of_neg hx hy),
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hc hx) hy,
      sign_neg hx, sign_neg hy, hy.ne]
  · simp [variation]
  · simp [variation, mul_neg_of_neg_of_pos hx hy,
    le_of_lt (mul_pos (mul_pos_of_neg_of_neg hc hx) hy),
      sign_neg hx, sign_pos hy, hy.ne']
  · simp [variation]
  · simp [variation]
  · simp [variation]
  · simp [variation, mul_neg_of_pos_of_neg hx hy,
    le_of_lt (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hc hx) hy),
      sign_pos hx, sign_neg hy, hy.ne]
  · simp [variation]
  · simp [variation, le_of_lt (mul_pos hx hy),
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc hx) hy,
      sign_pos hx, sign_pos hy, hy.ne']

@[simp]
theorem cindex_poly_z_1 (p q: Polynomial ℝ) (a b: ℝ) (hp: p = 0) : cauchyIndex p q a b = 0 := by
  simp [cauchyIndex, jumpVal, hp]

@[simp]
theorem cindex_poly_z_2 (p q: Polynomial ℝ) (a b: ℝ) (hq: q = 0) : cauchyIndex p q a b = 0 := by
  simp [cauchyIndex, jumpVal, hq]

theorem cindex_poly_const (p q : Polynomial ℝ) (a b x : ℝ) (hp_const : C x = p) :
    cauchyIndex p q a b = 0 := by
  have hp_nroots : p.roots = 0 := by rw [←hp_const]; exact roots_C x
  simp [cauchyIndex, rootsInInterval, hp_nroots]

theorem cindex_poly_mult {p q p': Polynomial ℝ} {a b: ℝ} (hp' : p' ≠ 0) :
    (cauchyIndex (p' * p) (p' * q) a b) = cauchyIndex p q a b := by
  if hp: p = 0 then
    simp [hp]
  else
    unfold cauchyIndex
    simp only [ne_eq, not_false_eq_true, jump_poly_mult, hp']
    have hsum : ∑ x ∈ rootsInInterval p' a b \ rootsInInterval p a b, jumpVal p q x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_sdiff, mem_rootsInInterval, mem_rootsInInterval] at hx
      exact jump_poly_not_root fun h => hx.2 ⟨⟨hp, h⟩, hx.1.2⟩
    have h_interval : rootsInInterval (p' * p) a b =
        rootsInInterval p a b ∪ (rootsInInterval p' a b \ rootsInInterval p a b) := by
      rw [Finset.union_sdiff_self_eq_union, mul_comm, rootsInInterval_mul a b (mul_ne_zero hp hp')]
    simp only [h_interval]
    have hdsj :
        Disjoint (rootsInInterval p a b) (rootsInInterval p' a b \ rootsInInterval p a b) :=
      Finset.disjoint_sdiff
    rw [Finset.sum_union hdsj]
    simp [hsum]

theorem cindex_poly_cross {p : Polynomial ℝ} {a b : ℝ} (hab : a < b) (hpa_nroot : eval a p ≠ 0)
    (hpb_nroot : eval b p ≠ 0) :
    cauchyIndex p 1 a b = cross p a b := by
  have hpz : p ≠ 0 := eval_non_zero p a hpa_nroot
  induction hp: p.natDegree using Nat.strong_induction_on generalizing p with
  | _ k ih  =>
    cases k with
    | zero =>
      obtain ⟨x, hx⟩ : ∃ x: ℝ, C x = p := natDegree_eq_zero.mp hp
      have hlz: cauchyIndex p 1 a b = 0 := cindex_poly_const p 1 a b x hx
      have hrz: cross p a b = 0 := by
        unfold cross variation
        have h_eq : eval a p = eval b p := by
          rw [← hx, eval_C, eval_C]
        simp [h_eq, mul_self_nonneg (eval b p)]
      rw [hlz, hrz]
      | succ k =>
        if H: (rootsInInterval p a b).Nonempty then
          let maxr : ℝ := Finset.max' (rootsInInterval p a b) H
          have hmaxr_root : eval maxr p = 0 ∧ maxr > a ∧  maxr < b := by
            have := mem_rootsInInterval.mp (Finset.max'_mem (rootsInInterval p a b) H)
            exact ⟨this.1.2, this.2.1, this.2.2⟩
          -- factor out the largest root: `p = p' * (X - maxr) ^ m` with `p' maxr ≠ 0`
          obtain ⟨p', hp', hmonon_nvdv⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpz maxr
          set maxrp := (X - C maxr) ^ rootMultiplicity maxr p with hmaxrp
          rw [mul_comm] at hp'
          have hpa' : eval a (p' * maxrp) ≠ 0 := hp' ▸ hpa_nroot
          have hpb' : eval b (p' * maxrp) ≠ 0 := hp' ▸ hpb_nroot
          rw [eval_mul] at hpa' hpb'
          obtain ⟨hap', hamaxrp⟩ := mul_ne_zero_iff.mp hpa'
          obtain ⟨hbp', hbmaxrp⟩ := mul_ne_zero_iff.mp hpb'
          have hp'z : p' ≠ 0 := eval_non_zero p' a hap'
          have maxrpz : maxrp ≠ 0 := eval_non_zero maxrp a hamaxrp
          have hmaxrp' : eval maxr p' ≠ 0 := (not_imp_not.mpr (dvd_iff_isRoot.mpr)) hmonon_nvdv
          have hmulrz :
              rootMultiplicity maxr p > 0 :=
              ((rootMultiplicity_pos hpz).mpr (IsRoot.def.mpr hmaxr_root.1))
          have hmulr : rootMultiplicity maxr p ≠ 0 := (zero_lt_iff.mp hmulrz)
          let maxr_sign := if Odd (rootMultiplicity maxr p) then -1 else 1
          have hc_sum :
              cauchyIndex p 1 a b = (∑ x ∈ (rootsInInterval p' a b), jumpVal p 1 x) +
              jumpVal p 1 maxr := by
            unfold cauchyIndex
            have hrinterval :
                rootsInInterval p a b = rootsInInterval p' a b ∪ rootsInInterval maxrp a b := by
              unfold rootsInInterval
              rw [hp'] at hpz ⊢; exact rootsInInterval_mul a b hpz;
            have hmaxrp_singleton : rootsInInterval maxrp a b = {maxr} := by
              ext y
              rw [mem_rootsInInterval, Finset.mem_singleton]
              have hev : eval y maxrp = 0 ↔ y = maxr := by
                simp only [hmaxrp, eval_pow, eval_sub, eval_X, eval_C, pow_eq_zero_iff hmulr,
                  sub_eq_zero]
              rw [hev]
              exact ⟨fun h => h.1.2, fun h => ⟨⟨maxrpz, h⟩, by rw [h]; exact hmaxr_root.2.1,
                by rw [h]; exact hmaxr_root.2.2⟩⟩
            have hdisjoint : rootsInInterval p' a b ∩ rootsInInterval maxrp a b = ∅ := by
              have : maxr ∉ rootsInInterval  p' a b := fun h =>
                hmonon_nvdv (dvd_iff_isRoot.mpr (mem_rootsInInterval.mp h).1.2)
              rw [hmaxrp_singleton]
              simp [this]
            rw [hrinterval, Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr hdisjoint),
              hmaxrp_singleton]
            simp
          have hcross :
              ∑ x ∈ rootsInInterval p' a b, jumpVal p 1 x = maxr_sign * cross p' a b := by
            have hcr_sign :
                ∑ x ∈ rootsInInterval p' a b, jumpVal p 1 x =
                ∑ x ∈ rootsInInterval p' a b, maxr_sign * jumpVal p' 1 x := by
              refine Finset.sum_congr rfl ?_
              intros x hx
              have hx_root: x ∈ rootsInInterval p a b := by
                rw [hp'] at hpz ⊢
                rw [rootsInInterval_mul a b hpz]
                exact Finset.mem_union_left _ hx
              have hx_maxr : x ≠ maxr := by
                intro h
                rw [h] at hx
                exact hmonon_nvdv (dvd_iff_isRoot.mpr (mem_rootsInInterval.mp hx).1.2)
              have hx_nroot: eval x maxrp ≠ 0 := by
                simp only [hmaxrp, eval_pow, eval_sub, eval_X, eval_C]
                exact pow_ne_zero _ (sub_ne_zero.mpr hx_maxr)
              have hxlmaxr: x < maxr := by
                have : x <= maxr := Finset.le_max' (rootsInInterval p a b) x hx_root
                exact lt_of_le_of_ne this hx_maxr
              have hmaxr_sign : sign (eval x maxrp) = maxr_sign := by
                have hevallt: (x - maxr) < 0 := by
                  simp [hxlmaxr]
                unfold maxr_sign
                rw [hmaxrp]
                simp only [eval_pow, eval_sub, eval_X, eval_C]
                split_ifs with h₁
                · simp [sign_neg (Odd.pow_neg h₁ hevallt)]
                · simp [sign_pos (Even.pow_pos (Nat.not_odd_iff_even.mp h₁)
                    (sub_ne_zero_of_ne hx_maxr))]
              rw [hp', jump_poly_1_mult (Or.inr hx_nroot), hmaxr_sign]
              simp [jump_poly_not_root hx_nroot]
            have hsec :
                ∑ x ∈ rootsInInterval p' a b, maxr_sign * jumpVal p' 1 x =
                maxr_sign * (∑ x ∈ rootsInInterval p' a b, jumpVal p' 1 x) :=
              Eq.symm (Finset.mul_sum (rootsInInterval p' a b) (jumpVal p' 1) maxr_sign)
            have hthird :
                maxr_sign * (∑ x ∈ rootsInInterval p' a b, jumpVal p' 1 x) =
                maxr_sign * cross p' a b:= by
              if H': rootsInInterval p' a b = ∅ then
                simp [H']
                exact Or.inr (cross_no_root hab H')
              else
                have hpp'_deg: p'.natDegree < p.natDegree := by
                  rw [hp', natDegree_mul hp'z maxrpz];
                  rw [hmaxrp]
                  simp [hmulrz]
                have hcindex: cauchyIndex p' 1 a b = cross p' a b := by
                  rw [←hp] at ih
                  exact ih p'.natDegree hpp'_deg hap' hbp' hp'z rfl
                have hf: cauchyIndex p' 1 a b = ∑ x ∈ rootsInInterval p' a b, jumpVal p' 1 x := by
                  unfold cauchyIndex
                  rfl
                rw [←hf, hcindex]
            rw [hcr_sign, hsec, hthird]
          have hcross_jp: maxr_sign * cross p' a b + jumpVal p 1 maxr = cross p a b := by
            if H': Odd (rootMultiplicity maxr p) then
              have hamaxrpltz: eval a maxrp < 0 := by
                rw [hmaxrp]
                simp
                have : a - maxr < 0 := by linarith
                exact Odd.pow_neg H' this
              have hbmaxrpgtz: eval b maxrp > 0 := by
                rw [hmaxrp]
                simp
                have : b - maxr > 0 := by linarith
                exact pow_pos this (rootMultiplicity maxr p)
              have hr: cross p a b = cross p' a b + sign (eval a p') := by
                rw [hp', cross, eval_mul, eval_mul, cross, mul_comm]
                rw [variation_mult_neg_1 (eval a maxrp) (eval a p') ((eval b p') * (eval b maxrp))
                  hamaxrpltz]
                rw [mul_comm, variation_mult_pos2 (eval b maxrp) (eval a p') (eval b p') hbmaxrpgtz]
                have : eval b maxrp * eval b p' ≠ 0 := by
                  exact mul_ne_zero hbmaxrp hbp'
                simp [this]
              have hl :
                  maxr_sign * cross p' a b + jumpVal p 1 maxr = - cross p' a b +
                  sign (eval b p') := by
                have hsrpos: (signRPos maxr p') = (eval maxr p' > 0) := by
                  rw [signRPos_rec p' maxr hp'z]
                  simp [hmaxrp']
                have hn: (eval maxr p' > 0) = (eval b p' > 0) := by
                  -- `p'` has no root in `(maxr, b)`, so its sign there is constant
                  have hprod : 0 ≤ eval maxr p' * eval b p' := by
                    by_contra! hneg
                    obtain ⟨r, hr, hrb, hrp'⟩ := exists_root_ioo_mul (le_of_lt hmaxr_root.2.2) hneg
                    have hrint : r ∈ rootsInInterval p a b := by
                      rw [hp'] at hpz ⊢
                      rw [rootsInInterval_mul a b hpz]
                      apply Finset.mem_union_left
                      simp only [rootsInInterval, Finset.mem_filter, Multiset.mem_toFinset,
                        mem_roots',
                        IsRoot.def, Set.mem_Ioo]
                      exact ⟨⟨hp'z, hrp'⟩, lt_trans hmaxr_root.2.1 hr, hrb⟩
                    have : r ≤ maxr := Finset.le_max' (rootsInInterval p a b) r hrint
                    exact absurd hr (not_lt.mpr this)
                  rw [eq_iff_iff, gt_iff_lt, gt_iff_lt, ← sign_eq_one_iff, ← sign_eq_one_iff,
                    sign_eq_sign_of_mul_nonneg hmaxrp' hbp' hprod]
                have hsrposmaxr: signRPos maxr maxrp := by
                  rw [hmaxrp]
                  exact signRPos_power maxr (rootMultiplicity maxr p)
                unfold maxr_sign jumpVal
                have haux: rootMultiplicity maxr 1 = 0 := by simp
                simp [H', haux, hpz]
                rw [mul_one, hp', signRPos_mult p' maxrp maxr hp'z maxrpz, hsrpos, hn]
                simp [hsrposmaxr]
                rcases lt_or_gt_of_ne hbp' with h | h
                · simp [not_lt.mpr h.le, sign_neg h]
                · simp [h, sign_pos h]
              have hvar :
                  variation (eval a p') (eval b p') + sign (eval a p') =
                  (-variation (eval a p') (eval b p')) + (sign (eval b p')) := by
                rw [variation_eq_of_ne_zero hap' hbp']
                rcases lt_or_gt_of_ne hap' with ha | ha <;> rcases lt_or_gt_of_ne hbp' with hb | hb
                · simp [ha, hb, sign_neg ha, sign_neg hb]
                · simp [ha, not_lt.mpr (le_of_lt hb), sign_neg ha, sign_pos hb]
                · simp [not_lt.mpr (le_of_lt ha), hb, sign_pos ha, sign_neg hb]
                · simp [not_lt.mpr (le_of_lt ha), not_lt.mpr (le_of_lt hb), sign_pos ha,
                  sign_pos hb]
              rw [hr, hl]
              unfold cross
              exact (Eq.symm hvar)
            else
              simp at H'
              have ⟨hapos, hbpos⟩ : eval a maxrp > 0 ∧ eval b maxrp > 0 := by
                rw [hmaxrp]
                rw [eval_pow, eval_pow]
                constructor
                · simp
                  have : a - maxr ≠ 0 := by clear *-hmaxr_root; linarith
                  exact Even.pow_pos H' this
                · simp
                  have : b - maxr ≠ 0 := by clear *-hmaxr_root; linarith
                  exact Even.pow_pos H' this
              have hr: cross p a b = cross p' a b := by
                unfold cross
                rw [hp', eval_mul, eval_mul]
                rw [mul_comm,
                  variation_mult_pos1 (eval a maxrp) (eval a p') (eval b p' * eval b maxrp) hapos,
                  mul_comm, variation_mult_pos2 (eval b maxrp) (eval a p') (eval b p') hbpos]
              unfold maxr_sign jumpVal
              have h_aux: rootMultiplicity maxr 1 = 0 := by simp
              have h_aux2: ¬ Odd (rootMultiplicity maxr p) := by simp [H']
              simp [h_aux2, h_aux, hpz]
              exact (Eq.symm hr)
          rw [hc_sum, hcross, hcross_jp]
        else
          have hlz : cauchyIndex p 1 a b = 0 := by
            rw [cauchyIndex, Finset.not_nonempty_iff_eq_empty.mp H, Finset.sum_empty]
          simp at H
          rw [hlz, cross_no_root hab H]

theorem cindex_poly_inverse_add {p q : Polynomial ℝ} (a b : ℝ) (hpq_coprime : IsCoprime p q) :
    cauchyIndex p q a b + cauchyIndex q p a b = cauchyIndex (q * p) 1 a b := by
  if hpqz: p = 0 ∨ q = 0 then
    rcases hpqz with rfl | rfl <;> simp
  else
    push Not at hpqz
    have ⟨hpz, hqz⟩ := hpqz
    let A := rootsInInterval p a b
    let B := rootsInInterval q a b
    have hl :
        cauchyIndex p q a b + cauchyIndex q p a b = ∑ x ∈ A, jumpVal (q * p) 1 x +
        ∑ x ∈ B, jumpVal (q*p) 1 x := by
      have hf: cauchyIndex p q a b = ∑ x ∈ A, jumpVal (q * p) 1 x := by
        unfold A cauchyIndex
        refine Finset.sum_congr rfl ?_
        intros x hx
        exact jump_poly_coprime (mem_rootsInInterval.mp hx).1.2 hpq_coprime
      have hs: cauchyIndex q p a b = ∑ x ∈ B, jumpVal (q * p) 1 x := by
       unfold B cauchyIndex
       refine Finset.sum_congr rfl ?_
       intros x hx
       rw [mul_comm]
       exact jump_poly_coprime (mem_rootsInInterval.mp hx).1.2 hpq_coprime.symm
      linarith
    have hab_union : A ∪ B = rootsInInterval (q * p) a b := by
      rw [rootsInInterval_mul a b (mul_ne_zero hqz hpz), Finset.union_comm]
    have hab_disjoint : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro y hyA hyB
      have hp_dvd : X - C y ∣ p := dvd_iff_isRoot.mpr (mem_rootsInInterval.mp hyA).1.2
      have hq_dvd : X - C y ∣ q := dvd_iff_isRoot.mpr (mem_rootsInInterval.mp hyB).1.2
      exact not_isUnit_X_sub_C y (isUnit_of_dvd_unit ((dvd_gcd_iff _ _ _).mpr ⟨hp_dvd, hq_dvd⟩)
        ((gcd_isUnit_iff p q).mpr hpq_coprime))
    rw [hl]
    unfold cauchyIndex
    unfold A B at hab_disjoint hab_union
    rw [←Finset.sum_union hab_disjoint, hab_union]

theorem cindex_poly_inverse_add_cross (p q : Polynomial ℝ) (a b : ℝ)
    (hab : a < b) (hapq : eval a (p*q) ≠ 0) (hbpq : eval b (p*q) ≠ 0) :
    cauchyIndex p q a b + cauchyIndex q p a b = variation (eval a (p * q)) (eval b (p*q)) := by
  have pneq0 : p ≠ 0 := by
    intro hfalse
    have : eval a (p * q) = 0 := by simp [hfalse]
    exact hapq this
  have qneq0 : q ≠ 0 := by
    intro hfalse
    have : eval a (p * q) = 0 := by simp [hfalse]
    exact hapq this
  let g := gcd p q
  have ⟨q', hq'⟩ : ∃q', q = g * q' := by
    unfold g; refine dvd_iff_exists_eq_mul_right.mp ?_; exact gcd_dvd_right p q
  have ⟨p', hp'⟩ : ∃p', p = g * p' := by
    unfold g; refine dvd_iff_exists_eq_mul_right.mp ?_; exact gcd_dvd_left p q
  have h_gcd : g ≠ 0 := by
    intro hfalse
    have : q = 0 := by simp [hq', hfalse]
    exact qneq0 this
  have cauchyMuls : cauchyIndex p q a b + cauchyIndex q p a b
      = cauchyIndex p' q' a b + cauchyIndex q' p' a b:= by
    rw [hp', hq', cindex_poly_mult h_gcd, cindex_poly_mult h_gcd]
  have cauchy1 : cauchyIndex p' q' a b + cauchyIndex q' p' a b
      = cauchyIndex (q' * p') 1 a b := by
        have : IsCoprime p' q' := (gcd_isUnit_iff p' q').mp (isUnit_gcd_of_eq_mul_gcd hp' hq' h_gcd)
        exact cindex_poly_inverse_add a b this
  have cauchyVar : cauchyIndex (p' * q') 1 a b
      = variation (eval a (p' * q'))  (eval b (p'*q')) := by
    have hpq : p * q = (g * g) * (p' * q') := by rw [hp', hq']; ring
    have : cauchyIndex (p' * q') 1 a b = cross (p' * q') a b := by
      have ha : eval a (p' * q') ≠ 0 :=
        right_ne_zero_of_mul (by rw [hpq, eval_mul] at hapq; exact hapq)
      have hb : eval b (p' * q') ≠ 0 :=
        right_ne_zero_of_mul (by rw [hpq, eval_mul] at hbpq; exact hbpq)
      exact cindex_poly_cross hab ha hb
    exact this
  have : variation (eval a (p' * q'))  (eval b (p'*q')) =
         variation (eval a (p * q)) (eval b (p*q)) := by
    have t1 : eval a (p * q) = eval a (g*g) * eval a (p' * q') := by
      rw [hp', hq']
      simp only [eval_mul]
      linarith
    rw[t1]
    have t2 : eval b (p * q) = eval b (g*g) * eval b (p' * q') := by
      rw[hp', hq']
      simp only [eval_mul]
      linarith
    rw[t2]
    simp at hapq
    obtain ⟨hap, haq⟩ := hapq
    have hag : eval a g ≠ 0 := by
      intro abs
      rw [hp'] at hap
      simp at hap
      obtain ⟨hag, hap'⟩ := hap
      exact hag abs
    simp at hbpq
    obtain ⟨hbp, hbq⟩ := hbpq
    have hbg : eval b g ≠ 0 := by
      intro abs
      rw [hp'] at hbp
      simp at hbp
      obtain ⟨hbg, hbp'⟩ := hbp
      exact hbg abs
    have t3 : eval a (g*g) > 0 := by simp [hag]
    have t4 : eval b (g*g) > 0 := by simp [hbg]
    rw [variation_mult_pos (eval a (g * g)) (eval b (g * g)) (eval a (p' * q')) (eval b (p' * q'))
      t3 t4]
  rw [cauchyMuls, cauchy1, mul_comm, cauchyVar, ←this]

lemma cindex_poly_congr (p q : Polynomial ℝ) (a a' b b' : ℝ) (haa' : a < a') (hb'b : b' < b)
    (ha'b' : a' < b')
    (hpx : ∀ x : ℝ, ((a < x ∧ x ≤ a') ∨ (b' ≤ x ∧ x < b)) → eval x p ≠ 0) :
    cauchyIndex p q a b = cauchyIndex p q a' b' := by
  unfold cauchyIndex
  have : rootsInInterval p a b = rootsInInterval p a' b' := by
    rw [rootsInSet_interval]
    rw [rootsInSet_interval]
    have : Set.Ioo a b = Set.Ioc a a' ∪ Set.Ioo a' b' ∪ Set.Ico b' b := by
      rw [Set.Ioc_union_Ioo_eq_Ioo (le_of_lt haa') ha'b']
      rw [Set.Ioo_union_Ico_eq_Ioo (gt_trans ha'b' haa') (le_of_lt hb'b)]
    rw [this, ← rootsInSet_cup, ← rootsInSet_cup]
    have : rootsInSet p (Set.Ioc a a') = ∅ := by
      by_contra!
      simp at this
      obtain ⟨x, hx⟩ :
          ∃ x : ℝ, x ∈ {x ∈ p.roots.toFinset | a < x ∧ x ≤ a'} := Finset.nonempty_def.mp this
      simp at hx
      obtain ⟨⟨hx11, hx12⟩, hx2, hx3⟩ := hx
      have := hpx x (Or.inl (And.intro hx2 hx3))
      exact this hx12
    rw [this]
    have : rootsInSet p (Set.Ico b' b) = ∅ := by
      by_contra!
      simp at this
      obtain ⟨x, hx⟩ :
          ∃ x : ℝ, x ∈ {x ∈ p.roots.toFinset | b' ≤ x ∧ x < b} := Finset.nonempty_def.mp this
      simp at hx
      obtain ⟨⟨hx11, hx12⟩, hx2, hx3⟩ := hx
      have := hpx x (Or.inr (And.intro hx2 hx3))
      exact this hx12
    rw [this]
    simp
  rw [this]
