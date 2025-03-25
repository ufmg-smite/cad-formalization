import Mathlib

open Polynomial

abbrev RPoly := Polynomial Real

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

theorem root_gcd (ps : List RPoly) (a : Real) :
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
