import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassDefs

/-!
# (A2) Weierstrass factorization into irreducibles — scaffolding

This file scaffolds **A2** of the codimension-1 nonsplitting plan (Zariski's Theorem 4.2.2): a
Weierstrass polynomial whose discriminant does not vanish identically factors, over the ring of
holomorphic germs, into irreducible Weierstrass polynomials. It supplies:

* `IsWeierstrassFamily H d` — the coordinate-free form of a Weierstrass polynomial: `H w` monic of
  constant degree `d`, analytic coefficients, and `H 0 = X^d`. Working with polynomial-valued
  families `H : CParam → ℂ[X]` (rather than coefficient tuples `Fin d → CParam → ℂ`) avoids dependent
  indexing when a polynomial is split into factors of *different* degrees.
* `weierstrassPoly_isWeierstrassFamily` — the canonical `weierstrassPoly d a` is such a family, so the
  factorization machinery applies to the objects appearing in `zariski_nonsplitting`.
* `WeierstrassIrreducible H d` — irreducibility in the monoid of Weierstrass germs (no nontrivial
  factorization into two positive-degree Weierstrass families).
* `weierstrass_irreducible_factorization` — **the A2 axiom**: existence of an irreducible factorization.
* `weierstrass_factorization_degree_sum` — a proved sanity check: the factor degrees sum to `d`.

The genuine analytic content of A2 (existence of the factorization over the germ ring) is the labeled
axiom; everything *around* it here is proved. Discharging A2 is a separate sub-project (germ ring =
analytic germs at `0`, an integral domain by the identity theorem; `ℂ[t]`-factorization descends from
the Weierstrass preparation / division already proved in this development).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- A **Weierstrass family**: `H w` is monic of constant degree `d`, its coefficients are analytic at
`0`, and `H 0 = X^d` (every coefficient below the leading one vanishes at `0`). This is the
coordinate-free form of `weierstrassPoly d a` with `a i 0 = 0`. -/
structure IsWeierstrassFamily (H : CParam s e → Polynomial ℂ) (d : ℕ) : Prop where
  monic : ∀ w, (H w).Monic
  degree_eq : ∀ w, (H w).natDegree = d
  coeff_analyticAt : ∀ i, AnalyticAt ℂ (fun w => (H w).coeff i) 0
  coeff_zero_vanish : ∀ i, (i : ℕ) < d → (H (0 : CParam s e)).coeff i = 0

/-- The canonical Weierstrass polynomial `weierstrassPoly d a` (coefficients analytic, vanishing at
`0`) is a Weierstrass family of degree `d`. -/
theorem weierstrassPoly_isWeierstrassFamily (d : ℕ) (a : Fin d → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0) :
    IsWeierstrassFamily (weierstrassPoly d a) d where
  monic w := weierstrassPoly_monic d a w
  degree_eq w := weierstrassPoly_natDegree d a w
  coeff_analyticAt i := by
    have hform : (fun w => (weierstrassPoly d a w).coeff i)
        = fun w => (if i = d then (1 : ℂ) else 0)
            + ∑ j : Fin d, a j w * (if i = (j : ℕ) then 1 else 0) := by
      funext w
      rw [weierstrassPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.finset_sum_coeff]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [hform]
    exact analyticAt_const.add
      (Finset.analyticAt_fun_sum _ fun j _ => (ha_an j).mul analyticAt_const)
  coeff_zero_vanish i hi := by
    have h0 : weierstrassPoly d a (0 : CParam s e) = X ^ d := by
      rw [weierstrassPoly]
      simp only [ha0, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [h0, Polynomial.coeff_X_pow, if_neg (by omega)]

/-- `H 0 = X^d` for a Weierstrass family (the section base point is `t ↦ t^d`). -/
theorem IsWeierstrassFamily.eval_zero {H : CParam s e → Polynomial ℂ} {d : ℕ}
    (hH : IsWeierstrassFamily H d) : H (0 : CParam s e) = X ^ d := by
  ext i
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy i d with hlt | heq | hgt
  · rw [if_neg (by omega), hH.coeff_zero_vanish i hlt]
  · subst heq
    rw [if_pos rfl]
    have hm := (hH.monic 0).coeff_natDegree
    rwa [hH.degree_eq 0] at hm
  · rw [if_neg (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hH.degree_eq 0]; omega)]

/-- **`H` is Weierstrass-irreducible of degree `d`**: it has positive degree and admits no
factorization into two positive-degree Weierstrass families (as germs at `0`). This is irreducibility
in the monoid of Weierstrass germs. -/
def WeierstrassIrreducible (H : CParam s e → Polynomial ℂ) (d : ℕ) : Prop :=
  1 ≤ d ∧
    ¬ ∃ (d₁ d₂ : ℕ) (H₁ H₂ : CParam s e → Polynomial ℂ),
      1 ≤ d₁ ∧ 1 ≤ d₂ ∧ IsWeierstrassFamily H₁ d₁ ∧ IsWeierstrassFamily H₂ d₂ ∧
      (∀ᶠ w in 𝓝 (0 : CParam s e), H w = H₁ w * H₂ w)

/-- In a Weierstrass factorization `H = H₁·H₂` (as germs), the degrees add: `d = d₁ + d₂`. (Evaluate
at `0`, where everything is monic and degrees of a product of monics add.) -/
theorem weierstrass_mul_degree {H H₁ H₂ : CParam s e → Polynomial ℂ} {d d₁ d₂ : ℕ}
    (hH : IsWeierstrassFamily H d) (hH₁ : IsWeierstrassFamily H₁ d₁) (hH₂ : IsWeierstrassFamily H₂ d₂)
    (heq : ∀ᶠ w in 𝓝 (0 : CParam s e), H w = H₁ w * H₂ w) : d = d₁ + d₂ := by
  have h0 : H (0 : CParam s e) = H₁ 0 * H₂ 0 := heq.self_of_nhds
  have hd := hH.degree_eq 0
  rw [h0, Polynomial.natDegree_mul (hH₁.monic 0).ne_zero (hH₂.monic 0).ne_zero,
    hH₁.degree_eq 0, hH₂.degree_eq 0] at hd
  exact hd.symm

/-- The product of a concatenated factor list splits as the product of the two parts (pointwise). -/
theorem prod_append_eval {k₁ k₂ : ℕ} (fac₁ : Fin k₁ → (CParam s e → Polynomial ℂ))
    (fac₂ : Fin k₂ → (CParam s e → Polynomial ℂ)) (w : CParam s e) :
    (∏ j : Fin (k₁ + k₂), Fin.append fac₁ fac₂ j w)
      = (∏ i : Fin k₁, fac₁ i w) * (∏ i : Fin k₂, fac₂ i w) := by
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [Fin.append_left]
  · exact Finset.prod_congr rfl fun i _ => by rw [Fin.append_right]

/-- **(A2) Weierstrass factorization into irreducibles — THEOREM.** A Weierstrass family of positive
degree factors, as a germ at `0`, into finitely many *irreducible* Weierstrass families.

Proved by well-founded recursion on the degree (no germ ring needed for *existence* — only uniqueness,
not claimed here, requires it): if `H` is already irreducible the trivial one-factor factorization
works; otherwise `H = H₁·H₂` with `1 ≤ deg Hᵢ < deg H` (degrees add), and the two recursive
factorizations are concatenated. -/
theorem weierstrass_irreducible_factorization
    (H : CParam s e → Polynomial ℂ) (d : ℕ) (hH : IsWeierstrassFamily H d) (hd : 1 ≤ d) :
    ∃ (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ)),
      0 < k ∧ (∀ j, 1 ≤ deg j) ∧
      (∀ j, IsWeierstrassFamily (fac j) (deg j)) ∧
      (∀ j, WeierstrassIrreducible (fac j) (deg j)) ∧
      (∀ᶠ w in 𝓝 (0 : CParam s e), H w = ∏ j : Fin k, fac j w) := by
  have key : ∀ d : ℕ, ∀ H : CParam s e → Polynomial ℂ, IsWeierstrassFamily H d → 1 ≤ d →
      ∃ (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ)),
        0 < k ∧ (∀ j, 1 ≤ deg j) ∧ (∀ j, IsWeierstrassFamily (fac j) (deg j)) ∧
        (∀ j, WeierstrassIrreducible (fac j) (deg j)) ∧
        (∀ᶠ w in 𝓝 (0 : CParam s e), H w = ∏ j : Fin k, fac j w) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro H hH hd
      by_cases hirr : WeierstrassIrreducible H d
      · exact ⟨1, fun _ => d, fun _ => H, one_pos, fun _ => hd, fun _ => hH, fun _ => hirr,
          Filter.Eventually.of_forall fun w => by simp [Fin.prod_univ_one]⟩
      · have hex : ∃ (d₁ d₂ : ℕ) (H₁ H₂ : CParam s e → Polynomial ℂ),
            1 ≤ d₁ ∧ 1 ≤ d₂ ∧ IsWeierstrassFamily H₁ d₁ ∧ IsWeierstrassFamily H₂ d₂ ∧
            (∀ᶠ w in 𝓝 (0 : CParam s e), H w = H₁ w * H₂ w) := by
          by_contra hne; exact hirr ⟨hd, hne⟩
        obtain ⟨d₁, d₂, H₁, H₂, hd₁, hd₂, hH₁, hH₂, heq⟩ := hex
        have hdsum : d = d₁ + d₂ := weierstrass_mul_degree hH hH₁ hH₂ heq
        obtain ⟨k₁, deg₁, fac₁, hk₁, hdeg₁, hfam₁, hirr₁, heq₁⟩ := IH d₁ (by omega) H₁ hH₁ hd₁
        obtain ⟨k₂, deg₂, fac₂, hk₂, hdeg₂, hfam₂, hirr₂, heq₂⟩ := IH d₂ (by omega) H₂ hH₂ hd₂
        refine ⟨k₁ + k₂, Fin.append deg₁ deg₂, Fin.append fac₁ fac₂, by omega, ?_, ?_, ?_, ?_⟩
        · intro j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simpa only [Fin.append_left] using hdeg₁ i
          · simpa only [Fin.append_right] using hdeg₂ i
        · intro j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simpa only [Fin.append_left] using hfam₁ i
          · simpa only [Fin.append_right] using hfam₂ i
        · intro j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simpa only [Fin.append_left] using hirr₁ i
          · simpa only [Fin.append_right] using hirr₂ i
        · filter_upwards [heq, heq₁, heq₂] with w hw hw1 hw2
          rw [hw, hw1, hw2, prod_append_eval]
  exact key d H hH hd
