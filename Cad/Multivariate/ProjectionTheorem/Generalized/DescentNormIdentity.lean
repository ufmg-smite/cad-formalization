import Cad.Multivariate.ProjectionTheorem.Generalized.MembershipDescent
import Cad.Multivariate.ProjectionTheorem.Generalized.Lifting
import Mathlib.Order.Filter.Germ.Basic

/-!
# Phase D1 descent — Step 3b: the norm identity

The final connector. From the descent's `=ᶠ` membership `polyToFun (C P) =ᶠ polyToFun (A'·h + B'·h')`
(output of `descent_membership`), produce the **norm identity** `P^m =ᶠ weierstrassResFun·Q` with `Q`
analytic — exactly the `hnorm` hypothesis of `DiscOrder.weierstrassDisc_order_const_along_section`.

Route: `polyToFun`-injectivity ⟹ coefficient-wise germ equality ⟹ an exact `⟨h,h'⟩` membership over
the **analytic-germ ring `𝒪` on `CParam s e`** ⟹ `norm_identity_elim` over `𝒪` ⟹
`P^m = resultant(h,h')·Q` with `Q ∈ 𝒪` (analytic); `resultant_map_map` over the germ coercion
identifies `resultant` with `weierstrassResFun`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- Abbreviation for the germ coercion ring hom on `CParam s e`. -/
abbrev germHom (s e : ℕ) : (CParam s e → ℂ) →+* Germ (𝓝 (0 : CParam s e)) ℂ :=
  Germ.coeRingHom _

/-- The analytic-germ ring `𝒪` on `CParam s e`: germs at `0` admitting an analytic representative. -/
def AnalyticGermP (s e : ℕ) : Subring (Germ (𝓝 (0 : CParam s e)) ℂ) where
  carrier := { g | ∃ f : CParam s e → ℂ, AnalyticAt ℂ f 0 ∧ germHom s e f = g }
  zero_mem' := ⟨0, analyticAt_const, map_zero _⟩
  one_mem' := ⟨1, analyticAt_const, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩; exact ⟨f₁ + f₂, hf₁.add hf₂, map_add _ _ _⟩
  mul_mem' := by
    rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩; exact ⟨f₁ * f₂, hf₁.mul hf₂, map_mul _ _ _⟩
  neg_mem' := by rintro _ ⟨f, hf, rfl⟩; exact ⟨-f, hf.neg, map_neg _ _⟩

lemma analyticCoeffs_germ_mem {p : (CParam s e → ℂ)[X]} (hp : AnalyticCoeffs p) :
    (↑(p.map (germHom s e)).coeffs : Set (Germ (𝓝 (0 : CParam s e)) ℂ))
      ⊆ (AnalyticGermP s e : Set (Germ (𝓝 (0 : CParam s e)) ℂ)) := by
  intro x hx
  obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
  rw [Polynomial.coeff_map]
  exact ⟨p.coeff n, hp n, rfl⟩

/-- The germ ring `Germ (𝓝 0) ℂ` on `CParam` has characteristic zero (nat-casts are germs of
nonzero constants on the `NeBot` neighbourhood filter). -/
instance : CharZero (Germ (𝓝 (0 : CParam s e)) ℂ) where
  cast_injective := by
    intro n m hnm
    rw [← map_natCast (germHom s e) n, ← map_natCast (germHom s e) m] at hnm
    obtain ⟨x, hx⟩ := (Germ.coe_eq.mp hnm).exists
    simpa using hx

/-- **Step 3b — the norm identity.** From the descent's `=ᶠ` membership produce `P^m =ᶠ
weierstrassResFun·Q` with `Q` analytic. -/
theorem descent_norm_identity {m : ℕ} (hm : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0)
    (P : CParam s e → ℂ) (hP_an : AnalyticAt ℂ P 0)
    (A' B' : (CParam s e → ℂ)[X]) (hA' : AnalyticCoeffs A') (hB' : AnalyticCoeffs B')
    (hmem : polyToFun s e (Polynomial.C P) =ᶠ[𝓝 0]
      polyToFun s e (A' * weierstrassPolyFun m a + B' * derivative (weierstrassPolyFun m a))) :
    ∃ Q : CParam s e → ℂ, AnalyticAt ℂ Q 0 ∧
      (fun w => P w ^ m) =ᶠ[𝓝 (0 : CParam s e)] fun w => weierstrassResFun m a w * Q w := by
  classical
  set γ := germHom s e with hγ
  set h := weierstrassPolyFun m a with hh
  have hmonic : h.Monic := weierstrassPolyFun_monic m a
  have hh_an : AnalyticCoeffs h := analyticCoeffs_weierstrassPolyFun a ha_an
  -- coefficient-wise germ equality from `polyToFun`-injectivity
  have hzero : polyToFun s e (Polynomial.C P
      - (A' * h + B' * derivative h)) =ᶠ[𝓝 0] 0 := by
    rw [map_sub]; filter_upwards [hmem] with zt hzt
    simp only [Pi.sub_apply, Pi.zero_apply, hzt, sub_self]
  have hcoeff : ∀ k, (Polynomial.C P - (A' * h + B' * derivative h)).coeff k
      =ᶠ[𝓝 (0 : CParam s e)] 0 := fun k => polyToFun_coeff_eventuallyEq_zero _ hzero k
  -- the membership over the germ ring `Germ`
  have hGermEq : (Polynomial.C P).map γ
      = (A' * h + B' * derivative h).map γ := by
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    have := hcoeff k
    rw [← sub_eq_zero, ← Germ.coe_zero, ← map_sub]
    show γ ((Polynomial.C P).coeff k - (A' * h + B' * derivative h).coeff k) = γ 0
    rw [show (Polynomial.C P).coeff k - (A' * h + B' * derivative h).coeff k
        = (Polynomial.C P - (A' * h + B' * derivative h)).coeff k from by rw [Polynomial.coeff_sub]]
    exact (Germ.coe_eq.mpr (by simpa using this))
  -- expand `hGermEq` into the germ-ideal membership form
  have hGermEq2 : Polynomial.C (γ P)
      = (A'.map γ) * (h.map γ) + (B'.map γ) * derivative (h.map γ) := by
    rw [← Polynomial.map_C, hGermEq, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.derivative_map]
  -- restrict to the analytic-germ ring `𝒪`
  set 𝒪 := AnalyticGermP s e with h𝒪
  set hS := (h.map γ).toSubring 𝒪 (analyticCoeffs_germ_mem hh_an) with hhS
  set A'S := (A'.map γ).toSubring 𝒪 (analyticCoeffs_germ_mem hA') with hA'S
  set B'S := (B'.map γ).toSubring 𝒪 (analyticCoeffs_germ_mem hB') with hB'S
  have hmapS_h : hS.map 𝒪.subtype = h.map γ := map_toSubring _ _ _
  have hmapS_A : A'S.map 𝒪.subtype = A'.map γ := map_toSubring _ _ _
  have hmapS_B : B'S.map 𝒪.subtype = B'.map γ := map_toSubring _ _ _
  have hinj : Function.Injective 𝒪.subtype := Subtype.coe_injective
  have hS_monic : hS.Monic :=
    hinj.monic_map_iff.mpr (by rw [hmapS_h]; exact hmonic.map γ)
  have hSnd : hS.natDegree = m := by
    rw [← Polynomial.natDegree_map_eq_of_injective hinj hS, hmapS_h,
      hmonic.natDegree_map, hh, weierstrassPolyFun_natDegree m a]
  haveI : CharZero (↥𝒪) := ⟨fun a b hab => by
    have := congrArg 𝒪.subtype hab; rwa [map_natCast, map_natCast, Nat.cast_inj] at this⟩
  -- `(derivative hS).natDegree = m − 1`: `≤` is `natDegree_derivative_le`; `≥` since the
  -- `(m−1)`-coefficient is `m·1 = m ≠ 0` (char-0 of the analytic-germ ring).
  have hdSnd : (derivative hS).natDegree = m - 1 := by
    refine le_antisymm (le_trans (natDegree_derivative_le hS) (by rw [hSnd])) ?_
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hm,
      show hS.coeff m = 1 from by rw [← hSnd]; exact hS_monic.coeff_natDegree, one_mul]
    exact_mod_cast Nat.succ_ne_zero (m - 1)
  set PS : 𝒪 := ⟨γ P, P, hP_an, rfl⟩ with hPS
  have hPSval : 𝒪.subtype PS = γ P := rfl
  -- membership over `𝒪[X]`
  have hmemS_eq : A'S * hS + B'S * derivative hS = Polynomial.C PS := by
    apply Polynomial.map_injective 𝒪.subtype hinj
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hmapS_A, hmapS_B, hmapS_h, Polynomial.map_C]
    exact hGermEq2.symm
  obtain ⟨QS, hQS⟩ := norm_identity_elim (↥𝒪) hS (derivative hS) hS_monic PS
    ((Ideal.mem_span_pair).mpr ⟨A'S, B'S, hmemS_eq⟩)
  -- `QS` has an analytic representative `q`
  obtain ⟨q, hq_an, hq_eq⟩ := QS.2
  refine ⟨q, hq_an, ?_⟩
  -- `𝒪.subtype (resultant hS (derivative hS) [defaults]) = γ (weierstrassResFun m a)`, via
  -- `resultant_map_map` over `subtype` then `γ`, using `hSnd`,`hdSnd` to match degree args `(m,m−1)`.
  -- REMAINING BOOKKEEPING (resultant degree-arg `rw` plumbing).
  -- via `resultant_map_map` over `subtype` then `γ`, with `hSnd`,`hdSnd` matching degree args `(m,m−1)`.
  have hres : 𝒪.subtype (Polynomial.resultant hS (derivative hS)
        hS.natDegree (derivative hS).natDegree) = γ (weierstrassResFun m a) := by
    rw [← Polynomial.resultant_map_map hS (derivative hS) hS.natDegree (derivative hS).natDegree
        𝒪.subtype, hmapS_h,
      show (derivative hS).map 𝒪.subtype = derivative (h.map γ) from by
        rw [← Polynomial.derivative_map, hmapS_h],
      hSnd, hdSnd]
    show Polynomial.resultant (h.map γ) (derivative (h.map γ)) m (m - 1) = _
    rw [show weierstrassResFun m a = Polynomial.resultant h (derivative h) m (m - 1) from rfl,
      Polynomial.derivative_map, Polynomial.resultant_map_map h (derivative h) m (m - 1) γ]
  -- map the norm identity back to germs and conclude
  have hmapId := congrArg 𝒪.subtype hQS
  rw [map_mul, map_pow, hres, hSnd, hPSval,
    show 𝒪.subtype QS = γ q from hq_eq.symm] at hmapId
  have hfinal : germHom s e (fun w => P w ^ m)
      = germHom s e (fun w => weierstrassResFun m a w * q w) := by
    rw [show (fun w => P w ^ m) = (P ^ m : CParam s e → ℂ) from rfl, map_pow,
      show (fun w => weierstrassResFun m a w * q w) = (weierstrassResFun m a * q : CParam s e → ℂ)
        from rfl, map_mul]
    exact hmapId
  exact Germ.coe_eq.mp hfinal

end
