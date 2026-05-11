import Cad.Multivariate.ProjectionTheorem.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Discriminant of a squarefree polynomial is nonzero

We prove that for `f : PolyR n` (i.e., `f ∈ R[x]` where `R = MvPolynomial (Fin n) ℝ`),
if `f` is squarefree and has positive degree, then `Polynomial.discr f ≠ 0`.

## Proof strategy

1. Let `K = FractionRing R`. Since `R` is a UFD of characteristic 0, `K` is a perfect field.
2. Map `f` to `K[x]` via `algebraMap R K`. The image is still squarefree (Gauss lemma).
3. Over a perfect field, squarefree ↔ separable (`PerfectField.separable_iff_squarefree`).
4. Separable means `IsCoprime f_K f_K'`, so `resultant f_K f_K' ≠ 0`.
5. By `resultant_deriv`, this resultant equals `±leadingCoeff · discr`, so `discr f_K ≠ 0`.
6. Since `discr` commutes with the ring map (via `resultant_map_map`) and `algebraMap` is
   injective, we conclude `discr f ≠ 0` in `R`.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

private abbrev K (n : ℕ) := FractionRing (MvPolynomial (Fin n) ℝ)

private def φ (n : ℕ) : MvPolynomial (Fin n) ℝ →+* K n :=
  algebraMap (MvPolynomial (Fin n) ℝ) (K n)

private lemma φ_injective : Function.Injective (φ n) :=
  IsFractionRing.injective _ _

private instance : CharZero (K n) :=
  charZero_of_injective_ringHom (φ_injective (n := n))

private instance : IsDomain (K n) := inferInstance

/-- Squarefree polynomials over a UFD remain squarefree when mapped to the fraction field.

**Proof sketch**: Suppose `p² | f.map φ` for monic irreducible `p ∈ K[X]`. Since `R` is
integrally closed (UFD), by `IsIntegrallyClosed.eq_map_mul_C_of_dvd`, the monic `p` lifts
to a monic `q ∈ R[X]` with `q.map φ = p`. By `Monic.irreducible_iff_irreducible_map_fraction_map`,
`q` is irreducible in `R[X]`. Then `q.map φ ∣ f.map φ` and (by the monic dvd lemma)
`q ∣ f` in `R[X]`. Similarly `q² ∣ f`. This contradicts `Squarefree f`. -/
private lemma squarefree_map_fractionRing (f : Polynomial (MvPolynomial (Fin n) ℝ))
    (hsf : Squarefree f) :
    Squarefree (f.map (φ n)) := by
  have hinj := φ_injective (n := n)
  have hfne : f ≠ 0 := hsf.ne_zero
  have hfKne : f.map (φ n) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hfne
  rw [squarefree_iff_no_irreducibles hfKne]
  intro p hp ⟨r, hr⟩
  -- p is irreducible in K[X], p * p * r = f.map φ
  -- Step 1: integer normalization of p
  set q₀ := IsLocalization.integerNormalization
    (nonZeroDivisors (MvPolynomial (Fin n) ℝ)) p
  obtain ⟨⟨c, hc_mem⟩, hc_eq⟩ := IsLocalization.integerNormalization_map_to_map
    (nonZeroDivisors (MvPolynomial (Fin n) ℝ)) p
  -- q₀.map φ = c • p, with c ∈ R⁰ (nonzero)
  have hq₀ne : q₀ ≠ 0 := by
    intro h
    have := IsFractionRing.integerNormalization_eq_zero_iff.mp h
    exact hp.ne_zero this
  -- Step 2: primPart
  have : NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ) := Classical.arbitrary _
  set q := q₀.primPart
  have hq_prim : q.IsPrimitive := isPrimitive_primPart q₀
  -- q₀ = C(content q₀) * q
  have hq₀_eq : q₀ = Polynomial.C q₀.content * q := q₀.eq_C_content_mul_primPart
  -- Step 3: q.map φ is associated to p, hence irreducible
  have hcne : (c : MvPolynomial (Fin n) ℝ) ≠ 0 := nonZeroDivisors.ne_zero hc_mem
  have hcont_ne : q₀.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
  have hφcont_ne : (φ n) q₀.content ≠ 0 := fun h => hcont_ne (hinj (by simp [h]))
  have hφc_ne : (φ n) c ≠ 0 := fun h => hcne (hinj (by simp [h]))
  -- q₀.map φ = C(φ(content q₀)) * q.map φ
  have hq₀_map : q₀.map (φ n) =
      Polynomial.C ((φ n) q₀.content) * q.map (φ n) := by
    conv_lhs => rw [hq₀_eq]
    simp [Polynomial.map_mul]
  -- Also q₀.map φ = c • p = C(φ c) * p
  have hq₀_map' : q₀.map (φ n) = Polynomial.C ((φ n) c) * p := by
    have : q₀.map (algebraMap _ (K n)) = c • p := hc_eq
    rw [show (φ n) = algebraMap _ (K n) from rfl] at hq₀_map ⊢
    rw [this, Algebra.smul_def, Polynomial.algebraMap_apply]
  -- So q.map φ is associated to p
  have hassoc : Associated p (q.map (φ n)) := by
    have heq : Polynomial.C ((φ n) q₀.content) * q.map (φ n) =
        Polynomial.C ((φ n) c) * p := by
      rw [← hq₀_map, ← hq₀_map']
    -- From heq: p = C(�� c)⁻¹ * C(φ(content q₀)) * q.map φ
    rw [Associated.comm]
    have hcoeff_unit : IsUnit (Polynomial.C ((φ n) q₀.content * ((φ n) c)⁻¹) :
        Polynomial (K n)) := by
      exact isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero hφcont_ne (inv_ne_zero hφc_ne)))
    obtain ⟨u, hu⟩ := hcoeff_unit
    exact ⟨u, by
      rw [show (u : Polynomial (K n)) = Polynomial.C ((φ n) q₀.content * ((φ n) c)⁻¹) from hu]
      calc q.map (φ n) * Polynomial.C ((φ n) q₀.content * ((φ n) c)⁻¹)
          = Polynomial.C ((φ n) c)⁻¹ *
            (Polynomial.C ((φ n) q₀.content) * q.map (φ n)) := by
              rw [Polynomial.C_mul]; ring
        _ = Polynomial.C ((φ n) c)⁻¹ * (Polynomial.C ((φ n) c) * p) := by rw [heq]
        _ = p := by rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hφc_ne,
                         Polynomial.C_1, one_mul]⟩
  have hq_map_irr : Irreducible (q.map (φ n)) := hassoc.irreducible hp
  -- Step 4: q is irreducible in R[X] (Gauss lemma)
  have hq_irr : Irreducible q :=
    hq_prim.irreducible_of_irreducible_map_of_injective hinj hq_map_irr
  -- Step 5: q * q | f
  -- First: (q.map φ) * (q.map φ) | f.map φ
  have hq_map_sq_dvd : q.map (φ n) * q.map (φ n) ∣ f.map (φ n) := by
    have : p * p ∣ f.map (φ n) := ⟨r, hr⟩
    exact (Associated.mul_mul hassoc hassoc).dvd_iff_dvd_left.mp this
  -- (q * q).map φ | f.map φ
  have hqq_map_dvd : (q * q).map (φ n) ∣ f.map (φ n) := by
    rwa [Polynomial.map_mul]
  -- Now pull back using IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
  have hqq_prim : (q * q).IsPrimitive := hq_prim.mul hq_prim
  -- We need to show q * q | f. Use primPart approach.
  have hf_prim := isPrimitive_primPart f
  -- (q * q).map φ | f.primPart.map φ
  have hqq_dvd_primPart_map : (q * q).map (φ n) ∣ f.primPart.map (φ n) := by
    have hfcont_ne : f.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
    have hφfcont_ne : (φ n) f.content ≠ 0 := fun h => hfcont_ne (hinj (by simp [h]))
    have hmap_eq : f.map (φ n) =
        Polynomial.C ((φ n) f.content) * f.primPart.map (φ n) := by
      conv_lhs => rw [f.eq_C_content_mul_primPart]
      simp [Polynomial.map_mul]
    rw [hmap_eq] at hqq_map_dvd
    rwa [Polynomial.dvd_C_mul hφfcont_ne] at hqq_map_dvd
  have hqq_dvd_primPart : q * q ∣ f.primPart :=
    hqq_prim.dvd_of_fraction_map_dvd_fraction_map hf_prim hqq_dvd_primPart_map
  have hqq_dvd_f : q * q ∣ f := (hqq_prim.dvd_primPart_iff_dvd hfne).mp hqq_dvd_primPart
  -- Step 6: Contradiction with squarefreeness
  exact hq_irr.not_isUnit (hsf q hqq_dvd_f)

/-- In characteristic 0, the derivative of a polynomial of degree ≥ 1 has degree exactly
    `natDegree f - 1`. -/
private lemma natDegree_derivative_eq
    {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (f : Polynomial S) (hf : 0 < f.natDegree) :
    f.derivative.natDegree = f.natDegree - 1 := by
  have hf_ne : f ≠ 0 := ne_zero_of_natDegree_gt hf
  apply le_antisymm (natDegree_derivative_le f)
  have hlc : f.derivative.coeff (f.natDegree - 1) ≠ 0 := by
    rw [coeff_derivative]
    have hsub : f.natDegree - 1 + 1 = f.natDegree := Nat.succ_pred_eq_of_pos hf
    have h1 : f.coeff (f.natDegree - 1 + 1) ≠ 0 := by
      rw [hsub]; exact leadingCoeff_ne_zero.mpr hf_ne
    have h2 : (↑(f.natDegree - 1) : S) + 1 ≠ 0 := by
      suffices h : (↑(f.natDegree - 1 + 1) : S) ≠ 0 by
        simpa [Nat.cast_add, Nat.cast_one] using h
      rw [hsub]; exact Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero h1 h2
  exact Polynomial.le_natDegree_of_ne_zero hlc

/-- The discriminant commutes with injective ring maps (when degree is positive).
    Proved via `resultant_map_map` and `resultant_deriv`. -/
private lemma discr_map_eq
    (f : Polynomial (MvPolynomial (Fin n) ℝ)) (hf : f ≠ 0) (hpos : 0 < f.natDegree) :
    Polynomial.discr (f.map (φ n)) = (φ n) (Polynomial.discr f) := by
  have hinj := φ_injective (n := n)
  have hdeg : (f.map (φ n)).natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have hfK_ne : f.map (φ n) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf
  have hf_deg : (0 : WithBot ℕ) < f.degree := by
    rw [Polynomial.degree_eq_natDegree hf]; exact_mod_cast hpos
  have hfK_deg : (0 : WithBot ℕ) < (f.map (φ n)).degree := by
    rw [Polynomial.degree_eq_natDegree hfK_ne, hdeg]; exact_mod_cast hpos
  have lhs := Polynomial.resultant_deriv (f := f.map (φ n)) hfK_deg
  have rhs := Polynomial.resultant_deriv (f := f) hf_deg
  have hmap : Polynomial.resultant (f.map (φ n)) (f.map (φ n)).derivative
      (f.map (φ n)).natDegree ((f.map (φ n)).natDegree - 1) =
      (φ n) (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)) := by
    conv_lhs => rw [show (f.map (φ n)).derivative = (f.derivative).map (φ n) from
      Polynomial.derivative_map f (φ n)]
    rw [hdeg]
    exact Polynomial.resultant_map_map (f := f) (g := f.derivative)
      (m := f.natDegree) (n := f.natDegree - 1) (φ n)
  rw [lhs, rhs] at hmap
  simp only [map_mul, map_pow, map_neg, map_one] at hmap
  have hlc : Polynomial.leadingCoeff (f.map (φ n)) = (φ n) f.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_injective hinj f
  rw [hlc, hdeg] at hmap
  -- hmap : (-1)^k * φ(lc) * discr(f.map φ) = (-1)^k * φ(lc) * φ(discr f)
  have hne : (-1 : K n) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      (φ n) f.leadingCoeff ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    · exact fun h => (leadingCoeff_ne_zero.mpr hf) (hinj (by simp [h]))
  exact mul_left_cancel₀ hne hmap

/-- **Theorem**: The discriminant of a squarefree polynomial with positive degree is nonzero. -/
theorem discr_ne_zero_of_squarefree
    (f : PolyR n)
    (hsf : Squarefree f) (hpos : 0 < f.natDegree) :
    Polynomial.discr f ≠ 0 := by
  set fK := f.map (φ n)
  have hf_ne : f ≠ 0 := ne_zero_of_natDegree_gt hpos
  have hdeg : fK.natDegree = f.natDegree :=
    natDegree_map_eq_of_injective φ_injective f
  have hfK_ne : fK ≠ 0 := (Polynomial.map_ne_zero_iff φ_injective).mpr hf_ne
  have hfK_pos : 0 < fK.natDegree := hdeg ▸ hpos
  have hfK_sf : Squarefree fK := squarefree_map_fractionRing f hsf
  have hfK_sep : fK.Separable := PerfectField.separable_iff_squarefree.mpr hfK_sf
  have hcop : IsCoprime fK fK.derivative := hfK_sep
  have hres : Polynomial.resultant fK fK.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero fK fK.derivative hcop
  have hdeg_der : fK.derivative.natDegree = fK.natDegree - 1 :=
    natDegree_derivative_eq fK hfK_pos
  -- The default-arg resultant uses fK.derivative.natDegree which equals fK.natDegree - 1
  have hres_eq : Polynomial.resultant fK fK.derivative =
      (-1) ^ (fK.natDegree * (fK.natDegree - 1) / 2) * fK.leadingCoeff *
        Polynomial.discr fK := by
    have hfK_deg_pos : (0 : WithBot ℕ) < fK.degree := by
      rw [Polynomial.degree_eq_natDegree hfK_ne]; exact_mod_cast hfK_pos
    -- resultant with defaults = resultant fK fK.derivative fK.natDegree fK.derivative.natDegree
    -- = resultant fK fK.derivative fK.natDegree (fK.natDegree - 1) by hdeg_der
    change Polynomial.resultant fK fK.derivative fK.natDegree fK.derivative.natDegree = _
    rw [hdeg_der]
    exact Polynomial.resultant_deriv hfK_deg_pos
  have hdisc_K : Polynomial.discr fK ≠ 0 := by
    intro hdisc
    apply hres
    rw [hres_eq, hdisc, mul_zero]
  intro hdisc
  apply hdisc_K
  rw [discr_map_eq f hf_ne hpos, hdisc, map_zero]

end
