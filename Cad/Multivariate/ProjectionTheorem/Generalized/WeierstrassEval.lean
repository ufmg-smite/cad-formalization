import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassZariskiAxioms
import Cad.Multivariate.ProjectionTheorem.OrderMulAnalytic

/-!
# Evaluation infrastructure: the Weierstrass polynomial over the pointwise function ring

The norm identity `norm_identity_elim` is generic over any `CommRing`. For Phase D it is applied
over the **pointwise function ring** `CParam s e → ℂ`: the monic Weierstrass polynomial with
*function* coefficients, `weierstrassPolyFun m a ∈ (CParam s e → ℂ)[X]`, whose `resultant` against
its derivative is a single function `weierstrassResFun m a : CParam s e → ℂ`.

This file provides the **evaluation transport** connecting that algebraic object to the
pointwise data the Zariski axiom speaks about:

* `weierstrassPolyFun_map_eval` — evaluating coefficients at `w` recovers `weierstrassPoly m a w`.
* `weierstrassResFun_apply` — `weierstrassResFun m a w = resultant (weierstrassPoly m a w) …`.
* `weierstrassResFun_eq_discFn` — for the monic Weierstrass polynomial, `weierstrassResFun` equals
  `±(weierstrassDiscFn)` pointwise (a sign unit), so they share vanishing order.

The transport is the ring-hom naturality of the resultant (`resultant_map_map`) under the
evaluation hom `Pi.evalRingHom`, plus `resultant_deriv` (resultant↔discriminant for monic `f`).
-/

noncomputable section

open Polynomial

variable {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))

/-- The monic degree-`m` Weierstrass polynomial with **function** coefficients, living in the
polynomial ring over the pointwise function ring `CParam s e → ℂ`. -/
def weierstrassPolyFun : Polynomial (CParam s e → ℂ) :=
  X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)

/-- Evaluating the function coefficients at a point `w` recovers the pointwise Weierstrass
polynomial `weierstrassPoly m a w`. -/
lemma weierstrassPolyFun_map_eval (w : CParam s e) :
    (weierstrassPolyFun m a).map (Pi.evalRingHom (fun _ : CParam s e => ℂ) w)
      = weierstrassPoly m a w := by
  simp only [weierstrassPolyFun, weierstrassPoly, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- The degree of the function-coefficient Weierstrass polynomial sum part is `< m`. -/
lemma weierstrassPolyFun_lower_degree_lt :
    (∑ i : Fin m, C (a i) * X ^ (i : ℕ)).degree < (m : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe m)).mpr ?_)
  intro i _
  have hi : (i : ℕ) < m := i.2
  calc (C (a i) * X ^ (i : ℕ)).degree
      ≤ (C (a i)).degree + (X ^ (i : ℕ)).degree := degree_mul_le _ _
    _ ≤ 0 + ((i : ℕ) : WithBot ℕ) := add_le_add degree_C_le (degree_X_pow _).le
    _ = ((i : ℕ) : WithBot ℕ) := zero_add _
    _ < ((m : ℕ) : WithBot ℕ) := by exact_mod_cast hi

/-- The function-coefficient Weierstrass polynomial is monic. -/
lemma weierstrassPolyFun_monic : (weierstrassPolyFun m a).Monic :=
  monic_X_pow_add (weierstrassPolyFun_lower_degree_lt m a)

/-- The function-coefficient Weierstrass polynomial has degree exactly `m`. -/
lemma weierstrassPolyFun_degree : (weierstrassPolyFun m a).degree = (m : WithBot ℕ) := by
  rw [weierstrassPolyFun,
    degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact weierstrassPolyFun_lower_degree_lt m a),
    degree_X_pow]

/-- The function-coefficient Weierstrass polynomial has natDegree `m`. -/
lemma weierstrassPolyFun_natDegree : (weierstrassPolyFun m a).natDegree = m :=
  natDegree_eq_of_degree_eq_some (weierstrassPolyFun_degree m a)

/-- The resultant of the function-coefficient Weierstrass polynomial against its derivative — a
single function `CParam s e → ℂ`. (Discriminant of the family, up to a sign unit.) -/
def weierstrassResFun : CParam s e → ℂ :=
  resultant (weierstrassPolyFun m a) (derivative (weierstrassPolyFun m a)) m (m - 1)

/-- The resultant function evaluated at `w` is the pointwise resultant of `weierstrassPoly m a w`
against its derivative. -/
lemma weierstrassResFun_apply (w : CParam s e) :
    weierstrassResFun m a w
      = resultant (weierstrassPoly m a w) (derivative (weierstrassPoly m a w)) m (m - 1) := by
  show (Pi.evalRingHom (fun _ : CParam s e => ℂ) w) (weierstrassResFun m a) = _
  rw [weierstrassResFun, ← resultant_map_map, ← derivative_map, weierstrassPolyFun_map_eval]

/-- For the monic Weierstrass polynomial, the resultant function equals `(-1)^k · discriminant`
pointwise (where `k = m(m-1)/2`); the two differ only by the sign unit, hence share vanishing
order. -/
lemma weierstrassResFun_eq_discFn (hm : 0 < m) (w : CParam s e) :
    weierstrassResFun m a w = (-1) ^ (m * (m - 1) / 2) * weierstrassDiscFn m a w := by
  rw [weierstrassResFun_apply]
  have hdeg : 0 < (weierstrassPoly m a w).degree := by
    rw [← natDegree_pos_iff_degree_pos, weierstrassPoly_natDegree m a w]; exact hm
  have hnd := weierstrassPoly_natDegree m a w
  have h := resultant_deriv hdeg
  rw [hnd, (weierstrassPoly_monic m a w).leadingCoeff, mul_one] at h
  rw [h, weierstrassDiscFn]

/-- The resultant function and the discriminant function share vanishing order (they differ by the
nonzero sign unit `(-1)^k`). This is the bridge connecting Phase D2's norm identity (which yields
`resultant`) to the Zariski axiom's hypothesis (stated via `discr`). -/
lemma order_weierstrassResFun_eq (hm : 0 < m) (p : CParam s e)
    (hdisc_an : AnalyticAt ℂ (weierstrassDiscFn m a) p) :
    order ℂ (weierstrassResFun m a) p = order ℂ (weierstrassDiscFn m a) p := by
  have hfun : weierstrassResFun m a
      = fun w => (-1 : ℂ) ^ (m * (m - 1) / 2) * weierstrassDiscFn m a w :=
    funext (weierstrassResFun_eq_discFn m a hm)
  rw [hfun]
  exact order_const_mul_analytic _ (pow_ne_zero _ (by norm_num)) _ p hdisc_an

end
