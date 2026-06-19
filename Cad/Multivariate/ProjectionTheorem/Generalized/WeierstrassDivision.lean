import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassEval

/-!
# Phase D1 descent — the polynomial↔germ bridge and division uniqueness

The norm identity lives in the **polynomial ring** `(CParam s e → ℂ)[X]` (where `weierstrassPolyFun`
sits), but the Weierstrass factorization `g = u·h` and the division theorem live among **germs of
`(z,t)`-functions** `CParam s e × ℂ → ℂ`. This file provides the ring-hom bridge between the two,

`polyToFun : (CParam s e → ℂ)[X] →+* (CParam s e × ℂ → ℂ)`,  `X ↦ t`,  `C c ↦ (z,t) ↦ c z`,

so that polynomial-ring statements transport to germ statements and back. It also upgrades the
zero-germ division-uniqueness axiom to the standard two-divisions form.

These are the load-bearing translation pieces for the D1 descent (germ-ring `⟨h,h'⟩` membership ⟹
polynomial-ring `⟨h,h'⟩` membership, via Weierstrass division).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- The ring hom embedding a function `c : CParam s e → ℂ` as the `t`-independent germ
`(z,t) ↦ c z`. -/
def constFunHom (s e : ℕ) : (CParam s e → ℂ) →+* (CParam s e × ℂ → ℂ) where
  toFun c := fun zt => c zt.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The evaluation bridge `(CParam s e → ℂ)[X] →+* (CParam s e × ℂ → ℂ)`: send `X` to the
distinguished coordinate `t` and a constant coefficient `c` to the `t`-independent germ `(z,t) ↦ c z`.
A polynomial `p(X)` with function coefficients maps to `(z,t) ↦ ∑ₖ (p.coeff k z)·tᵏ`. -/
def polyToFun (s e : ℕ) : (CParam s e → ℂ)[X] →+* (CParam s e × ℂ → ℂ) :=
  eval₂RingHom (constFunHom s e) (fun zt => zt.2)

/-- Pointwise description: `polyToFun p` evaluated at `(z,t)` is the ordinary evaluation at `t` of
the `ℂ`-polynomial obtained by evaluating each coefficient at `z`. -/
lemma polyToFun_apply (p : (CParam s e → ℂ)[X]) (zt : CParam s e × ℂ) :
    polyToFun s e p zt = (p.map (Pi.evalRingHom (fun _ => ℂ) zt.1)).eval zt.2 := by
  have hext : (Pi.evalRingHom (fun _ : CParam s e × ℂ => ℂ) zt).comp (polyToFun s e)
      = eval₂RingHom (Pi.evalRingHom (fun _ : CParam s e => ℂ) zt.1) zt.2 := by
    apply Polynomial.ringHom_ext
    · intro c; simp [polyToFun, constFunHom]
    · simp [polyToFun]
  have h := RingHom.congr_fun hext p
  rw [Polynomial.eval_map]
  simpa [polyToFun] using h

/-- `polyToFun` sends the function-coefficient Weierstrass polynomial to the pointwise Weierstrass
polynomial-as-a-germ. -/
lemma polyToFun_weierstrassPolyFun (m : ℕ) (a : Fin m → (CParam s e → ℂ)) :
    polyToFun s e (weierstrassPolyFun m a)
      = fun zt => (weierstrassPoly m a zt.1).eval zt.2 := by
  funext zt
  rw [polyToFun_apply, weierstrassPolyFun_map_eval]

/-- For a polynomial of `t`-degree `< m`, `polyToFun` is the explicit degree-`<m` sum — matching the
remainder shape `∑_{i<m} ρᵢ(z) tⁱ` of the Weierstrass division axiom. -/
lemma polyToFun_eq_finSum_of_natDegree_lt {m : ℕ} (R0 : (CParam s e → ℂ)[X])
    (hdeg : R0.natDegree < m) (wt : CParam s e × ℂ) :
    polyToFun s e R0 wt = ∑ i : Fin m, R0.coeff i wt.1 * wt.2 ^ (i : ℕ) := by
  rw [polyToFun_apply]
  have hnd : (R0.map (Pi.evalRingHom (fun _ => ℂ) wt.1)).natDegree < m :=
    lt_of_le_of_lt natDegree_map_le hdeg
  rw [Polynomial.eval_eq_sum_range' hnd wt.2,
    ← Fin.sum_univ_eq_sum_range
      (fun i => (R0.map (Pi.evalRingHom (fun _ => ℂ) wt.1)).coeff i * wt.2 ^ i) m]
  exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.coeff_map]; rfl)

/-- **Germ-injectivity of `polyToFun`.** If `polyToFun p` vanishes near `0`, then every coefficient
of `p` vanishes near `0`. (For each fixed `z` near `0`, `t ↦ polyToFun p (z,t)` is a `ℂ`-polynomial
vanishing on a neighborhood of `0`, hence identically zero.) This lets germ identities be transported
back to coefficient-wise identities — the descent's return trip from germs to `𝒪ₙ[t]`. -/
lemma polyToFun_coeff_eventuallyEq_zero (p : (CParam s e → ℂ)[X])
    (hp : polyToFun s e p =ᶠ[𝓝 0] 0) (k : ℕ) :
    p.coeff k =ᶠ[𝓝 (0 : CParam s e)] 0 := by
  have hp2 : ∀ᶠ x in 𝓝 ((0 : CParam s e), (0 : ℂ)), polyToFun s e p x = 0 := by
    filter_upwards [hp] with x hx; simpa using hx
  rw [nhds_prod_eq] at hp2
  obtain ⟨Pz, hPz, Pt, hPt, H⟩ := Filter.eventually_prod_iff.mp hp2
  filter_upwards [hPz] with z hz
  have hsub : {t | Pt t} ⊆ {t | (p.map (Pi.evalRingHom (fun _ => ℂ) z)).IsRoot t} := by
    intro t ht
    have happ : polyToFun s e p (z, t)
        = (p.map (Pi.evalRingHom (fun _ => ℂ) z)).eval t := polyToFun_apply p (z, t)
    show (p.map (Pi.evalRingHom (fun _ => ℂ) z)).IsRoot t
    rw [Polynomial.IsRoot, ← happ]
    exact H hz ht
  have hpz0 : p.map (Pi.evalRingHom (fun _ => ℂ) z) = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ ((infinite_of_mem_nhds (0 : ℂ) hPt).mono hsub)
  have hck : (p.map (Pi.evalRingHom (fun _ => ℂ) z)).coeff k = 0 := by rw [hpz0]; simp
  rw [Polynomial.coeff_map] at hck
  simpa using hck

/-- **Core descent step.** If an analytic germ `k` satisfies `k · h =ᶠ polyToFun P₀` for a monic
Weierstrass `h` and a polynomial `P₀`, then `k` is germ-equal to the **polynomial** germ
`polyToFun (P₀ /ₘ h)`. (Polynomial-divide `P₀ = h·Q₀ + R₀`; then `(k − polyToFun Q₀)·h =ᶠ polyToFun R₀`
is a division of `0`, and uniqueness forces `k =ᶠ polyToFun Q₀`.) The analyticity of the quotient germ
and the remainder coefficients — i.e. that `/ₘ`,`%ₘ` by the analytic monic `h` preserve analyticity
— are taken as hypotheses; they are the precise remaining obligation (provable via `map_divByMonic`
over the analytic-germ ring on `CParam`). -/
lemma analytic_mul_weierstrass_eq_poly {m : ℕ} (hm : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (k : CParam s e × ℂ → ℂ) (hk : AnalyticAt ℂ k 0)
    (P0 : (CParam s e → ℂ)[X])
    (hQ_an : AnalyticAt ℂ (polyToFun s e (P0 /ₘ weierstrassPolyFun m a)) 0)
    (hR_an : ∀ i, AnalyticAt ℂ ((P0 %ₘ weierstrassPolyFun m a).coeff i) 0)
    (heq : (fun zt => k zt * polyToFun s e (weierstrassPolyFun m a) zt) =ᶠ[𝓝 0] polyToFun s e P0) :
    k =ᶠ[𝓝 0] polyToFun s e (P0 /ₘ weierstrassPolyFun m a) := by
  have hmonic : (weierstrassPolyFun m a).Monic := weierstrassPolyFun_monic m a
  set h := weierstrassPolyFun m a with hh_def
  set Q0 := P0 /ₘ h with hQ0_def
  set R0 := P0 %ₘ h with hR0_def
  have hPdiv : P0 = R0 + h * Q0 := (modByMonic_add_div P0 hmonic).symm
  have hRdeg : R0.natDegree < m := by
    rcases eq_or_ne R0 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact hm
    · have hd : R0.degree < (m : WithBot ℕ) := by
        have hlt := degree_modByMonic_lt P0 hmonic
        rw [← hR0_def] at hlt
        rwa [show h.degree = (m : WithBot ℕ) from weierstrassPolyFun_degree m a] at hlt
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hd
  -- The combination `(k − polyToFun Q₀)·h + ∑ (−R₀.coeffᵢ) tⁱ =ᶠ 0` is a division of zero.
  have key : (fun wt => (fun zt => k zt - polyToFun s e Q0 zt) wt
        * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, (fun w => -(R0.coeff i w)) wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 := by
    filter_upwards [heq] with wt hwt
    have hH : (weierstrassPoly m a wt.1).eval wt.2 = polyToFun s e h wt := by
      rw [hh_def, polyToFun_weierstrassPolyFun]
    have hsum : (∑ i : Fin m, -(R0.coeff i wt.1) * wt.2 ^ (i : ℕ)) = - polyToFun s e R0 wt := by
      rw [polyToFun_eq_finSum_of_natDegree_lt R0 hRdeg wt, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hP0 : polyToFun s e P0 wt
        = polyToFun s e R0 wt + polyToFun s e h wt * polyToFun s e Q0 wt := by
      have : polyToFun s e P0 = polyToFun s e R0 + polyToFun s e h * polyToFun s e Q0 := by
        rw [hPdiv, map_add, map_mul]
      exact congrFun this wt
    have hkH : k wt * polyToFun s e h wt
        = polyToFun s e R0 wt + polyToFun s e h wt * polyToFun s e Q0 wt := by
      rw [← hP0]; exact hwt
    simp only [Pi.zero_apply]
    rw [hsum, hH]
    linear_combination hkH
  obtain ⟨hq0, -⟩ := weierstrass_division_unique m a ha_an ha0
    (fun zt => k zt - polyToFun s e Q0 zt) (fun i => fun w => -(R0.coeff i w))
    (hk.sub hQ_an) (fun i => (hR_an i).neg) key
  filter_upwards [hq0] with zt h
  simpa [sub_eq_zero] using h


/-! ## Discharging the divByMonic-analyticity obligations (Step 1) -/

/-- The functions on `CParam s e` that are **analytic at `0`** form a subring (closed under `+,*,−`
and the constants), since `AnalyticAt` is). -/
def AnalyticAtSubring (s e : ℕ) : Subring (CParam s e → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' hf hg := hf.mul hg
  one_mem' := analyticAt_const
  add_mem' hf hg := hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' hf := hf.neg


/-- **divByMonic preserves analytic coefficients.** Dividing by a monic polynomial whose coefficients
are analytic keeps the quotient/remainder coefficients analytic — because division by a monic uses
only ring operations, so it stays inside the analytic-at-`0` subring (`map_divByMonic` over it). -/
lemma coeff_divByMonic_analyticAt (P0 h : (CParam s e → ℂ)[X])
    (hP : ∀ i, AnalyticAt ℂ (P0.coeff i) 0) (hh : ∀ i, AnalyticAt ℂ (h.coeff i) 0)
    (hmonic : h.Monic) (i : ℕ) :
    AnalyticAt ℂ ((P0 /ₘ h).coeff i) 0 ∧ AnalyticAt ℂ ((P0 %ₘ h).coeff i) 0 := by
  set S := AnalyticAtSubring s e with hS
  have hPsub : (↑P0.coeffs : Set (CParam s e → ℂ)) ⊆ ↑S := by
    intro x hx; obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx; exact hP n
  have hhsub : (↑h.coeffs : Set (CParam s e → ℂ)) ⊆ ↑S := by
    intro x hx; obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx; exact hh n
  set P0' := P0.toSubring S hPsub with hP0'
  set h' := h.toSubring S hhsub with hh'
  have hmap_h : h'.map S.subtype = h := map_toSubring h S hhsub
  have hmap_P : P0'.map S.subtype = P0 := map_toSubring P0 S hPsub
  have hh'_monic : h'.Monic := by
    have hinj : Function.Injective (S.subtype) := Subtype.coe_injective
    have hmm : (h'.map S.subtype).Monic := by rw [hmap_h]; exact hmonic
    exact hinj.monic_map_iff.mpr hmm
  have hmapdiv : (P0' /ₘ h').map S.subtype = P0 /ₘ h := by
    rw [Polynomial.map_divByMonic _ hh'_monic, hmap_P, hmap_h]
  have hmapmod : (P0' %ₘ h').map S.subtype = P0 %ₘ h := by
    rw [Polynomial.map_modByMonic _ hh'_monic, hmap_P, hmap_h]
  constructor
  · have hc : (P0 /ₘ h).coeff i = ↑((P0' /ₘ h').coeff i) := by
      rw [← hmapdiv, Polynomial.coeff_map]; rfl
    rw [hc]; exact ((P0' /ₘ h').coeff i).2
  · have hc : (P0 %ₘ h).coeff i = ↑((P0' %ₘ h').coeff i) := by
      rw [← hmapmod, Polynomial.coeff_map]; rfl
    rw [hc]; exact ((P0' %ₘ h').coeff i).2

/-- `polyToFun` of a polynomial with analytic coefficients is analytic at `0`
(a finite sum of `(coeffᵢ ∘ fst) · sndⁱ`). -/
lemma polyToFun_analyticAt (Q : (CParam s e → ℂ)[X])
    (hQ : ∀ i, AnalyticAt ℂ (Q.coeff i) 0) :
    AnalyticAt ℂ (polyToFun s e Q) 0 := by
  have heq : polyToFun s e Q
      = fun zt => ∑ i : Fin (Q.natDegree + 1), Q.coeff i zt.1 * zt.2 ^ (i : ℕ) := by
    funext zt; exact polyToFun_eq_finSum_of_natDegree_lt Q (Nat.lt_succ_self _) zt
  rw [heq]
  apply Finset.analyticAt_fun_sum
  intro i _
  have hfst : AnalyticAt ℂ (fun zt : CParam s e × ℂ => zt.1) 0 :=
    (ContinuousLinearMap.fst ℂ (CParam s e) ℂ).analyticAt (0 : CParam s e × ℂ)
  have hsnd : AnalyticAt ℂ (fun zt : CParam s e × ℂ => zt.2) 0 :=
    (ContinuousLinearMap.snd ℂ (CParam s e) ℂ).analyticAt (0 : CParam s e × ℂ)
  exact ((hQ i).comp_of_eq hfst rfl).mul (hsnd.pow (i : ℕ))

/-- The coefficients of the function-coefficient Weierstrass polynomial are analytic at `0`. -/
lemma weierstrassPolyFun_coeff_analyticAt {m : ℕ} (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (k : ℕ) :
    AnalyticAt ℂ ((weierstrassPolyFun m a).coeff k) 0 := by
  set S := AnalyticAtSubring s e
  let hSpoly : S[X] := X ^ m + ∑ i : Fin m, C (⟨a i, ha_an i⟩ : S) * X ^ (i : ℕ)
  have hmap : hSpoly.map S.subtype = weierstrassPolyFun m a := by
    simp only [hSpoly, weierstrassPolyFun, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hc : (weierstrassPolyFun m a).coeff k = ↑(hSpoly.coeff k) := by
    rw [← hmap, Polynomial.coeff_map]; rfl
  rw [hc]; exact (hSpoly.coeff k).2

/-- **Core descent step, fully discharged.** Same as `analytic_mul_weierstrass_eq_poly`, but the
divByMonic-analyticity hypotheses are *derived* from `P0` having analytic coefficients (Step 1). -/
lemma analytic_mul_weierstrass_eq_poly_of_coeffs {m : ℕ} (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (k : CParam s e × ℂ → ℂ) (hk : AnalyticAt ℂ k 0)
    (P0 : (CParam s e → ℂ)[X]) (hP0 : ∀ i, AnalyticAt ℂ (P0.coeff i) 0)
    (heq : (fun zt => k zt * polyToFun s e (weierstrassPolyFun m a) zt) =ᶠ[𝓝 0] polyToFun s e P0) :
    k =ᶠ[𝓝 0] polyToFun s e (P0 /ₘ weierstrassPolyFun m a) := by
  have hh_an := weierstrassPolyFun_coeff_analyticAt a ha_an
  have hmonic := weierstrassPolyFun_monic m a
  refine analytic_mul_weierstrass_eq_poly hm a ha_an ha0 k hk P0 ?_ ?_ heq
  · exact polyToFun_analyticAt _
      (fun i => (coeff_divByMonic_analyticAt P0 _ hP0 hh_an hmonic i).1)
  · exact fun i => (coeff_divByMonic_analyticAt P0 _ hP0 hh_an hmonic i).2

end
