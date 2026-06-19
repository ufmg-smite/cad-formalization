import Cad.Multivariate.ProjectionTheorem.Generalized.CWeierstrassNewton
import Cad.Multivariate.ProjectionTheorem.Generalized.CDivisionByW
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Layer C, piece 5: the synthesis `G = u·W` (WIP)

The final step of Weierstrass preparation. From the Newton coefficients (`weierstrass_coeffs_exist`)
we have a monic Weierstrass polynomial `W(z,·)` whose roots are exactly the zeros of `G(z,·)` in the
disc. The **unit** `u = G/W` is recovered as a Cauchy contour integral

`u(z,t) = (2πi)⁻¹ ∮_{|ζ|=R} G(z,ζ) / (W(z,ζ)·(ζ − t)) dζ`,

which is jointly analytic in `(z,t)` (the keystone, via `qIntegrand_analyticAt`), satisfies
`u·W = G` near `0` (Cauchy reproducing, since `G/W` is holomorphic on the disc — `G` and `W` share
zeros), and is non-vanishing at `0` (because `G(0,·)` and `W(0,·) = t^m` both have order `m`).
Feeding `(u, a, …, G = u·W)` to `weierstrass_division_via_cauchy` discharges `weierstrass_division`.
-/

noncomputable section

open Complex Metric Filter Polynomial
open scoped Real Topology

variable {s e : ℕ}

/-- **Step 1: the candidate unit `u` is jointly analytic** at `0 ∈ CParam × ℂ`. The integrand is the
Cauchy quotient `G(z,ζ)/(W(z,ζ)(ζ−t))`, analytic on the contour (`W(0,ζ)=ζ^m ≠ 0`, `ζ−0 ≠ 0`);
`circleIntegral_analyticAt_fiber` (the keystone, parameter `(z,t)`) does the rest. -/
theorem u_analyticAt (G : CParam s e × ℂ → ℂ) (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0) {R : ℝ} (hR : 0 < R)
    (hGan_sph : ∀ ζ ∈ sphere (0 : ℂ) R, AnalyticAt ℂ G (0, ζ)) :
    AnalyticAt ℂ (fun p : CParam s e × ℂ => (2 * π * I)⁻¹ *
      ∮ ζ in C(0, R), G (p.1, ζ) / ((weierstrassPoly m a p.1).eval ζ * (ζ - p.2))) 0 := by
  refine analyticAt_const.mul ?_
  have : (0 : CParam s e × ℂ) = ((0 : CParam s e), (0 : ℂ)) := rfl
  rw [this]
  refine circleIntegral_analyticAt_fiber
    (fun x : (CParam s e × ℂ) × ℂ =>
      G (x.1.1, x.2) / ((weierstrassPoly m a x.1.1).eval x.2 * (x.2 - x.1.2))) hR fun ζ hζ => ?_
  have hζ0 : ζ ≠ 0 := by
    rw [mem_sphere_zero_iff_norm] at hζ
    intro h; rw [h, norm_zero] at hζ; exact absurd hζ.symm (ne_of_gt hR)
  exact qIntegrand_analyticAt m a ha_an ha0 G ζ hζ0 (hGan_sph ζ hζ)

/-- Product of `f` over a multiset built as `∑ a, n a • {a}`. -/
private lemma prod_nsmul_singleton (T : Finset ℂ) (n : ℂ → ℕ) (f : ℂ → ℂ) :
    ((∑ a ∈ T, n a • ({a} : Multiset ℂ)).map f).prod = ∏ a ∈ T, (f a) ^ (n a) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]
    simp [Multiset.map_nsmul, Multiset.prod_nsmul]

/-- The Weierstrass polynomial evaluates as the finite product over its root support, with the
divisor multiplicities. (Vieta form of `weierstrass_coeffs_exist`'s root-product identity.) -/
theorem weierstrassPoly_eval_eq_finsetProd (G : CParam s e × ℂ → ℂ) (m : ℕ)
    (a : Fin m → (CParam s e → ℂ)) {R₁ : ℝ} {z : CParam s e} (t : ℂ)
    (hW : weierstrassPoly m a z = ((rootMultiset G R₁ z).map (fun r => X - C r)).prod) :
    (weierstrassPoly m a z).eval t
      = ∏ a' ∈ (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset,
          (t - a') ^ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) a').toNat := by
  rw [hW, Polynomial.eval_multiset_prod, Multiset.map_map, rootMultiset, prod_nsmul_singleton]
  refine Finset.prod_congr rfl fun a' _ => ?_
  simp

/-- **Step 2: slice factorization `G(z,·) = W(z,·)·g`** with `g` analytic and **non-vanishing** on the
closed disc `|t| ≤ R`. Obtained from `MeromorphicOn.extract_zeros_poles` (the factorization of the
meromorphic `G(z,·)` into its divisor part times an analytic unit), identifying the divisor product
with `W` via `weierstrassPoly_eval_eq_finsetProd`. -/
theorem slice_factorization (G : CParam s e × ℂ → ℂ) (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    {R R₁ : ℝ} (hRR₁ : R < R₁) {z : CParam s e}
    (hAn : AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall (0 : ℂ) R₁))
    (hNe : ∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0)
    (hW : weierstrassPoly m a z = ((rootMultiset G R₁ z).map (fun r => X - C r)).prod) :
    ∃ g : ℂ → ℂ, (∀ t ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ g t) ∧
      (∀ t ∈ closedBall (0 : ℂ) R, g t ≠ 0) ∧
      (∀ t ∈ closedBall (0 : ℂ) R, G (z, t) = (weierstrassPoly m a z).eval t * g t) := by
  classical
  obtain ⟨z₀, hz₀mem, hz₀ne⟩ := hNe
  have hcbpre : IsPreconnected (closedBall (0 : ℂ) R₁) := (convex_closedBall 0 R₁).isPreconnected
  have horder : ∀ u : closedBall (0 : ℂ) R₁, meromorphicOrderAt (fun t => G (z, t)) u ≠ ⊤ := fun u =>
    meromorphicOrderAt_ne_top_of_analyticOnNhd hcbpre hAn hz₀mem hz₀ne u u.2
  obtain ⟨g, hg_an, hg_ne, hfact⟩ :=
    (AnalyticOnNhd.meromorphicOn hAn).extract_zeros_poles horder
      (divisor_support_finite (fun t => G (z, t)))
  have hdivnn : ∀ u, 0 ≤ MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
  set D := MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁) with hD
  set s := (divisor_support_finite (R₁ := R₁) (fun t => G (z, t))).toFinset with hs
  have hcbsub : closedBall (0 : ℂ) R ⊆ closedBall (0 : ℂ) R₁ := closedBall_subset_closedBall hRR₁.le
  -- the divisor product equals `W`
  have hfacteq : (∏ᶠ u, (· - u) ^ (D u)) • g
      = fun x => (weierstrassPoly m a z).eval x * g x := by
    funext x
    rw [Pi.smul_apply', smul_eq_mul,
      Function.FactorizedRational.finprod_eq_fun (divisor_support_finite (fun t => G (z, t)))]
    exact congrArg (· * g x)
      ((finprod_sub_zpow_eq_finset_prod (divisor_support_finite (fun t => G (z, t))) hdivnn x).trans
        (weierstrassPoly_eval_eq_finsetProd G m a x hW).symm)
  refine ⟨g, fun t ht => hg_an t (hcbsub ht), fun t ht => hg_ne ⟨t, hcbsub ht⟩, fun t ht => ?_⟩
  -- upgrade the codiscrete factorization to pointwise equality at `t`
  have htcb : t ∈ closedBall (0 : ℂ) R₁ := hcbsub ht
  have hcbmem : closedBall (0 : ℂ) R₁ ∈ 𝓝 t :=
    mem_of_superset (isOpen_ball.mem_nhds (by
      rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at ht; linarith)) ball_subset_closedBall
  have hGt : AnalyticAt ℂ (fun t => G (z, t)) t := hAn t htcb
  have hpoly : AnalyticAt ℂ (fun x => (weierstrassPoly m a z).eval x) t :=
    (Polynomial.differentiable (weierstrassPoly m a z)).differentiableOn.analyticAt Filter.univ_mem
  have hWgan : AnalyticAt ℂ (fun x => (weierstrassPoly m a z).eval x * g x) t :=
    hpoly.mul (hg_an t htcb)
  have hφgan : AnalyticAt ℂ ((∏ᶠ u, (· - u) ^ (D u)) • g) t := by rw [hfacteq]; exact hWgan
  have hbridge := eventuallyEq_nhds_of_codiscreteWithin hfact hcbmem hGt hφgan
  rw [hfacteq] at hbridge
  exact hbridge.eq_of_nhds

/-- **Step 3: Cauchy reproducing — `u(z,·) = g` and `u·W = G` on the slice.** Combining the
factorization `G = W·g` with the Cauchy integral formula for the analytic `g`: on the contour the
quotient integrand `G/(W·(ζ−t))` equals `g(ζ)/(ζ−t)`, whose contour integral reproduces `g(t)`. -/
theorem synthesis_slice (G : CParam s e × ℂ → ℂ) (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    {R R₁ : ℝ} (hR : 0 < R) (hRR₁ : R < R₁) {z : CParam s e}
    (hAn : AnalyticOnNhd ℂ (fun t => G (z, t)) (closedBall (0 : ℂ) R₁))
    (hNe : ∃ t ∈ closedBall (0 : ℂ) R₁, G (z, t) ≠ 0)
    (hSupp : ∀ a' ∈ (MeromorphicOn.divisor (fun t => G (z, t)) (closedBall (0 : ℂ) R₁)).support,
      a' ∈ ball (0 : ℂ) R)
    (hW : weierstrassPoly m a z = ((rootMultiset G R₁ z).map (fun r => X - C r)).prod) :
    ∃ g : ℂ → ℂ, (∀ t ∈ closedBall (0 : ℂ) R, g t ≠ 0) ∧
      (∀ t : ℂ, ‖t‖ < R → (2 * π * I)⁻¹ *
        ∮ ζ in C(0, R), G (z, ζ) / ((weierstrassPoly m a z).eval ζ * (ζ - t)) = g t) ∧
      (∀ t ∈ closedBall (0 : ℂ) R, G (z, t) = (weierstrassPoly m a z).eval t * g t) := by
  obtain ⟨g, hg_an, hg_ne, hGeq⟩ := slice_factorization G m a hRR₁ hAn hNe hW
  -- `W` is non-vanishing on the contour (its roots lie strictly inside)
  have hWsph : ∀ ζ ∈ sphere (0 : ℂ) R, (weierstrassPoly m a z).eval ζ ≠ 0 := by
    intro ζ hζ
    rw [weierstrassPoly_eval_eq_finsetProd G m a ζ hW, Finset.prod_ne_zero_iff]
    intro a' ha'
    refine pow_ne_zero _ ?_
    rw [sub_ne_zero]
    intro h
    have ha'mem : a' ∈ ball (0 : ℂ) R := hSupp a' ((Set.Finite.mem_toFinset _).mp ha')
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [mem_ball_zero_iff, ← h, hζ] at ha'mem
    exact lt_irrefl R ha'mem
  refine ⟨g, hg_ne, fun t ht => ?_, hGeq⟩
  have htball : t ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr ht
  have hcong : (∮ ζ in C(0, R), G (z, ζ) / ((weierstrassPoly m a z).eval ζ * (ζ - t)))
      = ∮ ζ in C(0, R), (ζ - t)⁻¹ • g ζ := by
    refine circleIntegral.integral_congr hR.le fun ζ hζ => ?_
    have hζcb : ζ ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hζ
    have hWζ : (weierstrassPoly m a z).eval ζ ≠ 0 := hWsph ζ hζ
    have hζt : ζ - t ≠ 0 := by
      rw [sub_ne_zero]; intro h
      rw [mem_sphere_zero_iff_norm] at hζ
      rw [← h] at ht; rw [hζ] at ht; exact (lt_irrefl R) ht
    rw [hGeq ζ hζcb, smul_eq_mul]
    field_simp
  rw [hcong]
  have hcauchy :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (E := ℂ) (s := ∅) Set.countable_empty htball
      (fun ζ hζ => (hg_an ζ hζ).continuousAt.continuousWithinAt)
      (fun ζ hζ => (hg_an ζ (ball_subset_closedBall hζ.1)).differentiableAt)
  rw [smul_eq_mul] at hcauchy
  exact hcauchy

/-- **Weierstrass preparation (synthesis): `G = u·W`.** Independent of the `weierstrass_division`
axiom: from `G` analytic at `0` and `t`-regular of order `m > 0`, there is an analytic **unit** `u`
(`u 0 ≠ 0`) and Weierstrass coefficients `a` (`a i 0 = 0`) with `G = u·W` near `0`. The unit is the
Cauchy quotient integral, analytic (`u_analyticAt`), reproducing `G/W` on each slice
(`synthesis_slice`), non-vanishing at `0` because `G(0,·)` and `W(0,·) = t^m` share the order `m`. -/
theorem weierstrass_preparation_synthesis (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hm_pos : 0 < m) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    ∃ (u : CParam s e × ℂ → ℂ) (a : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      G =ᶠ[𝓝 0] fun wt => u wt * (weierstrassPoly m a wt.1).eval wt.2 := by
  obtain ⟨a, R, R₁, hR, hRR₁, ha_an, ha0, hGan_sph, hG0_sph, hev⟩ :=
    weierstrass_coeffs_exist G hG m hm_pos hreg
  set u : CParam s e × ℂ → ℂ := fun p => (2 * π * I)⁻¹ *
    ∮ ζ in C(0, R), G (p.1, ζ) / ((weierstrassPoly m a p.1).eval ζ * (ζ - p.2)) with hu_def
  refine ⟨u, a, u_analyticAt G m a ha_an ha0 hR hGan_sph, ?_, ha_an, ha0, ?_⟩
  · -- `u 0 ≠ 0`: at the slice `z = 0`, `u 0 = g 0 ≠ 0`
    obtain ⟨hAn0, hNe0, hSupp0, hW0⟩ := hev.self_of_nhds
    obtain ⟨g, hg_ne, hg_eq, _⟩ := synthesis_slice G m a hR hRR₁ hAn0 hNe0 hSupp0 hW0
    have hval : u 0 = g 0 := hg_eq 0 (by rw [norm_zero]; exact hR)
    rw [hval]
    exact hg_ne 0 (by rw [mem_closedBall, dist_self]; exact hR.le)
  · -- `G =ᶠ[𝓝 0] u·W`
    have hev' := (continuous_fst.tendsto' (0 : CParam s e × ℂ) 0 rfl).eventually hev
    have ht' : ∀ᶠ p : CParam s e × ℂ in 𝓝 0, p.2 ∈ ball (0 : ℂ) R :=
      (continuous_snd.tendsto' (0 : CParam s e × ℂ) 0 rfl).eventually (Metric.ball_mem_nhds 0 hR)
    filter_upwards [hev', ht'] with p hp ht
    obtain ⟨hAn, hNe, hSupp, hW⟩ := hp
    obtain ⟨g, _, hg_eq, hGeq⟩ := synthesis_slice G m a hR hRR₁ hAn hNe hSupp hW
    have h1 : u p = g p.2 := hg_eq p.2 (mem_ball_zero_iff.mp ht)
    have h2 : G (p.1, p.2) = (weierstrassPoly m a p.1).eval p.2 * g p.2 :=
      hGeq p.2 (ball_subset_closedBall ht)
    show G p = u p * (weierstrassPoly m a p.1).eval p.2
    rw [h1, show G p = G (p.1, p.2) from rfl, h2]
    ring

/-- **`weierstrass_division`, discharged — no longer an axiom.** Convergent Weierstrass division by an
arbitrary `t`-regular germ `G`, proved (standard axioms only) by assembling Layer C's preparation
`G = u·W` (`weierstrass_preparation_synthesis`) with the already-proved Layer A∘B division-by-`W`
(`weierstrass_division_via_cauchy`) and the unconditional keystone (`circleIntegral_analyticAt_fiber`).
The `m = 0` case is the trivial one where `G` is a unit (`W = 1`). The statement is identical to the
former `weierstrass_division` axiom. -/
theorem weierstrass_division_proved (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    (∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) ∧
    (∀ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0) := by
  have hkey : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
      (Φ : H × ℂ → ℂ) {r : ℝ} {p₀ : H}, 0 < r →
      (∀ ζ ∈ sphere (0 : ℂ) r, AnalyticAt ℂ Φ (p₀, ζ)) →
      AnalyticAt ℂ (fun p : H => ∮ ζ in C(0, r), Φ (p, ζ)) p₀ := by
    intro H _ _ _ Φ r p₀ hr hΦ
    exact circleIntegral_analyticAt_fiber Φ hr hΦ
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- `m = 0`: `G` is a unit (order `0` ⟹ `G 0 ≠ 0`), `W = 1`, `u = G`
    subst hm0
    have hG0 : G 0 ≠ 0 := by
      have hsl : AnalyticAt ℂ (fun t => G (0, t)) 0 :=
        hG.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
      exact hsl.analyticOrderAt_eq_zero.mp (by simpa using hreg)
    refine weierstrass_division_via_cauchy G 0 G Fin.elim0 hG hG0 (fun i => i.elim0)
      (fun i => i.elim0) ?_ hkey
    filter_upwards with wt
    show G wt = G wt * (weierstrassPoly 0 Fin.elim0 wt.1).eval wt.2
    simp [weierstrassPoly]
  · obtain ⟨u, a, hu, hu0, ha_an, ha0, hGW⟩ :=
      weierstrass_preparation_synthesis G hG m hm_pos hreg
    exact weierstrass_division_via_cauchy G m u a hu hu0 ha_an ha0 hGW hkey

end

