import Cad.Multivariate.ProjectionTheorem.Generalized.Monodromy
import Cad.Multivariate.ProjectionTheorem.Puiseux.Covering
import Cad.Multivariate.ProjectionTheorem.Puiseux.RootCover
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Lemma 4.2.6 (Newton–Puiseux parametrization) — the `s = 0` (classical) case

For an irreducible univariate Weierstrass family `q` of degree `m` (the codimension-one, no-section
case), the roots of `q` over the punctured transverse disc are parametrized by `w = uᵐ`, `t = φ(u)`
for a single holomorphic `φ`. The construction (the convergent/covering route, C1–C4 of the
Newton–Puiseux sub-project):

* **universal cover**: the punctured disc `Δ* = {0 < |w| < e^c}` has the half-plane `H = {Re τ < c}`
  as universal cover via `w = exp τ`; `H` is convex, hence contractible and simply connected;
* **lift**: pulling the root cover back along `exp : H → Δ*` (a map from a simply-connected space)
  yields, by `IsCoveringMap.existsUnique_continuousMap_lifts`, a continuous — then analytic — root
  section `ρ : H → ℂ`, `(q (exp τ)).eval (ρ τ) = 0`;
* **period**: the connected `m`-sheeted cover has single-`m`-cycle monodromy, so `ρ(τ + 2πi·m) = ρ τ`;
* **descent**: `φ(u) := ρ (m · log u)` is single-valued (the period), `w = uᵐ`, analytic, and bounded,
  hence extends across `u = 0` (removable singularity).

This file is **work in progress** (not yet wired into the main build). It begins with the
universal-cover domain and the analytic root lift — the validation that the C1 ↔ `rootCover` ↔ C4.3
interfaces compose.
-/

noncomputable section

open Filter Topology Complex Polynomial
open scoped Real

namespace Puiseux

/-! ### Lift uniqueness and periodicity (the covering-theoretic core of the period) -/

section Lift

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
  [SimplyConnectedSpace A] [LocPathConnectedSpace A] {p : E → X}

/-- **Lift uniqueness.** Two continuous lifts of the same map over a simply-connected (and
locally-path-connected) domain that agree at one point are equal. -/
theorem lift_unique (cov : IsCoveringMap p) {F G : C(A, E)}
    (hFG : (p ∘ F : A → X) = (p ∘ G : A → X)) (a₀ : A) (h : F a₀ = G a₀) : F = G := by
  have hcont : Continuous (p ∘ (G : A → E)) := cov.continuous.comp G.continuous
  obtain ⟨_, _, huniq⟩ :=
    cov.existsUnique_continuousMap_lifts ⟨p ∘ (G : A → E), hcont⟩ a₀ (G a₀) rfl
  rw [huniq F ⟨h, hFG⟩, huniq G ⟨rfl, rfl⟩]

/-- **Periodicity propagation.** If `F` lifts `f`, the shift `s` preserves `f` (`f ∘ s = f`), and the
lift is fixed by `s` at one point, then it is fixed everywhere: `F (s a) = F a` for all `a`. -/
theorem lift_periodic (cov : IsCoveringMap p) {F : C(A, E)} {f : C(A, X)}
    (hF : (p ∘ F : A → X) = f) (s : C(A, A)) (hs : (f ∘ s : A → X) = f)
    (a₀ : A) (h0 : F (s a₀) = F a₀) : ∀ a, F (s a) = F a := by
  have key : F.comp s = F := by
    refine lift_unique cov ?_ a₀ h0
    funext a
    show p (F (s a)) = p (F a)
    calc p (F (s a)) = f (s a) := congrFun hF (s a)
      _ = f a := congrFun hs a
      _ = p (F a) := (congrFun hF a).symm
  intro a
  exact DFunLike.congr_fun key a

end Lift

/-- The open left half-plane `{τ : Re τ < c}` — the universal cover of the punctured disc of radius
`e^c` via `w = exp τ`. -/
def halfPlane (c : ℝ) : Set ℂ := {τ : ℂ | τ.re < c}

lemma isOpen_halfPlane (c : ℝ) : IsOpen (halfPlane c) :=
  isOpen_lt (by fun_prop) continuous_const

lemma convex_halfPlane (c : ℝ) : Convex ℝ (halfPlane c) := by
  refine fun x hx y hy s t hs ht hst => ?_
  simp only [halfPlane, Set.mem_setOf_eq] at hx hy ⊢
  have hre : (s • x + t • y).re = s * x.re + t * y.re := by
    simp [Complex.add_re, Complex.real_smul]
  rw [hre]
  rcases lt_or_eq_of_le hs with hs0 | hs0
  · have h1 : s * x.re < s * c := by nlinarith
    have h2 : t * y.re ≤ t * c := by nlinarith
    have hsum : s * x.re + t * y.re < s * c + t * c := by linarith
    rwa [← add_mul, hst, one_mul] at hsum
  · have ht1 : t = 1 := by rw [← hs0] at hst; linarith
    rw [← hs0, ht1, zero_mul, one_mul, zero_add]; exact hy

/-- `k · 2πi` is purely imaginary. -/
lemma intMul_two_pi_I_re (k : ℤ) : ((k : ℂ) * (2 * (π : ℂ) * Complex.I)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

lemma natMul_two_pi_I_re (m : ℕ) : ((m : ℂ) * (2 * (π : ℂ) * Complex.I)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- **A continuous root of an analytic separable family is analytic.** If `ρ` is a continuous root
section `(q (g τ)).eval (ρ τ) = 0` of a monic analytic family with `g` analytic and `q (g τ₁)`
separable, then `ρ` is analytic at `τ₁` (it locally coincides with one of the analytic root sections,
by continuity + the separation of distinct roots). -/
theorem analyticAt_continuous_root {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {g : W → Fin n → ℂ} {ρ : W → ℂ} {τ₁ : W}
    (hg : AnalyticAt ℂ g τ₁)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (g τ₁))
    (hsep : (q (g τ₁)).Separable)
    (hρc : ContinuousAt ρ τ₁)
    (hρr : ∀ᶠ τ in 𝓝 τ₁, (q (g τ)).eval (ρ τ) = 0) :
    AnalyticAt ℂ ρ τ₁ := by
  classical
  obtain ⟨V, φ, hVopen, hgτ₁V, _, _, hφan, hφinj, hφroots⟩ :=
    exists_local_root_sections q hmonic hdeg hcoeff hsep Set.univ isOpen_univ (Set.mem_univ _)
  have hgcont : ContinuousAt g τ₁ := hg.continuousAt
  have hgV : ∀ᶠ τ in 𝓝 τ₁, g τ ∈ V := hgcont (hVopen.mem_nhds hgτ₁V)
  have hφcat : ∀ i, ContinuousAt (fun τ => φ i (g τ)) τ₁ := fun i =>
    (((hφan i).analyticAt (hVopen.mem_nhds hgτ₁V)).continuousAt).comp hgcont
  -- `ρ τ₁` is a root, so `= φ i₀ (g τ₁)` for some `i₀`
  have hρ₁_root : (q (g τ₁)).eval (ρ τ₁) = 0 := hρr.self_of_nhds
  have hρ₁_mem : ρ τ₁ ∈ (q (g τ₁)).roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots').mpr ⟨(hmonic (g τ₁)).ne_zero, hρ₁_root⟩
  rw [hφroots (g τ₁) hgτ₁V, Finset.mem_image] at hρ₁_mem
  obtain ⟨i₀, _, hi₀⟩ := hρ₁_mem
  -- near `τ₁`, `ρ` coincides with `φ i₀ ∘ g`
  have hsep_ev : ∀ᶠ τ in 𝓝 τ₁, ρ τ = φ i₀ (g τ) := by
    have hclose : ∀ᶠ τ in 𝓝 τ₁,
        ∀ i, i ≠ i₀ → ‖ρ τ - φ i₀ (g τ)‖ < ‖φ i (g τ) - φ i₀ (g τ)‖ := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_imp_distrib_left]
      intro hi
      have hlhs : Tendsto (fun τ => ‖ρ τ - φ i₀ (g τ)‖) (𝓝 τ₁) (𝓝 0) := by
        have hd : Tendsto (fun τ => ρ τ - φ i₀ (g τ)) (𝓝 τ₁) (𝓝 (ρ τ₁ - φ i₀ (g τ₁))) :=
          hρc.sub (hφcat i₀)
        rw [hi₀, sub_self] at hd
        simpa using (continuous_norm.tendsto (0 : ℂ)).comp hd
      have hrhs : Tendsto (fun τ => ‖φ i (g τ) - φ i₀ (g τ)‖) (𝓝 τ₁)
          (𝓝 ‖φ i (g τ₁) - φ i₀ (g τ₁)‖) :=
        (continuous_norm.continuousAt).comp ((hφcat i).sub (hφcat i₀))
      have hpos : 0 < ‖φ i (g τ₁) - φ i₀ (g τ₁)‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact fun h => hi (hφinj (g τ₁) hgτ₁V h)
      exact hlhs.eventually_lt hrhs hpos
    filter_upwards [hclose, hgV, hρr] with τ hτ hτV hτroot
    -- `ρ τ` is a root, = `φ j (g τ)` for some `j`; `hτ` forces `j = i₀`
    have hmem : ρ τ ∈ (q (g τ)).roots.toFinset := by
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots').mpr ⟨(hmonic (g τ)).ne_zero, hτroot⟩
    rw [hφroots (g τ) hτV, Finset.mem_image] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    by_cases hji : j = i₀
    · rw [← hj, hji]
    · exfalso
      have hcontra := hτ j hji
      rw [← hj] at hcontra
      exact lt_irrefl _ hcontra
  have hsep_ev' : ρ =ᶠ[𝓝 τ₁] fun τ => φ i₀ (g τ) := hsep_ev
  exact (((hφan i₀).analyticAt (hVopen.mem_nhds hgτ₁V)).comp hg).congr hsep_ev'.symm

/-- A local analytic branch of `log` near any `u₀ ≠ 0` (principal `log` on the slit plane, a rotated
branch on the negative axis). -/
lemma exists_local_log_branch {u₀ : ℂ} (hu₀ : u₀ ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L u₀ ∧ (∀ᶠ u in 𝓝 u₀, Complex.exp (L u) = u) := by
  by_cases hs : u₀ ∈ Complex.slitPlane
  · exact ⟨Complex.log, analyticAt_clog hs,
      by filter_upwards [isOpen_ne.mem_nhds hu₀] with u hu using Complex.exp_log hu⟩
  · have hu₀re : u₀.re < 0 := by
      rw [Complex.mem_slitPlane_iff, not_or, not_lt] at hs
      rcases hs.1.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (h.trans Complex.zero_re.symm)
          ((not_not.mp hs.2).trans Complex.zero_im.symm)) hu₀
    have hneg : -u₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; exact Or.inl (by rw [Complex.neg_re]; linarith)
    refine ⟨fun u => Complex.log (-u) + ↑π * Complex.I,
      ((analyticAt_clog hneg).comp analyticAt_id.neg).add analyticAt_const, ?_⟩
    filter_upwards [isOpen_ne.mem_nhds hu₀] with u hu
    show Complex.exp (Complex.log (-u) + ↑π * Complex.I) = u
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hu), Complex.exp_pi_mul_I]
    ring

/-- The fibre of the root cover over a base point `b = rootProj e₀` is in bijection with the roots of
`q b` (each root `t` gives the variety point `(b, t)`, and conversely). -/
def rootCover_fiberEquiv {N : ℕ} (q : (Fin N → ℂ) → Polynomial ℂ)
    {U : Set (Fin N → ℂ)} (e₀ : ↥(rootProj q ⁻¹' U)) (hq : q (e₀.val.val.1) ≠ 0) :
    {e // U.restrictPreimage (rootProj q) e = U.restrictPreimage (rootProj q) e₀}
      ≃ ↥((q (e₀.val.val.1)).roots.toFinset) where
  toFun e := ⟨e.val.val.val.2, by
    rw [Multiset.mem_toFinset]
    have hbase : e.val.val.val.1 = e₀.val.val.1 :=
      congrArg Subtype.val e.property
    have hr : (q e.val.val.val.1).eval e.val.val.val.2 = 0 := e.val.val.property
    rw [hbase] at hr
    exact (Polynomial.mem_roots').mpr ⟨hq, hr⟩⟩
  invFun t := ⟨⟨⟨(e₀.val.val.1, t.val),
      (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp t.property)).2⟩, e₀.property⟩,
    Subtype.ext rfl⟩
  left_inv e := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    have hbase : e.val.val.val.1 = e₀.val.val.1 := congrArg Subtype.val e.property
    show (e₀.val.val.1, e.val.val.val.2) = e.val.val.val
    rw [← hbase]
  right_inv t := by apply Subtype.ext; rfl

/-- **Root bound (Lagrange, `Fin n → ℂ` base).** For a monic family with `q 0 = Xᵐ` (so the lower
coefficients vanish at `0`), all roots of `q y` lie within `‖·‖ ≤ R` for `y` near `0`. Discharges the
`hbdd` hypothesis. -/
theorem roots_eventually_bounded {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (m : ℕ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i)) (hq0 : q 0 = X ^ m)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ R := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := min 1 (R ^ m) / (m + 1) with hδdef
  have hmin_pos : 0 < min 1 (R ^ m) := lt_min one_pos (by positivity)
  have hδpos : 0 < δ := div_pos hmin_pos (by positivity)
  have hδm_lt : δ * (m : ℝ) < min 1 (R ^ m) := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left (by linarith) hmin_pos
  have hδm1 : δ * (m : ℝ) < 1 := lt_of_lt_of_le hδm_lt (min_le_left _ _)
  have hδmR : δ * (m : ℝ) < R ^ m := lt_of_lt_of_le hδm_lt (min_le_right _ _)
  have ha0 : ∀ i, i < m → (q 0).coeff i = 0 := fun i hi => by
    rw [hq0, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi)]
  have hev : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ i ∈ Finset.range m, ‖(q y).coeff i‖ ≤ δ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    refine (((hcoeff i).continuousAt.norm).eventually_lt continuousAt_const ?_).mono fun y h => h.le
    rw [ha0 i (Finset.mem_range.mp hi)]; simpa using hδpos
  filter_upwards [hev] with y hy t ht
  have htroot : (q y).eval t = 0 :=
    (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp ht)).2
  have h0 : t ^ m = -∑ i ∈ Finset.range m, (q y).coeff i * t ^ i := by
    have hevr : (q y).eval t = ∑ i ∈ Finset.range (m + 1), (q y).coeff i * t ^ i := by
      rw [Polynomial.eval_eq_sum_range, hdeg y]
    rw [Finset.sum_range_succ,
      show (q y).coeff m = 1 from by rw [← hdeg y]; exact (hmonic y).coeff_natDegree, one_mul,
      htroot] at hevr
    linear_combination -hevr
  have hnorm : ‖t‖ ^ m ≤ δ * ∑ i ∈ Finset.range m, ‖t‖ ^ i := by
    have he : ‖t‖ ^ m = ‖∑ i ∈ Finset.range m, (q y).coeff i * t ^ i‖ := by
      rw [← norm_pow, h0, norm_neg]
    rw [he]
    calc ‖∑ i ∈ Finset.range m, (q y).coeff i * t ^ i‖
        ≤ ∑ i ∈ Finset.range m, ‖(q y).coeff i * t ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range m, ‖(q y).coeff i‖ * ‖t‖ ^ i := by simp only [norm_mul, norm_pow]
      _ ≤ ∑ i ∈ Finset.range m, δ * ‖t‖ ^ i :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hy i hi) (by positivity)
      _ = δ * ∑ i ∈ Finset.range m, ‖t‖ ^ i := by rw [Finset.mul_sum]
  rcases le_total 1 ‖t‖ with hr1 | hr1
  · exfalso
    have hsum_le : ∑ i ∈ Finset.range m, ‖t‖ ^ i ≤ (m : ℝ) * ‖t‖ ^ (m - 1) := by
      calc ∑ i ∈ Finset.range m, ‖t‖ ^ i
          ≤ ∑ _i ∈ Finset.range m, ‖t‖ ^ (m - 1) :=
            Finset.sum_le_sum fun i hi =>
              pow_le_pow_right₀ hr1 (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
        _ = (m : ℝ) * ‖t‖ ^ (m - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpow_pos : 0 < ‖t‖ ^ (m - 1) := pow_pos (lt_of_lt_of_le one_pos hr1) _
    have hrm_eq : ‖t‖ ^ m = ‖t‖ * ‖t‖ ^ (m - 1) := by
      rw [mul_comm ‖t‖ (‖t‖ ^ (m - 1)), ← pow_succ, Nat.sub_add_cancel hm]
    have hrm : ‖t‖ * ‖t‖ ^ (m - 1) ≤ (δ * (m : ℝ)) * ‖t‖ ^ (m - 1) := by
      rw [← hrm_eq, mul_assoc]
      exact le_trans hnorm (mul_le_mul_of_nonneg_left hsum_le hδpos.le)
    have hr_le : ‖t‖ ≤ δ * (m : ℝ) := le_of_mul_le_mul_right hrm hpow_pos
    linarith
  · have hsum_le : ∑ i ∈ Finset.range m, ‖t‖ ^ i ≤ (m : ℝ) := by
      calc ∑ i ∈ Finset.range m, ‖t‖ ^ i
          ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => pow_le_one₀ (norm_nonneg t) hr1
        _ = (m : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hrm : ‖t‖ ^ m ≤ δ * (m : ℝ) := le_trans hnorm (mul_le_mul_of_nonneg_left hsum_le hδpos.le)
    exact le_of_lt (lt_of_pow_lt_pow_left₀ m hR.le (lt_of_le_of_lt hrm hδmR))

end Puiseux
