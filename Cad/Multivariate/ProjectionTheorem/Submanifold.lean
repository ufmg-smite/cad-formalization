import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Analytic submanifolds of `ℝⁿ`

McCallum's (p.20) definition of an analytic `s`-dimensional submanifold of `ℝⁿ`,
expressed via the regular value theorem (zero set of an analytic submersion).

## Main results

- `IsAnalyticSubmanifold` — definition of an analytic submanifold
- `IsAnalyticSubmanifold.straightening_chart` — Theorem 2.2.1: local coordinate chart
  straightening the submanifold to a coordinate subspace
-/

noncomputable section

open Set

variable {n : ℕ}

/-- `S` is an analytic `s`-dimensional submanifold of `ℝⁿ` (McCallum, Definition
p.20). For each `p ∈ S` there exist an open neighborhood `W` of `p` and an
analytic map `F : ℝⁿ → ℝ^{n-s}` for which `p` is a regular point (the Fréchet
derivative of `F` at `p` is surjective), such that `S ∩ W` is exactly the zero
set of `F` inside `W`. -/
def IsAnalyticSubmanifold (S : Set (Fin n → ℝ)) : Prop :=
  S.Nonempty ∧
  ∃ s : ℕ, s ≤ n ∧
    ∀ p ∈ S, ∃ W : Set (Fin n → ℝ), IsOpen W ∧ p ∈ W ∧
      ∃ F : (Fin n → ℝ) → (Fin (n - s) → ℝ),
        AnalyticOnNhd ℝ F W ∧
        Function.Surjective (fderiv ℝ F p) ∧
        (∀ x ∈ W, x ∈ S ↔ F x = 0)

/-! ### Linear algebra: complement of a surjective map -/

/-- Given a surjective continuous linear map `L : ℝⁿ →L ℝᵐ`, there exists a
continuous linear map `P : ℝⁿ →L ℝˢ` (where `s = n - m`) such that
`(P, L) : ℝⁿ → ℝˢ × ℝᵐ` is a continuous linear equivalence. -/
theorem exists_complement_of_surjective {n s : ℕ} (hs : s ≤ n)
    (L : (Fin n → ℝ) →L[ℝ] (Fin (n - s) → ℝ))
    (hL : Function.Surjective L) :
    ∃ P : (Fin n → ℝ) →L[ℝ] (Fin s → ℝ),
      Function.Bijective
        (fun v => (P v, L v) : (Fin n → ℝ) → (Fin s → ℝ) × (Fin (n - s) → ℝ)) := by
  -- Work with the underlying linear map
  set Lₗ := L.toLinearMap
  -- Rank-nullity: finrank (ker Lₗ) = s
  have hfr_range : Module.finrank ℝ (LinearMap.range Lₗ) = n - s := by
    rw [LinearMap.range_eq_top.mpr (show Function.Surjective Lₗ from hL), finrank_top,
      Module.finrank_fin_fun]
  have hfr_ker : Module.finrank ℝ (LinearMap.ker Lₗ) = s := by
    have h := LinearMap.finrank_range_add_finrank_ker Lₗ
    rw [hfr_range, Module.finrank_fin_fun] at h; omega
  set K := LinearMap.ker Lₗ
  -- Complement of K
  obtain ⟨Q, hKQ⟩ := K.exists_isCompl
  -- Linear equivalence K ≃ₗ[ℝ] (Fin s → ℝ)
  let e : K ≃ₗ[ℝ] (Fin s → ℝ) := LinearEquiv.ofFinrankEq K (Fin s → ℝ)
    (by rw [hfr_ker, Module.finrank_fin_fun])
  -- Build P: project to K, then apply e
  let proj := Submodule.linearProjOfIsCompl K Q hKQ
  let Pₗ : (Fin n → ℝ) →ₗ[ℝ] (Fin s → ℝ) := (e : K →ₗ[ℝ] (Fin s → ℝ)).comp proj
  let P : (Fin n → ℝ) →L[ℝ] (Fin s → ℝ) := LinearMap.toContinuousLinearMap Pₗ
  refine ⟨P, ?_⟩
  -- Rewrite as P.prod L
  show Function.Bijective (P.prod L)
  -- Dimensions match: n = s + (n - s)
  have hdim : Module.finrank ℝ (Fin n → ℝ) =
      Module.finrank ℝ ((Fin s → ℝ) × (Fin (n - s) → ℝ)) := by
    simp [Module.finrank_prod, Nat.add_comm s (n - s), Nat.sub_add_cancel hs]
  -- Helper: the combined map is injective
  have hinj : Function.Injective (P.prod L) := by
    intro v₁ v₂ hv
    have hPv := congr_arg Prod.fst hv
    have hLv := congr_arg Prod.snd hv
    simp only [ContinuousLinearMap.prod_apply] at hPv hLv
    suffices h : v₁ - v₂ = 0 from sub_eq_zero.mp h
    set w := v₁ - v₂
    -- L w = 0 ⟹ w ∈ K
    have hLw : L w = 0 := by simp [w, map_sub, sub_eq_zero.mpr hLv]
    have hw_K : w ∈ K := LinearMap.mem_ker.mpr (show Lₗ w = 0 from hLw)
    -- P w = 0 ⟹ proj w = 0 ⟹ w ∈ Q
    have hPw : P w = 0 := by simp [w, map_sub, sub_eq_zero.mpr hPv]
    have hw_Q : w ∈ Q := by
      rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hKQ]
      have he : e (proj w) = 0 := (show Pₗ w = 0 from hPw)
      exact_mod_cast e.injective (by rw [he, map_zero] : e (proj w) = e 0)
    -- w ∈ K ⊓ Q = ⊥
    have : w ∈ K ⊓ Q := Submodule.mem_inf.mpr ⟨hw_K, hw_Q⟩
    rwa [hKQ.disjoint.eq_bot, Submodule.mem_bot] at this
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-! ### Theorem 2.2.1: Submanifold straightening chart -/

/-- **Theorem 2.2.1** (Submanifold straightening / coordinate chart).

For an `s`-dimensional analytic submanifold `S` of `ℝⁿ` and a point `p ∈ S`,
there exist:
- open neighborhoods `U` of `p` and `V` of `0` in `ℝˢ × ℝ^{n-s}`,
- an analytic diffeomorphism `Φ : U → V` with `Φ(p) = 0`,
such that `S ∩ U = { x ∈ U : snd(Φ(x)) = 0 }`.

The "straightening" property means that `Φ` maps `S` locally to the coordinate
subspace `ℝˢ × {0}`. -/
theorem IsAnalyticSubmanifold.straightening_chart
    {S : Set (Fin n → ℝ)}
    (hS : IsAnalyticSubmanifold S)
    (p : Fin n → ℝ) (hp : p ∈ S) :
    ∃ s : ℕ, s ≤ n ∧
    ∃ (Φ : OpenPartialHomeomorph (Fin n → ℝ) ((Fin s → ℝ) × (Fin (n - s) → ℝ))),
      p ∈ Φ.source ∧
      Φ p = (0, 0) ∧
      (∀ x ∈ Φ.source, AnalyticAt ℝ Φ x) ∧
      AnalyticAt ℝ Φ.symm (Φ p) ∧
      (∀ x ∈ Φ.source, x ∈ S ↔ (Φ x).2 = 0) := by
  obtain ⟨_, s, hs, hS_data⟩ := hS
  obtain ⟨W, hW_open, hp_W, F, hF_an, hF_surj, hF_zero⟩ := hS_data p hp
  refine ⟨s, hs, ?_⟩
  -- Step 1: Get the complement projection P
  obtain ⟨P, hPL_bij⟩ := exists_complement_of_surjective hs (fderiv ℝ F p) hF_surj
  -- Step 2: Build the chart map Φ(x) = (P(x - p), F(x))
  let Φ : (Fin n → ℝ) → (Fin s → ℝ) × (Fin (n - s) → ℝ) :=
    fun x => (P (x - p), F x)
  -- Step 3: Φ is analytic at p
  have hΦ_an : AnalyticAt ℝ Φ p :=
    AnalyticAt.prod
      (AnalyticAt.comp (P.analyticAt _) (analyticAt_id.sub analyticAt_const))
      (hF_an p hp_W)
  -- Step 4: fderiv of (x ↦ P(x - p)) at p equals P
  have hfderiv_Pp : HasFDerivAt (fun x => P (x - p))
      (P : (Fin n → ℝ) →L[ℝ] (Fin s → ℝ)) p := by
    have h1 : HasFDerivAt (fun x : Fin n → ℝ => x - p)
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p := by
      have := (hasFDerivAt_id (𝕜 := ℝ) p).sub
        (hasFDerivAt_const (𝕜 := ℝ) (x := p) p)
      simp at this ⊢
      exact this
    have h2 := P.hasFDerivAt.comp p h1
    rwa [ContinuousLinearMap.comp_id] at h2
  -- Step 5: HasFDerivAt for Φ
  have hF_hasFDeriv : HasFDerivAt F (fderiv ℝ F p) p :=
    (hF_an p hp_W).differentiableAt.hasFDerivAt
  have hΦ_hasFDeriv : HasFDerivAt Φ (P.prod (fderiv ℝ F p)) p :=
    hfderiv_Pp.prodMk hF_hasFDeriv
  -- Step 6: fderiv Φ p is bijective (from the complement lemma)
  have hΦ_bij : Function.Bijective (fderiv ℝ Φ p) := by
    rw [hΦ_hasFDeriv.fderiv]
    exact hPL_bij
  -- Step 7: Build ContinuousLinearEquiv and apply IFT
  let i : (Fin n → ℝ) ≃L[ℝ] (Fin s → ℝ) × (Fin (n - s) → ℝ) :=
    (LinearEquiv.ofBijective (fderiv ℝ Φ p).toLinearMap hΦ_bij).toContinuousLinearEquiv
  have hi : fderiv ℝ Φ p = i.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun _ => rfl
  have hΦ_strict : HasStrictFDerivAt Φ (i : (Fin n → ℝ) →L[ℝ] _) p :=
    hi ▸ hΦ_an.hasStrictFDerivAt
  let R₀ := hΦ_strict.toOpenPartialHomeomorph Φ
  have hR₀_source : p ∈ R₀.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  -- Restrict R₀ to W so the straightening property can use hF_zero
  let R := R₀.restr W
  have hR_source : p ∈ R.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hW_open]
    exact ⟨hR₀_source, hp_W⟩
  -- Step 8: Φ(p) = (0, 0)
  have hΦ_val : Φ p = (0, 0) :=
    Prod.ext (by simp [Φ]) ((hF_zero p hp_W).mp hp)
  -- Step 9: Analyticity of R.symm at Φ(p)
  have hR_an_symm : AnalyticAt ℝ R.symm (Φ p) := by
    have hR₀_an_symm := R₀.analyticAt_symm' hR₀_source hΦ_an hi
    convert hR₀_an_symm using 1
  -- Step 10: Straightening property — x ∈ S ↔ F(x) = 0 ↔ snd(Φ(x)) = 0
  have hR_straight : ∀ x ∈ R.source, x ∈ S ↔ (Φ x).2 = 0 := by
    intro x hx
    rw [OpenPartialHomeomorph.restr_source' _ _ hW_open] at hx
    simp only [Φ, hF_zero x hx.2]
  have hΦ_an_all : ∀ x ∈ R.source, AnalyticAt ℝ Φ x := by
    intro x hx
    rw [OpenPartialHomeomorph.restr_source' _ _ hW_open] at hx
    exact AnalyticAt.prod
      (AnalyticAt.comp (P.analyticAt _) (analyticAt_id.sub analyticAt_const))
      (hF_an x hx.2)
  exact ⟨R, hR_source, hΦ_val, hΦ_an_all, hR_an_symm, hR_straight⟩

end
