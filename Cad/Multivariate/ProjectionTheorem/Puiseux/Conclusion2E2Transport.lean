import Cad.Multivariate.ProjectionTheorem.Puiseux.OrderInvariance
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Conclusion 2 — the e≥2 order transport (thesis stage 8, "t ≥ ord h'")

This file provides the key analytic core of the thesis's order-under-blow-up argument
(`thesis/thesis.tex`, §7 "Case II (conclusion)", the "`t ≥ ord h'`" term-tracking, lines 2388–2487).

The thesis shows that the order of a Weierstrass family `h` along its singular graph is transported to the
blown-up family `h' = h ∘ (Q × id)` by tracking a top-degree Taylor term: a nonzero degree-`t` term of `h`
becomes, after the quadratic substitution `Q`, a nonzero analytic coefficient in the ratio coordinates,
hence nonzero at *some* ratio point.

The clean analytic distillation is `exists_line_order_le`: if `F` vanishes to finite order `t` at `p`, then
among any **dense** set of directions, *some* direction realizes the order — its line restriction has order
`≤ t`. (The leading form `iteratedFDeriv ℂ t F p` is a nonzero symmetric multilinear map; if its diagonal
vanished on a dense set it would vanish identically, forcing the form to be zero by polarization.) This is
the same mechanism as `ZariskiE2.genericity_exists`, but for the *evaluation* (not the discriminant) and
over an arbitrary dense direction set.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Puiseux

/-- **Multivariate identity theorem corollary.** A nonzero analytic function on a (connected) normed
space is nonzero somewhere in every nonempty open set. -/
theorem exists_mem_open_ne_zero {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {Φ : P → ℂ} (hΦ : AnalyticOnNhd ℂ Φ Set.univ) {q₁ : P} (hq₁ : Φ q₁ ≠ 0)
    {V : Set P} (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ q ∈ V, Φ q ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨q₀, hq₀⟩ := hVne
  have hev : Φ =ᶠ[𝓝 q₀] 0 := by
    filter_upwards [hV.mem_nhds hq₀] with q hq using hcon q hq
  have hpre : IsPreconnected (Set.univ : Set P) := (convex_univ (𝕜 := ℝ)).isPreconnected
  exact hq₁ (hΦ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre (Set.mem_univ q₀) hev
    (Set.mem_univ q₁))

/-- **Order transport, parametrized form** (the directly-usable version for the blow-up). If `F` has finite
order `t` at `p`, `g : P → E` is an entire direction family whose range is dense, and `V` is any nonempty
open set of parameters, then some parameter `q ∈ V` realizes the order: the line `τ ↦ F (p + τ • g q)` has
order `≤ t`. Combines the polarization core (`exists_line_order_le`'s mechanism) with the identity theorem:
the leading form's diagonal pulled back along `g` is a nonzero analytic function of the parameter, hence
nonzero somewhere in `V`. -/
theorem exists_param_line_order_le {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    {F : E → ℂ} {p : E} (hF : AnalyticAt ℂ F p) {t : ℕ} (hord : order ℂ F p = (t : ℕ∞))
    {g : P → E} (hg : ∀ q, AnalyticAt ℂ g q) (hdense : Dense (Set.range g))
    {V : Set P} (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ q ∈ V, analyticOrderAt (fun τ : ℂ => F (p + τ • g q)) 0 ≤ (t : ℕ∞) := by
  set L := iteratedFDeriv ℂ t F p with hL
  have hLne : L ≠ 0 := (order_eq_natCast_iff.mp hord).2
  -- `Φ q = L (diagonal (g q))` is the leading form's diagonal pulled back along `g`; it is entire
  set Φ : P → ℂ := fun q => L (fun _ => g q) with hΦdef
  have hΦan : AnalyticOnNhd ℂ Φ Set.univ := by
    intro q _
    have h1 : AnalyticAt ℂ (fun w : E => (fun _ : Fin t => w)) (g q) :=
      (ContinuousLinearMap.pi (fun _ : Fin t => ContinuousLinearMap.id ℂ E)).analyticAt (g q)
    exact (L.analyticAt).comp (h1.comp (hg q))
  -- `Φ ≢ 0`: otherwise the leading form's diagonal vanishes on the dense range, hence everywhere
  have hΦne : ∃ q, Φ q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hLne
    refine symmetric_multilinear_eq_zero_of_diagonal_zero L
      (fun v σ => hF.contDiffAt.iteratedFDeriv_comp_perm v σ) ?_
    have hcont : Continuous (fun w : E => L (fun _ => w)) :=
      L.cont.comp (continuous_pi fun _ => continuous_id)
    have hclosed : IsClosed {w : E | L (fun _ => w) = 0} := isClosed_eq hcont continuous_const
    have hsub : Set.range g ⊆ {w : E | L (fun _ => w) = 0} := by rintro w ⟨q, rfl⟩; exact h q
    intro w
    exact (hclosed.closure_subset_iff.mpr hsub) (hdense.closure_eq ▸ Set.mem_univ w)
  -- find a parameter in `V` with `Φ ≠ 0` (identity theorem), then unfold to the line order
  obtain ⟨q₁, hq₁⟩ := hΦne
  obtain ⟨q, hqV, hqne⟩ := exists_mem_open_ne_zero hΦan hq₁ hV hVne
  refine ⟨q, hqV, ?_⟩
  by_contra hle
  push_neg at hle
  apply hqne
  show L (fun _ => g q) = 0
  have hle' : ((t + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun τ : ℂ => F (p + τ • g q)) 0 := by
    rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt hle
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_line_restriction F p (g q) hF)]
    at hle'
  have ht := hle' t (by omega)
  rw [iteratedDeriv_line_eq_iteratedFDeriv_diag F p (g q) t hF] at ht
  exact ht

/-- **The blow-up transverse directions are dense.** The directions `c • Fin.snoc w'' 1` reachable as the
`u`-slices of the quadratic transformation `Q` (over all scalings `c` and ratio vectors `w''`) are dense in
the transverse space `Fin (k+2) → ℂ` — they contain every vector with nonzero last coordinate (the
complement of the last-coordinate hyperplane). This is the density hypothesis for `exists_param_line_order_le`
in the e≥2 order transport. -/
theorem dense_smul_snoc {k : ℕ} :
    Dense (Set.range (fun cw : ℂ × (Fin (k + 1) → ℂ) =>
      cw.1 • (Fin.snoc cw.2 1 : Fin (k + 2) → ℂ))) := by
  have hsub : {T : Fin (k + 2) → ℂ | T (Fin.last (k + 1)) ≠ 0} ⊆
      Set.range (fun cw : ℂ × (Fin (k + 1) → ℂ) => cw.1 • (Fin.snoc cw.2 1 : Fin (k + 2) → ℂ)) := by
    intro T hT
    refine ⟨(T (Fin.last (k + 1)), fun i => T (Fin.castSucc i) / T (Fin.last (k + 1))), ?_⟩
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Fin.snoc_last]
    · intro i
      simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
      rw [mul_div_cancel₀ _ hT]
  have hdense : Dense {T : Fin (k + 2) → ℂ | T (Fin.last (k + 1)) ≠ 0} := by
    have hpre : {T : Fin (k + 2) → ℂ | T (Fin.last (k + 1)) ≠ 0}
        = (Function.eval (Fin.last (k + 1)) : (Fin (k + 2) → ℂ) → ℂ) ⁻¹' {0}ᶜ := by
      ext T; simp [Function.eval]
    rw [hpre]
    exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval (Fin.last (k + 1)))
  exact hdense.mono hsub

end Puiseux
