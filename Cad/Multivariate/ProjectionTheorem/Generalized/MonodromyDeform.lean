import Cad.Multivariate.ProjectionTheorem.Generalized.MonodromyGen
import Mathlib.Topology.Homotopy.Path

/-!
# M3 — the two explicit deformations (thesis Theorem 4.2.2, steps 7–8)

The root-exchange loop `Γ` from Lemma 4.2.5 (`rootCover_exchange_gen`) is deformed, within the separable
locus `U`, to a small loop `Γ''` that runs along the transverse circle `|z₀| = |w'₀|` with the section
coordinates pinned to `w' = Γ 0`. Two explicit path homotopies do it:

* `H(s,t) = ((1−s)·Γ_sec(t) + s·w'_sec, Γ₀(t))` — collapse the section component to the constant `w'`,
  leaving the transverse coordinate `z₀ = Γ₀(t)` untouched;
* `K(s,t) = (w'_sec, [(1−s) + s·|w'₀|/|Γ₀(t)|]·Γ₀(t))` — push the transverse coordinate radially onto
  the circle `|z₀| = |w'₀|`.

**Design.** We take the base neighbourhood to be a *punctured sup-norm ball*
`U = ball 0 δ ∩ {z | z₀ ≠ 0}`. In normal form (`disc = z₀^r·N`, `N` non-vanishing) this is exactly the
separable locus, so `rootCover_exchange_gen` applies to it; and both homotopies stay inside it for free
(`H` interpolates the section coordinates — the sup-ball is convex — keeping `z₀ ≠ 0`; `K` rescales `z₀`
by a positive real, so `|z₀|` stays a convex combination of `|Γ₀(t)|` and `|w'₀|`, both `< δ` and `> 0`).

The output `deform_to_transverse_loop` is exactly the `Γ.HomotopicRel Γ'' {0,1}` consumed by
`monodromy_exchange_contradiction`, together with the two facts (section constant, transverse modulus
constant) that let M4 feed `Γ''` into the M2 confinement at the slice `q(w'_sec, ·)`.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace MonodromyDeform

variable {n : ℕ}

/-- The **punctured sup-norm ball** `ball 0 δ ∩ {z | z₀ ≠ 0}`: the separable locus in normal form, and
the neighbourhood the deformation lives in. -/
def punctBall (δ : ℝ) : Set (Fin (n + 1) → ℂ) := ball 0 δ ∩ {z | z 0 ≠ 0}

lemma mem_punctBall {δ : ℝ} {z : Fin (n + 1) → ℂ} :
    z ∈ punctBall δ ↔ ‖z‖ < δ ∧ z 0 ≠ 0 := by
  simp only [punctBall, Set.mem_inter_iff, mem_ball, dist_zero_right, Set.mem_setOf_eq]

/-- Build a `HomotopyRel` into the subtype `↥(punctBall δ)` from an ambient homotopy formula `F` that
stays in the ball, with the prescribed endpoints and a fixed boundary on `{0,1}`. -/
def mkHomRel {δ : ℝ} {f₀ f₁ : C(unitInterval, ↥(punctBall (n := n) δ))}
    (F : C(unitInterval × unitInterval, Fin (n + 1) → ℂ))
    (hmem : ∀ p, F p ∈ punctBall δ)
    (h0 : ∀ t, F (0, t) = (f₀ t : Fin (n + 1) → ℂ))
    (h1 : ∀ t, F (1, t) = (f₁ t : Fin (n + 1) → ℂ))
    (hrel : ∀ s, ∀ x ∈ ({0, 1} : Set unitInterval), F (s, x) = (f₀ x : Fin (n + 1) → ℂ)) :
    ContinuousMap.HomotopyRel f₀ f₁ {0, 1} where
  toFun p := ⟨F p, hmem p⟩
  continuous_toFun := F.continuous.subtype_mk hmem
  map_zero_left t := Subtype.ext (h0 t)
  map_one_left t := Subtype.ext (h1 t)
  prop' s x hx := Subtype.ext (hrel s x hx)

/-- **M3 (thesis steps 7–8).** A loop `Γ` in the punctured ball, based at `w' = Γ 0`, deforms — rel its
endpoints — to a loop `Γ''` whose section coordinates are pinned to `w'` (`Γ'' t i = w' i` for `i ≠ 0`)
and whose transverse coordinate runs on the circle `|z₀| = |w'₀|` (`‖Γ'' t 0‖ = ‖w'₀‖`). This is the
deformation `Γ ≃ Γ''` (the composite of the section-collapse `H` and the radial push `K`) that the
homotopy-deformation contradiction consumes. -/
theorem deform_to_transverse_loop {δ : ℝ} (hδ : 0 < δ)
    (Γ : C(unitInterval, ↥(punctBall (n := n) δ))) (hloop : Γ 0 = Γ 1) :
    ∃ Γ'' : C(unitInterval, ↥(punctBall (n := n) δ)),
      (∀ t, ∀ i, i ≠ 0 → (Γ'' t : Fin (n + 1) → ℂ) i = (Γ 0 : Fin (n + 1) → ℂ) i) ∧
      (∀ t, ‖(Γ'' t : Fin (n + 1) → ℂ) 0‖ = ‖(Γ 0 : Fin (n + 1) → ℂ) 0‖) ∧
      Γ.HomotopicRel Γ'' {0, 1} := by
  classical
  -- the ambient loop and basic facts
  set g : unitInterval → (Fin (n + 1) → ℂ) := fun t => (Γ t : Fin (n + 1) → ℂ) with hg
  have hg_cont : Continuous g := continuous_subtype_val.comp Γ.continuous
  have hg_mem : ∀ t, g t ∈ punctBall δ := fun t => (Γ t).2
  have hg0_ne : ∀ t, g t 0 ≠ 0 := fun t => (mem_punctBall.mp (hg_mem t)).2
  have hg_norm : ∀ t, ‖g t‖ < δ := fun t => (mem_punctBall.mp (hg_mem t)).1
  have hg_ball : ∀ t, g t ∈ ball (0 : Fin (n + 1) → ℂ) δ := fun t => (hg_mem t).1
  have hloop' : g 1 = g 0 := congrArg Subtype.val hloop.symm
  have hgt0_norm_ne : ∀ t, ‖g t 0‖ ≠ 0 := fun t => norm_ne_zero_iff.mpr (hg0_ne t)
  have hg00_norm_ne : ‖g 0 0‖ ≠ 0 := hgt0_norm_ne 0
  have hI0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have hI1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  -- a real convexity helper
  have conv_lt : ∀ w a b : ℝ, 0 ≤ w → w ≤ 1 → a < δ → b < δ → (1 - w) * a + w * b < δ := by
    intro w a b hw0 hw1 ha hb
    rcases eq_or_lt_of_le hw0 with hw | hw
    · rw [← hw]; simpa using ha
    · have h1 : w * (b - δ) < 0 := mul_neg_of_pos_of_neg hw (by linarith)
      have h2 : (1 - w) * (a - δ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith [h1, h2]
  -- the section-collapsed loop `Γ'` (transverse `= g t 0`, section `= g 0`)
  set c : unitInterval → (Fin (n + 1) → ℂ) := fun t => Function.update (g 0) 0 (g t 0) with hc
  have hc_def : ∀ t, c t = Function.update (g 0) 0 (g t 0) := fun _ => rfl
  have hc_cont : Continuous c := by
    refine continuous_pi fun i => ?_
    simp only [hc, Function.update_apply]
    split_ifs
    · exact (continuous_apply 0).comp hg_cont
    · exact continuous_const
  have hc_mem : ∀ t, c t ∈ punctBall δ := fun t => by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
      intro i
      rw [hc_def, Function.update_apply]
      split_ifs
      · exact lt_of_le_of_lt (norm_le_pi_norm (g t) 0) (hg_norm t)
      · exact lt_of_le_of_lt (norm_le_pi_norm (g 0) i) (hg_norm 0)
    · show c t 0 ≠ 0
      rw [hc_def, Function.update_self]; exact hg0_ne t
  set Γ' : C(unitInterval, ↥(punctBall (n := n) δ)) :=
    ⟨fun t => ⟨c t, hc_mem t⟩, hc_cont.subtype_mk hc_mem⟩ with hΓ'
  -- the transverse-circle loop `Γ''`
  set d : unitInterval → (Fin (n + 1) → ℂ) :=
    fun t => Function.update (g 0) 0 ((‖g 0 0‖ / ‖g t 0‖ : ℝ) • g t 0) with hd
  have hd_def : ∀ t, d t = Function.update (g 0) 0 ((‖g 0 0‖ / ‖g t 0‖ : ℝ) • g t 0) := fun _ => rfl
  have hd0_norm : ∀ t, ‖d t 0‖ = ‖g 0 0‖ := fun t => by
    rw [hd_def, Function.update_self, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (hgt0_norm_ne t)]
  have hd0_ne : ∀ t, d t 0 ≠ 0 := fun t => by
    rw [hd_def, Function.update_self]
    exact smul_ne_zero (div_ne_zero hg00_norm_ne (hgt0_norm_ne t)) (hg0_ne t)
  have hd_cont : Continuous d := by
    refine continuous_pi fun i => ?_
    simp only [hd, Function.update_apply]
    split_ifs
    · exact ((continuous_const.div (continuous_norm.comp ((continuous_apply 0).comp hg_cont))
        fun t => hgt0_norm_ne t).smul ((continuous_apply 0).comp hg_cont))
    · exact continuous_const
  have hd_mem : ∀ t, d t ∈ punctBall δ := fun t => by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
      intro i
      rcases eq_or_ne i 0 with h | h
      · subst h; rw [hd0_norm]; exact lt_of_le_of_lt (norm_le_pi_norm (g 0) 0) (hg_norm 0)
      · rw [hd_def, Function.update_of_ne h]; exact lt_of_le_of_lt (norm_le_pi_norm (g 0) i) (hg_norm 0)
    · exact hd0_ne t
  set Γ'' : C(unitInterval, ↥(punctBall (n := n) δ)) :=
    ⟨fun t => ⟨d t, hd_mem t⟩, hd_cont.subtype_mk hd_mem⟩ with hΓ''
  have hc0 : c 0 = g 0 := by rw [hc_def, Function.update_eq_self]
  have hc1 : c 1 = g 0 := by rw [hc_def, hloop', Function.update_eq_self]
  -- the section-collapse homotopy `H : Γ ≃ Γ'`
  have hs_cont : Continuous (fun p : unitInterval × unitInterval => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have H_cont : Continuous
      (fun p : unitInterval × unitInterval => (1 - (p.1 : ℝ)) • g p.2 + (p.1 : ℝ) • c p.2) :=
    ((continuous_const.sub hs_cont).smul (hg_cont.comp continuous_snd)).add
      (hs_cont.smul (hc_cont.comp continuous_snd))
  have H_coord0 : ∀ (s t : unitInterval),
      ((1 - (s : ℝ)) • g t + (s : ℝ) • c t) 0 = g t 0 := fun s t => by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hc_def, Function.update_self, ← add_smul,
      show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul]
  have H_mem : ∀ p : unitInterval × unitInterval,
      ((1 - (p.1 : ℝ)) • g p.2 + (p.1 : ℝ) • c p.2) ∈ punctBall δ := by
    rintro ⟨s, t⟩
    refine ⟨convex_ball (0 : Fin (n + 1) → ℂ) δ (hg_ball t) (hc_mem t).1
      (by linarith [unitInterval.le_one s]) (unitInterval.nonneg s) (by ring), ?_⟩
    show ((1 - (s : ℝ)) • g t + (s : ℝ) • c t) 0 ≠ 0
    rw [H_coord0]; exact hg0_ne t
  have hH : ContinuousMap.HomotopyRel Γ Γ' {0, 1} :=
    mkHomRel ⟨_, H_cont⟩ H_mem
      (fun t => by
        show (1 - ((0 : unitInterval) : ℝ)) • g t + ((0 : unitInterval) : ℝ) • c t = g t
        rw [hI0, sub_zero, one_smul, zero_smul, add_zero])
      (fun t => by
        show (1 - ((1 : unitInterval) : ℝ)) • g t + ((1 : unitInterval) : ℝ) • c t = c t
        rw [hI1, sub_self, zero_smul, one_smul, zero_add])
      (fun s x hx => by
        rcases hx with hx | hx
        · subst hx
          show (1 - (s : ℝ)) • g 0 + (s : ℝ) • c 0 = g 0
          rw [hc0, ← add_smul, show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul]
        · rw [Set.mem_singleton_iff] at hx; subst hx
          show (1 - (s : ℝ)) • g 1 + (s : ℝ) • c 1 = g 1
          rw [hc1, hloop', ← add_smul, show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul])
  -- the radial homotopy `K : Γ' ≃ Γ''`
  set K : unitInterval × unitInterval → (Fin (n + 1) → ℂ) :=
    fun p => Function.update (g 0) 0
      (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (‖g 0 0‖ / ‖g p.2 0‖)) • g p.2 0) with hK
  have hK_def : ∀ s t, K (s, t) = Function.update (g 0) 0
      (((1 - (s : ℝ)) + (s : ℝ) * (‖g 0 0‖ / ‖g t 0‖)) • g t 0) := fun _ _ => rfl
  have K_cont : Continuous K := by
    refine continuous_pi fun i => ?_
    simp only [hK, Function.update_apply]
    split_ifs
    · exact (((continuous_const.sub hs_cont).add (hs_cont.mul (continuous_const.div
        (continuous_norm.comp ((continuous_apply 0).comp (hg_cont.comp continuous_snd)))
        fun p => hgt0_norm_ne p.2))).smul
        ((continuous_apply 0).comp (hg_cont.comp continuous_snd)))
    · exact continuous_const
  have K_coeff_nonneg : ∀ (s t : unitInterval),
      0 ≤ (1 - (s : ℝ)) + (s : ℝ) * (‖g 0 0‖ / ‖g t 0‖) := fun s t => by
    have : 0 ≤ (s : ℝ) * (‖g 0 0‖ / ‖g t 0‖) := mul_nonneg (unitInterval.nonneg s) (by positivity)
    linarith [unitInterval.le_one s]
  have K_coeff_pos : ∀ (s t : unitInterval),
      0 < (1 - (s : ℝ)) + (s : ℝ) * (‖g 0 0‖ / ‖g t 0‖) := fun s t => by
    have hdiv : 0 < ‖g 0 0‖ / ‖g t 0‖ :=
      div_pos (norm_pos_iff.mpr (hg0_ne 0)) (norm_pos_iff.mpr (hg0_ne t))
    rcases lt_or_eq_of_le (unitInterval.le_one s) with h | h
    · have : 0 ≤ (s : ℝ) * (‖g 0 0‖ / ‖g t 0‖) := mul_nonneg (unitInterval.nonneg s) hdiv.le
      linarith
    · rw [h]; simpa using hdiv
  have K_mem : ∀ p : unitInterval × unitInterval, K p ∈ punctBall δ := by
    rintro ⟨s, t⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
      intro i
      rcases eq_or_ne i 0 with h | h
      · subst h
        rw [hK_def, Function.update_self, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (K_coeff_nonneg s t)]
        have heq : ((1 - (s : ℝ)) + (s : ℝ) * (‖g 0 0‖ / ‖g t 0‖)) * ‖g t 0‖
            = (1 - (s : ℝ)) * ‖g t 0‖ + (s : ℝ) * ‖g 0 0‖ := by
          rw [add_mul, mul_assoc, div_mul_cancel₀ _ (hgt0_norm_ne t)]
        rw [heq]
        exact conv_lt (s : ℝ) ‖g t 0‖ ‖g 0 0‖ (unitInterval.nonneg s) (unitInterval.le_one s)
          (lt_of_le_of_lt (norm_le_pi_norm (g t) 0) (hg_norm t))
          (lt_of_le_of_lt (norm_le_pi_norm (g 0) 0) (hg_norm 0))
      · rw [hK_def, Function.update_of_ne h]
        exact lt_of_le_of_lt (norm_le_pi_norm (g 0) i) (hg_norm 0)
    · show K (s, t) 0 ≠ 0
      rw [hK_def, Function.update_self]
      exact smul_ne_zero (K_coeff_pos s t).ne' (hg0_ne t)
  have hK0 : ∀ t, K (0, t) = c t := fun t => by
    rw [hK_def, hI0]
    simp only [sub_zero, zero_mul, add_zero, one_smul]
    exact (hc_def t).symm
  have hK1 : ∀ t, K (1, t) = d t := fun t => by
    rw [hK_def, hI1]
    simp only [sub_self, one_mul, zero_add]
    exact (hd_def t).symm
  have hK : ContinuousMap.HomotopyRel Γ' Γ'' {0, 1} :=
    mkHomRel ⟨_, K_cont⟩ K_mem hK0 hK1
      (fun s x hx => by
        rcases hx with hx | hx
        · subst hx
          show K (s, 0) = (Γ' 0 : Fin (n + 1) → ℂ)
          rw [hK_def, div_self hg00_norm_ne, mul_one,
            show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul, Function.update_eq_self]
          exact hc0.symm
        · rw [Set.mem_singleton_iff] at hx; subst hx
          show K (s, 1) = (Γ' 1 : Fin (n + 1) → ℂ)
          rw [hK_def, hloop', div_self hg00_norm_ne, mul_one,
            show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul, Function.update_eq_self]
          exact hc1.symm)
  -- assemble
  refine ⟨Γ'', ?_, ?_, ⟨hH.trans hK⟩⟩
  · intro t i hi
    show d t i = g 0 i
    rw [hd_def, Function.update_of_ne hi]
  · intro t
    show ‖d t 0‖ = ‖g 0 0‖
    rw [hd0_norm]

end MonodromyDeform
