import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVMultiIndex
import Cad.Multivariate.ProjectionTheorem.Generalized.CSCVBridgeStep

/-!
# The iterated-Cauchy value — multi-index induction on dimension (WIP)

The remaining crux of the `ℂⁿ` bridge: a function `f : (Fin n → ℂ) → ℂ` differentiable and bounded on a
closed polydisc has a multi-index power-series representation
`f(z₀+y) = ∑_{α : Fin n → ℕ} c_α · ∏ⱼ yⱼ^{αⱼ}`, with `‖c_α‖ ≤ M/R^{|α|}` (the `n`-fold nested Cauchy
estimate). The proof is by **induction on `n`**: peel the first coordinate by the 1-variable Cauchy
expansion, get coefficient functions `Bₖ` analytic in the remaining `n−1` variables (induction
hypothesis), and combine via the clean `Fin.cons` split `(Fin (n+1) → ℕ) ≃ ℕ × (Fin n → ℕ)` — **no
multiplicity / polarization**.

This file builds the induction. The multi-index formulation (rather than the assignment-based
`mtSeries`) keeps the split clean: each monomial `∏ yⱼ^{αⱼ}` appears exactly once.
-/

noncomputable section

open Complex Metric Finset
open scoped Real Topology

/-- `‖Fin.cons a v‖ ≤ R` from `‖a‖ ≤ R` and `‖v‖ ≤ R` (the sup-norm bound on a `cons`). -/
theorem norm_cons_le {n : ℕ} {a : ℂ} {v : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : ‖a‖ ≤ R) (hv : ‖v‖ ≤ R) : ‖(Fin.cons a v : Fin (n + 1) → ℂ)‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  refine Fin.cases ?_ ?_ i
  · rwa [Fin.cons_zero]
  · intro j; rw [Fin.cons_succ]; exact (norm_le_pi_norm v j).trans hv

/-- `‖Fin.tail y‖ ≤ ‖y‖` (dropping the first coordinate cannot increase the sup-norm). -/
theorem norm_tail_le {n : ℕ} (y : Fin (n + 1) → ℂ) : ‖Fin.tail y‖ ≤ ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i; exact norm_le_pi_norm y i.succ

/-- Membership of a `cons` in a closed polydisc-ball, from the coordinatewise distance bounds. -/
theorem cons_mem_closedBall {n : ℕ} {z₀ : Fin (n + 1) → ℂ} {R : ℝ} (hR : 0 ≤ R) {ζ : ℂ}
    {w : Fin n → ℂ} (hζ : ‖ζ - z₀ 0‖ ≤ R) (hw : ‖w - Fin.tail z₀‖ ≤ R) :
    Fin.cons ζ w ∈ closedBall z₀ R := by
  rw [mem_closedBall, dist_eq_norm]
  have hsub : Fin.cons ζ w - z₀ = Fin.cons (ζ - z₀ 0) (w - Fin.tail z₀) := by
    conv_lhs => rw [← Fin.cons_self_tail z₀]
    funext i
    refine Fin.cases ?_ ?_ i <;> simp [Fin.tail]
  rw [hsub]
  exact norm_cons_le hR hζ hw

/-- **Cauchy estimate for `stepB`:** if `‖f(ζ,w)‖ ≤ Mf` for `ζ` on the circle `C(z₀,rz)`, then
`‖stepB f z₀ rz k w‖ ≤ Mf / rz^k`. (The 1-fold analog of `norm_scvCoeff_le`.) -/
theorem norm_stepB_le {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {f : ℂ × E' → ℂ} {z₀ : ℂ} {rz Mf : ℝ} (hrz : 0 < rz) (k : ℕ) (w : E')
    (hb : ∀ ζ ∈ sphere z₀ rz, ‖f (ζ, w)‖ ≤ Mf) :
    ‖stepB f z₀ rz k w‖ ≤ Mf / rz ^ k := by
  have hnorminv : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by rw [norm_inv, norm_two_pi_I]
  have hI : ‖∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (k + 1))⁻¹ • f (ζ, w)‖
      ≤ 2 * π * rz * (Mf / rz ^ (k + 1)) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hrz.le fun ζ hζ => ?_
    have hζn : ‖ζ - z₀‖ = rz := mem_sphere_iff_norm.mp hζ
    rw [norm_smul, norm_inv, norm_pow, hζn, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hb ζ hζ) (by positivity)
  rw [stepB, norm_smul, hnorminv]
  calc (2 * π)⁻¹ * ‖∮ ζ in C(z₀, rz), ((ζ - z₀) ^ (k + 1))⁻¹ • f (ζ, w)‖
      ≤ (2 * π)⁻¹ * (2 * π * rz * (Mf / rz ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = Mf / rz ^ k := by rw [pow_succ]; field_simp

/-- **Monomial `Fin.cons` split:** the multi-index monomial factors cleanly along the first
coordinate — `∏ⱼ yⱼ^{(cons k β)ⱼ} = y₀ᵏ · ∏ᵢ y_{i+1}^{βᵢ}`. (No multinomial factor: this is why the
multi-index formulation gives a clean induction.) -/
theorem prod_pow_cons {n : ℕ} (y : Fin (n + 1) → ℂ) (k : ℕ) (β : Fin n → ℕ) :
    ∏ j : Fin (n + 1), y j ^ (Fin.cons k β : Fin (n + 1) → ℕ) j
      = y 0 ^ k * ∏ i : Fin n, y i.succ ^ β i := by
  simp [Fin.prod_univ_succ]

/-- **`cons`-reindexing of `HasSum`:** a `HasSum` over `(k, β) ∈ ℕ × (Fin n → ℕ)` of `g (cons k β)`
gives a `HasSum` over the full multi-index space `Fin (n+1) → ℕ` (via `Fin.consEquiv`). -/
theorem hasSum_cons {n : ℕ} {g : (Fin (n + 1) → ℕ) → ℂ} {S : ℂ}
    (h : HasSum (fun p : ℕ × (Fin n → ℕ) => g (Fin.cons p.1 p.2)) S) :
    HasSum g S :=
  (Equiv.hasSum_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mp h

/-- **Multi-index summability** (product of geometrics): for `0 ≤ t < 1`, the family
`t^{∑ⱼ αⱼ}` over multi-indices `α : Fin n → ℕ` is summable. Proof: induction on `n`, factoring the
exponent along `Fin.cons` and using `Summable.mul_of_nonneg`. -/
theorem summable_multiIndex_pow (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun α : Fin n → ℕ => t ^ ∑ j, α j) := by
  induction n with
  | zero => exact (hasSum_unique fun α : Fin 0 → ℕ => t ^ ∑ j, α j).summable
  | succ n IH =>
    refine (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mp ?_
    have h := (summable_geometric_of_lt_one ht0 ht1).mul_of_nonneg IH
      (fun k => by positivity) fun β => by positivity
    refine h.congr fun p => ?_
    show t ^ p.1 * t ^ (∑ i, p.2 i) = t ^ ∑ j, (Fin.cons p.1 p.2 : Fin (n + 1) → ℕ) j
    rw [← pow_add]
    congr 1
    rw [Fin.sum_univ_succ]; simp

/-- **The iterated-Cauchy value (multi-index induction on dimension).** A function `f` differentiable
and bounded by `M` on the closed polydisc-ball `closedBall z₀ R` has, for any working radius `0<r<R`,
a multi-index power-series expansion `f(z₀+y) = ∑_{α} c_α · ∏ⱼ yⱼ^{αⱼ}` with the `n`-fold Cauchy bound
`‖c_α‖ ≤ M/r^{|α|}`, valid for `‖y‖ < r`. Proof by induction on `n`: peel the first coordinate by the
1-variable Cauchy expansion (`stepB_hasSum`), the `z`-coefficients `Bₖ` are differentiable in the
remaining variables (`stepB_hasFDerivAt`) and bounded (`norm_stepB_le`), so the induction hypothesis
applies to each `Bₖ`; reassemble along the clean `Fin.cons` split. -/
theorem multiIndexCauchy : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) {R M : ℝ},
    (∀ z ∈ closedBall z₀ R, DifferentiableAt ℂ f z) → (∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M) →
    ∀ {r : ℝ}, 0 < r → r < R →
    ∃ c : (Fin n → ℕ) → ℂ, (∀ α, ‖c α‖ ≤ M / r ^ (∑ j, α j)) ∧
      ∀ y : Fin n → ℂ, ‖y‖ < r → HasSum (fun α => c α * ∏ j, y j ^ α j) (f (z₀ + y)) := by
  intro n
  induction n with
  | zero =>
    intro f z₀ R M _ hb r hr0 hrR
    refine ⟨fun _ => f z₀, fun α => ?_, fun y _ => ?_⟩
    · rw [show (∑ j : Fin 0, α j) = 0 from by simp, pow_zero, div_one]
      exact hb z₀ (mem_closedBall_self (by linarith))
    · rw [Subsingleton.elim (z₀ + y) z₀]
      simp
  | succ n IH =>
    intro f z₀ R M hd hb r hr0 hrR
    have hR0 : (0 : ℝ) < R := lt_trans hr0 hrR
    set R' : ℝ := (r + R) / 2 with hR'_def
    have hrR' : r < R' := by rw [hR'_def]; linarith
    have hR'R : R' < R := by rw [hR'_def]; linarith
    have hR'0 : 0 < R' := lt_trans hr0 hrR'
    set z00 : ℂ := z₀ 0 with hz00
    set w₀ : Fin n → ℂ := Fin.tail z₀ with hw₀
    have hz₀cons : z₀ = Fin.cons z00 w₀ := (Fin.cons_self_tail z₀).symm
    set g : ℂ × (Fin n → ℂ) → ℂ := fun p => f (Fin.cons p.1 p.2) with hg
    -- membership of a `cons` in the polydisc, from coordinate bounds
    have hg_mem : ∀ (ζ : ℂ) (w : Fin n → ℂ), ‖ζ - z00‖ ≤ R → ‖w - w₀‖ ≤ R →
        (Fin.cons ζ w : Fin (n + 1) → ℂ) ∈ closedBall z₀ R := fun ζ w hζ hw =>
      cons_mem_closedBall hR0.le hζ hw
    -- `g` is differentiable / bounded where the corresponding `cons` lies in the polydisc
    have hg_diff : ∀ p : ℂ × (Fin n → ℂ), (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ) ∈ closedBall z₀ R →
        DifferentiableAt ℂ g p := fun p hp =>
      (hd (Fin.cons p.1 p.2) hp).comp p
        (Fin.consEquivL (R := ℂ) (M := fun _ : Fin (n + 1) => ℂ)).differentiableAt
    have hg_bound : ∀ p : ℂ × (Fin n → ℂ), (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ) ∈ closedBall z₀ R →
        ‖g p‖ ≤ M := fun p hp => hb _ hp
    -- `Bₖ` is differentiable on the `w`-polydisc `closedBall w₀ R'`
    have hBk_diff : ∀ (k : ℕ), ∀ w₁ ∈ closedBall w₀ R', DifferentiableAt ℂ (stepB g z00 r k) w₁ := by
      intro k w₁ hw₁
      have hmem : ∀ q ∈ closedBall (z00 : ℂ) R ×ˢ closedBall w₁ (R - R'),
          DifferentiableAt ℂ g q := by
        rintro ⟨a, b⟩ hq
        rw [Set.mem_prod, mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm] at hq
        refine hg_diff (a, b) (hg_mem a b hq.1 ?_)
        calc ‖b - w₀‖ ≤ ‖b - w₁‖ + ‖w₁ - w₀‖ := by
              rw [show b - w₀ = (b - w₁) + (w₁ - w₀) by ring]; exact norm_add_le _ _
          _ ≤ (R - R') + R' := by
              gcongr ?_ + ?_
              · exact hq.2
              · rw [← dist_eq_norm]; exact mem_closedBall.1 hw₁
          _ = R := by ring
      have hbd : ∀ q ∈ closedBall (z00 : ℂ) R ×ˢ closedBall w₁ (R - R'), ‖g q‖ ≤ M := by
        rintro ⟨a, b⟩ hq
        rw [Set.mem_prod, mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm] at hq
        refine hg_bound (a, b) (hg_mem a b hq.1 ?_)
        calc ‖b - w₀‖ ≤ ‖b - w₁‖ + ‖w₁ - w₀‖ := by
              rw [show b - w₀ = (b - w₁) + (w₁ - w₀) by ring]; exact norm_add_le _ _
          _ ≤ (R - R') + R' := by
              gcongr ?_ + ?_
              · exact hq.2
              · rw [← dist_eq_norm]; exact mem_closedBall.1 hw₁
          _ = R := by ring
      have hfd := stepB_hasFDerivAt (f := g) (z₀ := z00) (w₀ := w₁) (rz := r) (Rz := R)
        (Rw := R - R') (Mf := M) k hr0 hrR (by linarith) hmem hbd
      exact (hfd.const_smul (2 * π * I : ℂ)⁻¹).differentiableAt
    -- `Bₖ` is bounded by `M/r^k` on `closedBall w₀ R'`
    have hBk_bound : ∀ (k : ℕ), ∀ w₁ ∈ closedBall w₀ R', ‖stepB g z00 r k w₁‖ ≤ M / r ^ k := by
      intro k w₁ hw₁
      refine norm_stepB_le hr0 k w₁ fun ζ hζ => ?_
      refine hg_bound (ζ, w₁) (hg_mem ζ w₁ ?_ ?_)
      · rw [← dist_eq_norm]; exact le_of_eq (mem_sphere.1 hζ) |>.trans hrR.le
      · rw [← dist_eq_norm]; exact (mem_closedBall.1 hw₁).trans hR'R.le
    -- apply the induction hypothesis to each `Bₖ`
    have hBk : ∀ k, ∃ d : (Fin n → ℕ) → ℂ, (∀ β, ‖d β‖ ≤ (M / r ^ k) / r ^ (∑ i, β i)) ∧
        ∀ y' : Fin n → ℂ, ‖y'‖ < r →
          HasSum (fun β => d β * ∏ i, y' i ^ β i) (stepB g z00 r k (w₀ + y')) := fun k =>
      IH (stepB g z00 r k) w₀ (hBk_diff k) (hBk_bound k) hr0 hrR'
    choose d hd_bound hd_sum using hBk
    refine ⟨fun α => d (α 0) (Fin.tail α), fun α => ?_, fun y hy => ?_⟩
    · -- coefficient bound `‖c α‖ ≤ M / r^{|α|}`
      have hsplit : (∑ j, α j) = α 0 + ∑ i, Fin.tail α i := by rw [Fin.sum_univ_succ]; rfl
      calc ‖d (α 0) (Fin.tail α)‖ ≤ (M / r ^ (α 0)) / r ^ (∑ i, Fin.tail α i) := hd_bound _ _
        _ = M / r ^ (∑ j, α j) := by rw [hsplit, pow_add]; field_simp
    · -- convergence: peel coordinate 0 by `z`-Cauchy, expand each `Bₖ` by the IH, reassemble
      have hy0r : ‖y 0‖ < r := lt_of_le_of_lt (norm_le_pi_norm y 0) hy
      have hy'r : ‖Fin.tail y‖ < r := lt_of_le_of_lt (norm_tail_le y) hy
      have hz₀y : z₀ + y = Fin.cons (z00 + y 0) (w₀ + Fin.tail y) := by
        funext i
        refine Fin.cases ?_ ?_ i <;>
          simp [Pi.add_apply, hw₀, Fin.tail, Fin.cons_zero, Fin.cons_succ, hz00]
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hb z₀ (mem_closedBall_self hR0.le))
      -- the `z`-Cauchy expansion of the coordinate-0 slice
      have hsliceDiff : ∀ ζ : ℂ, ‖ζ - z00‖ ≤ R →
          DifferentiableAt ℂ (fun ζ' => g (ζ', w₀ + Fin.tail y)) ζ := by
        intro ζ hζ
        have hgζ : DifferentiableAt ℂ g (ζ, w₀ + Fin.tail y) :=
          hg_diff (ζ, w₀ + Fin.tail y) (hg_mem ζ (w₀ + Fin.tail y) hζ
            (by rw [add_sub_cancel_left]; exact hy'r.le.trans hrR.le))
        exact DifferentiableAt.comp (g := g) (f := fun ζ' : ℂ => (ζ', w₀ + Fin.tail y)) ζ hgζ
          (differentiableAt_id.prodMk (differentiableAt_const _))
      have houter : HasSum (fun k => (y 0) ^ k • stepB g z00 r k (w₀ + Fin.tail y)) (f (z₀ + y)) := by
        have hcont : ContinuousOn (fun ζ => g (ζ, w₀ + Fin.tail y)) (closedBall z00 r) := fun ζ hζ =>
          (hsliceDiff ζ (by rw [← dist_eq_norm]; exact (mem_closedBall.1 hζ).trans hrR.le)).continuousAt.continuousWithinAt
        have hdiffz : ∀ ζ ∈ ball z00 r, DifferentiableAt ℂ (fun ζ' => g (ζ', w₀ + Fin.tail y)) ζ :=
          fun ζ hζ => hsliceDiff ζ (by rw [← dist_eq_norm]; exact (mem_ball.1 hζ).le.trans hrR.le)
        have hkey := stepB_hasSum (f := g) (z₀ := z00) (rz := r) hr0 (w₀ + Fin.tail y) hcont hdiffz
          (z := z00 + y 0) (by rw [add_sub_cancel_left]; exact hy0r)
        rw [add_sub_cancel_left] at hkey
        have hval : g (z00 + y 0, w₀ + Fin.tail y) = f (z₀ + y) := by
          show f (Fin.cons (z00 + y 0) (w₀ + Fin.tail y)) = f (z₀ + y); rw [← hz₀y]
        rwa [hval] at hkey
      -- the `ℕ × (Fin n → ℕ)` family is summable
      have ht0 : (0 : ℝ) ≤ ‖y‖ / r := by positivity
      have ht1 : ‖y‖ / r < 1 := (div_lt_one hr0).mpr hy
      have hsummable : Summable (fun p : ℕ × (Fin n → ℕ) =>
          (y 0) ^ p.1 • (d p.1 p.2 * ∏ i, Fin.tail y i ^ p.2 i)) := by
        have hmaj := Summable.mul_of_nonneg
          ((summable_geometric_of_lt_one ht0 ht1).mul_left M)
          (summable_multiIndex_pow n ht0 ht1) (fun _ => mul_nonneg hM0 (by positivity))
          (fun _ => by positivity)
        refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hmaj)
        obtain ⟨k, β⟩ := p
        simp only [norm_smul, norm_pow, norm_mul, norm_prod]
        calc ‖y 0‖ ^ k * (‖d k β‖ * ∏ i, ‖Fin.tail y i‖ ^ β i)
            ≤ ‖y‖ ^ k * ((M / r ^ k / r ^ (∑ i, β i)) * ∏ i, ‖y‖ ^ β i) := by
              gcongr with i
              · exact norm_le_pi_norm y 0
              · exact hd_bound k β
              · exact norm_le_pi_norm y i.succ
          _ = M * (‖y‖ / r) ^ k * (‖y‖ / r) ^ (∑ i, β i) := by
              rw [Finset.prod_pow_eq_pow_sum, div_pow, div_pow]; ring
      -- assemble: regroup the iterated sum and reindex along `Fin.cons`
      have hsigma : HasSum (fun p : ℕ × (Fin n → ℕ) =>
          (y 0) ^ p.1 • (d p.1 p.2 * ∏ i, Fin.tail y i ^ p.2 i)) (f (z₀ + y)) := by
        refine (Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ (Fin n → ℕ))).mp
          (HasSum.sigma_of_hasSum houter (fun k => ?_)
            ((Equiv.summable_iff (Equiv.sigmaEquivProd ℕ (Fin n → ℕ))).mpr hsummable))
        show HasSum (fun β => (y 0) ^ k • (d k β * ∏ i, Fin.tail y i ^ β i))
          ((y 0) ^ k • stepB g z00 r k (w₀ + Fin.tail y))
        exact (hd_sum k (Fin.tail y) hy'r).const_smul ((y 0) ^ k)
      refine hasSum_cons ?_
      have hfe : (fun p : ℕ × (Fin n → ℕ) =>
            (fun α : Fin (n + 1) → ℕ => d (α 0) (Fin.tail α) * ∏ j, y j ^ α j) (Fin.cons p.1 p.2))
          = fun p => (y 0) ^ p.1 • (d p.1 p.2 * ∏ i, Fin.tail y i ^ p.2 i) := by
        funext p
        obtain ⟨k, β⟩ := p
        simp only [Fin.cons_zero, Fin.tail_cons]
        rw [prod_pow_cons, smul_eq_mul]
        simp only [Fin.tail]
        ring
      rw [hfe]; exact hsigma

/-- **Realizability of a multi-index by an assignment.** Every multi-index `α : Fin n → ℕ` is the
"degree profile" of some assignment `assign : Fin (∑ α) → Fin n`: the monomial `∏ⱼ wⱼ^{αⱼ}` is the
product `∏ᵢ w(assign i)`. Proof by induction on `n`, appending `α 0` copies of coordinate `0`. -/
theorem exists_realize : ∀ (n : ℕ) (α : Fin n → ℕ),
    ∃ assign : Fin (∑ j, α j) → Fin n, ∀ w : Fin n → ℂ,
      ∏ i, w (assign i) = ∏ j, w j ^ α j := by
  intro n
  induction n with
  | zero =>
    intro α
    refine ⟨fun i => i.elim0, fun w => ?_⟩
    haveI : IsEmpty (Fin (∑ j : Fin 0, α j)) := by
      rw [show (∑ j : Fin 0, α j) = 0 from rfl]; infer_instance
    rw [Finset.prod_of_isEmpty, Fin.prod_univ_zero]
  | succ n IH =>
    intro α
    obtain ⟨assign', hassign'⟩ := IH (Fin.tail α)
    have hsum : (∑ j, α j) = α 0 + ∑ j, Fin.tail α j := by rw [Fin.sum_univ_succ]; rfl
    refine ⟨fun i => Fin.append (fun _ : Fin (α 0) => (0 : Fin (n + 1)))
        (fun i => (assign' i).succ) (Fin.cast hsum i), fun w => ?_⟩
    rw [Fin.prod_congr' (fun i' => w (Fin.append (fun _ : Fin (α 0) => (0 : Fin (n + 1)))
      (fun i => (assign' i).succ) i')) hsum, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hassign' (fun j => w j.succ),
      Fin.prod_univ_succ]
    rfl

/-- A chosen realizing assignment `Fin N → Fin n` for `α` (when `∑ α = N`; junk otherwise). -/
noncomputable def realizeAssign {n : ℕ} [NeZero n] (N : ℕ) (α : Fin n → ℕ) : Fin N → Fin n :=
  fun i => if h : ∑ j, α j = N then (exists_realize n α).choose (Fin.cast h.symm i) else 0

/-- The monomial product of a realizing assignment: `∏ᵢ w(realizeAssign N α i) = ∏ⱼ wⱼ^{αⱼ}`. -/
theorem realizeAssign_prod {n : ℕ} [NeZero n] {N : ℕ} {α : Fin n → ℕ} (hα : ∑ j, α j = N)
    (w : Fin n → ℂ) : ∏ i, w (realizeAssign N α i) = ∏ j, w j ^ α j := by
  simp only [realizeAssign, dif_pos hα]
  rw [Fin.prod_congr' (fun i => w ((exists_realize n α).choose i)) hα.symm]
  exact (exists_realize n α).choose_spec w

end

