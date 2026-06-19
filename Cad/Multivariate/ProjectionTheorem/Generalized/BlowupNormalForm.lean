import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticDivCoord
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# M5b — the blow-up discriminant normal form (validation of the iterated-division engine)

The thesis Case II blow-up `Q̃` reduces `disc(H∘Q̃) = F∘Q̃` to the codimension-one normal form
`F∘Q̃ = (z 0)^r · N` with `N(0) ≠ 0` (here `z 0` is the distinguished blow-up coordinate `u`).
The order-invariance of `F` on the section forces the low-order `z 0`-jets of `F∘Q̃` to vanish on
`{z 0 = 0}`; this file builds the **iterated-division engine** turning that jet-vanishing into the
factorization, by applying `AnalyticDivCoord.analytic_div_coord0` repeatedly.

The coordinate partial `pderiv0 G z = fderiv ℂ G z (e0 n)` and the Leibniz identity
`pderiv0 (z 0 · N) = N + z 0 · pderiv0 N` drive a clean induction on the division exponent.
-/

noncomputable section

open Filter
open scoped Topology

namespace BlowupNormalForm

variable {n : ℕ}

/-- The coordinate-`0` basis vector in `Fin (n+1) → ℂ`. -/
def e0 (n : ℕ) : Fin (n + 1) → ℂ := Pi.single 0 1

/-- The partial derivative of `G` in the coordinate-`0` direction. -/
def pderiv0 (G : (Fin (n + 1) → ℂ) → ℂ) (z : Fin (n + 1) → ℂ) : ℂ :=
  fderiv ℂ G z (e0 n)

/-- `pderiv0` preserves analyticity: it is the composition of `fderiv ℂ G` (analytic, valued in the
continuous-linear-map space) with evaluation at the fixed vector `e0 n` (a CLM). -/
theorem pderiv0_analyticAt {G : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (hG : AnalyticAt ℂ G x₀) : AnalyticAt ℂ (pderiv0 G) x₀ := by
  have hev := (ContinuousLinearMap.apply ℂ ℂ (e0 n)).analyticAt
    (fderiv ℂ G x₀)
  exact hev.comp hG.fderiv

/-- **Single Leibniz step.** Near a point where `N` is analytic,
`pderiv0 (fun z => z 0 * N z) = fun z => N z + z 0 * pderiv0 N z`. -/
theorem pderiv0_coord0_mul {N : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (hN : AnalyticAt ℂ N x₀) :
    ∀ᶠ z in 𝓝 x₀, pderiv0 (fun z => z 0 * N z) z = N z + z 0 * pderiv0 N z := by
  filter_upwards [hN.eventually_analyticAt] with z hNz
  have hproj : HasFDerivAt (fun z : Fin (n + 1) → ℂ => z 0)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).hasFDerivAt
  have hNd : HasFDerivAt N (fderiv ℂ N z) z := hNz.differentiableAt.hasFDerivAt
  have hmul := hproj.mul hNd
  show fderiv ℂ (fun z => z 0 * N z) z (e0 n) = N z + z 0 * pderiv0 N z
  rw [show (fun z : Fin (n + 1) → ℂ => z 0 * N z) = (fun z => z 0) * N from rfl, hmul.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, e0, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [add_comm]; rfl

/-- `pderiv0` respects local equality of germs. -/
theorem pderiv0_congr {G H : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (h : G =ᶠ[𝓝 x₀] H) : pderiv0 G =ᶠ[𝓝 x₀] pderiv0 H := by
  filter_upwards [h.eventually_nhds] with z hz
  have hz' : G =ᶠ[𝓝 z] H := hz
  unfold pderiv0; rw [hz'.fderiv_eq]

/-- Iterated `pderiv0` respects local equality of germs. -/
theorem pderiv0_iterate_congr {G H : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (i : ℕ) (h : G =ᶠ[𝓝 x₀] H) : (pderiv0)^[i] G =ᶠ[𝓝 x₀] (pderiv0)^[i] H := by
  induction i with
  | zero => simpa using h
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact pderiv0_congr ih

/-- Iterated `pderiv0` preserves analyticity. -/
theorem pderiv0_iterate_analyticAt {G : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (i : ℕ) (hG : AnalyticAt ℂ G x₀) : AnalyticAt ℂ ((pderiv0)^[i] G) x₀ := by
  induction i with
  | zero => simpa using hG
  | succ k ih => simp only [Function.iterate_succ_apply']; exact pderiv0_analyticAt ih

/-- `pderiv0` is additive on analytic germs. -/
theorem pderiv0_add {f g : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (hf : AnalyticAt ℂ f x₀) (hg : AnalyticAt ℂ g x₀) :
    ∀ᶠ z in 𝓝 x₀, pderiv0 (fun z => f z + g z) z = pderiv0 f z + pderiv0 g z := by
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
  unfold pderiv0
  have hadd : HasFDerivAt (fun z => f z + g z) (fderiv ℂ f z + fderiv ℂ g z) z :=
    hfz.differentiableAt.hasFDerivAt.add hgz.differentiableAt.hasFDerivAt
  rw [hadd.fderiv, ContinuousLinearMap.add_apply]

/-- `pderiv0` commutes with multiplication by a constant. -/
theorem pderiv0_const_mul (c : ℂ) {f : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (hf : AnalyticAt ℂ f x₀) :
    ∀ᶠ z in 𝓝 x₀, pderiv0 (fun z => c * f z) z = c * pderiv0 f z := by
  filter_upwards [hf.eventually_analyticAt] with z hfz
  unfold pderiv0
  have hcm : HasFDerivAt (fun z => c * f z) (c • fderiv ℂ f z) z :=
    hfz.differentiableAt.hasFDerivAt.const_mul c
  rw [hcm.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **Iterated Leibniz for the coordinate factor.** Near `x₀`,
`pderiv0^[i+1] (z 0 · N) = z 0 · pderiv0^[i+1] N + (i+1) · pderiv0^[i] N`. -/
theorem pderiv0_iterate_coord0_mul {N : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (hN : AnalyticAt ℂ N x₀) (i : ℕ) :
    ∀ᶠ z in 𝓝 x₀, (pderiv0)^[i + 1] (fun z => z 0 * N z) z
      = z 0 * (pderiv0)^[i + 1] N z + (i + 1 : ℂ) * (pderiv0)^[i] N z := by
  induction i with
  | zero =>
    filter_upwards [pderiv0_coord0_mul hN] with z hz
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq]
    rw [hz]; push_cast; ring
  | succ k ih =>
    -- `pderiv0^[k+2](z0 N) = pderiv0 (pderiv0^[k+1](z0 N))`
    have hNk1 : AnalyticAt ℂ ((pderiv0)^[k + 1] N) x₀ := pderiv0_iterate_analyticAt _ hN
    have hNk : AnalyticAt ℂ ((pderiv0)^[k] N) x₀ := pderiv0_iterate_analyticAt _ hN
    -- differentiate the IH identity
    have hstep := pderiv0_congr (x₀ := x₀) ih
    have hsum : ∀ᶠ z in 𝓝 x₀,
        pderiv0 (fun z => z 0 * (pderiv0)^[k + 1] N z + (k + 1 : ℂ) * (pderiv0)^[k] N z) z
          = ((pderiv0)^[k + 1] N z + z 0 * (pderiv0)^[k + 2] N z)
            + (k + 1 : ℂ) * (pderiv0)^[k + 1] N z := by
      have hproj_an : AnalyticAt ℂ (fun z : Fin (n + 1) → ℂ => z 0) x₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt x₀
      have hA : AnalyticAt ℂ (fun z => z 0 * (pderiv0)^[k + 1] N z) x₀ :=
        hproj_an.mul hNk1
      have hB : AnalyticAt ℂ (fun z => (k + 1 : ℂ) * (pderiv0)^[k] N z) x₀ :=
        analyticAt_const.mul hNk
      filter_upwards [pderiv0_add hA hB, pderiv0_coord0_mul hNk1,
        pderiv0_const_mul (k + 1 : ℂ) hNk] with z hadd hmul hcst
      rw [hadd, hmul, hcst]
      congr 1
      · simp only [Function.iterate_succ_apply']
      · simp only [Function.iterate_succ_apply']
    filter_upwards [hstep, hsum] with z hz hsumz
    rw [Function.iterate_succ_apply' (n := k + 1), hz, hsumz]
    push_cast
    ring

/-- `pderiv0` as a slice (line) derivative at a point of differentiability. -/
theorem pderiv0_eq_deriv_slice {G : (Fin (n + 1) → ℂ) → ℂ} {z : Fin (n + 1) → ℂ}
    (hG : DifferentiableAt ℂ G z) :
    pderiv0 G z = deriv (fun t : ℂ => G (z + t • e0 n)) 0 := by
  have hl : HasDerivAt (fun t : ℂ => G (z + t • e0 n))
      (fderiv ℂ G z (e0 n)) 0 := HasFDerivAt.hasLineDerivAt hG.hasFDerivAt (e0 n)
  exact hl.deriv.symm

/-- **The coordinate-`0` partial as a directional derivative along a line.** For `G` analytic at `z₀`,
the `j`-fold coordinate-`0` partial equals the `j`-th derivative of the `z 0`-slice. This is the bridge
turning the order-vanishing of `g` into the `div_coord0_pow` jet hypothesis. -/
theorem pderiv0_iterate_eq_iteratedDeriv {G : (Fin (n + 1) → ℂ) → ℂ} {z₀ : Fin (n + 1) → ℂ}
    (hG : AnalyticAt ℂ G z₀) (j : ℕ) :
    ∀ᶠ z in 𝓝 z₀, (pderiv0)^[j] G z
      = iteratedDeriv j (fun t : ℂ => G (z + t • e0 n)) 0 := by
  induction j with
  | zero =>
    filter_upwards with z
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero, zero_smul, add_zero]
  | succ j ih =>
    filter_upwards [hG.eventually_analyticAt, ih.eventually_nhds] with z hGz hih_nhds
    -- the `t`-slice of `pderiv0^[j] G` agrees with `iteratedDeriv j` of the `z`-slice near `0`
    have hslice : (fun t : ℂ => (pderiv0)^[j] G (z + t • e0 n))
        =ᶠ[𝓝 0] fun t => iteratedDeriv j (fun s : ℂ => G (z + s • e0 n)) t := by
      have hcont : Filter.Tendsto
          (fun t : ℂ => z + t • e0 n) (𝓝 0) (𝓝 z) := by
        have hc : Continuous (fun t : ℂ => z + t • e0 n) := by
          fun_prop
        have h0 : z + (0 : ℂ) • e0 n = z := by simp
        simpa [h0] using hc.tendsto 0
      filter_upwards [hcont.eventually hih_nhds] with t ht
      rw [ht]
      have hfun : (fun s : ℂ => G (z + t • e0 n + s • e0 n))
          = fun s : ℂ => (fun u : ℂ => G (z + u • e0 n)) (t + s) := by
        funext s; simp only [add_smul, add_assoc]
      rw [hfun, iteratedDeriv_comp_const_add j (fun u : ℂ => G (z + u • e0 n)) t]
      simp
    rw [Function.iterate_succ_apply',
      pderiv0_eq_deriv_slice (pderiv0_iterate_analyticAt j hGz).differentiableAt,
      hslice.deriv_eq, ← iteratedDeriv_succ]

/-- **Iterated division by the coordinate `z 0`.** If `G` is analytic at `x₀` (with `x₀ 0 = 0`) and
its first `r` coordinate-`0` jets vanish on the hyperplane `{z 0 = 0}` near `x₀`, then `G` factors as
`(z 0)^r · N` with `N` analytic at `x₀`. This is the engine of the discriminant normal form. -/
theorem div_coord0_pow (r : ℕ) {G : (Fin (n + 1) → ℂ) → ℂ} {x₀ : Fin (n + 1) → ℂ}
    (hx0 : x₀ 0 = 0) (hG : AnalyticAt ℂ G x₀)
    (hjet : ∀ j < r, ∀ᶠ z in 𝓝 x₀, z 0 = 0 → (pderiv0)^[j] G z = 0) :
    ∃ N : (Fin (n + 1) → ℂ) → ℂ, AnalyticAt ℂ N x₀ ∧ ∀ᶠ z in 𝓝 x₀, G z = (z 0) ^ r * N z := by
  induction r generalizing G with
  | zero =>
    refine ⟨G, hG, ?_⟩
    filter_upwards with z; rw [pow_zero, one_mul]
  | succ r ih =>
    -- the `j = 0` jet: `G` vanishes on `{z 0 = 0}` near `x₀`
    have h0 : ∀ᶠ z in 𝓝 x₀, z 0 = 0 → G z = 0 := by
      have := hjet 0 (by omega)
      simpa using this
    obtain ⟨N₁, hN₁an, hN₁eq⟩ := AnalyticDivCoord.analytic_div_coord0 hx0 hG h0
    have hGeq : G =ᶠ[𝓝 x₀] fun z => z 0 * N₁ z := hN₁eq
    -- the quotient `N₁` has its first `r` jets vanishing on `{z 0 = 0}`
    have hjet₁ : ∀ j < r, ∀ᶠ z in 𝓝 x₀, z 0 = 0 → (pderiv0)^[j] N₁ z = 0 := by
      intro j hj
      have hcong := pderiv0_iterate_congr (j + 1) hGeq
      have hleib := pderiv0_iterate_coord0_mul hN₁an j
      have hjetj := hjet (j + 1) (by omega)
      filter_upwards [hcong, hleib, hjetj] with z hcz hlz hjz
      intro hz0
      have hval : (pderiv0)^[j + 1] G z = (j + 1 : ℂ) * (pderiv0)^[j] N₁ z := by
        rw [hcz, hlz, hz0]; ring
      have hzero : (pderiv0)^[j + 1] G z = 0 := hjz hz0
      rw [hval] at hzero
      have hne : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      exact (mul_eq_zero.mp hzero).resolve_left hne
    obtain ⟨N, hNan, hNeq⟩ := ih hN₁an hjet₁
    refine ⟨N, hNan, ?_⟩
    filter_upwards [hN₁eq, hNeq] with z h1 h2
    rw [h1, h2]; ring

/-! ### Directional derivative along a line equals the iterated Fréchet derivative on the diagonal

This is the bridge used to feed `div_coord0_pow`: on `{u = 0}`, the `u`-slice of `g ∘ Q̃` is a straight
line in a transverse direction, so its `iteratedDeriv` is the directional iterated Fréchet derivative
of `g`, which vanishes below the order. We prove it for a general space `E` and direction `v`. -/

section LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Repeated directional `fderiv` in direction `v`. -/
private def slope (v : E) (G : E → ℂ) (z : E) : ℂ := fderiv ℂ G z v

private theorem slope_analyticAt (v : E) {G : E → ℂ} {x₀ : E}
    (hG : AnalyticAt ℂ G x₀) : AnalyticAt ℂ (slope v G) x₀ :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ G x₀)).comp hG.fderiv

private theorem slope_iterate_analyticAt (v : E) (i : ℕ) {G : E → ℂ} {x₀ : E}
    (hG : AnalyticAt ℂ G x₀) : AnalyticAt ℂ ((slope v)^[i] G) x₀ := by
  induction i with
  | zero => simpa using hG
  | succ k ih => simp only [Function.iterate_succ_apply']; exact slope_analyticAt v ih

private theorem slope_eq_deriv_slice (v : E) {G : E → ℂ} {z : E}
    (hG : DifferentiableAt ℂ G z) :
    slope v G z = deriv (fun t : ℂ => G (z + t • v)) 0 :=
  (HasFDerivAt.hasLineDerivAt hG.hasFDerivAt v).deriv.symm

/-- The directional iterate equals the line `iteratedDeriv` (general direction). -/
private theorem slope_iterate_eq_iteratedDeriv (v : E) {G : E → ℂ} {z₀ : E}
    (hG : AnalyticAt ℂ G z₀) (j : ℕ) :
    ∀ᶠ z in 𝓝 z₀, (slope v)^[j] G z = iteratedDeriv j (fun t : ℂ => G (z + t • v)) 0 := by
  induction j with
  | zero =>
    filter_upwards with z
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero, zero_smul, add_zero]
  | succ j ih =>
    filter_upwards [hG.eventually_analyticAt, ih.eventually_nhds] with z hGz hih_nhds
    have hslice : (fun t : ℂ => (slope v)^[j] G (z + t • v))
        =ᶠ[𝓝 0] fun t => iteratedDeriv j (fun s : ℂ => G (z + s • v)) t := by
      have hcont : Filter.Tendsto (fun t : ℂ => z + t • v) (𝓝 0) (𝓝 z) := by
        have hc : Continuous (fun t : ℂ => z + t • v) := by fun_prop
        have h0 : z + (0 : ℂ) • v = z := by simp
        simpa [h0] using hc.tendsto 0
      filter_upwards [hcont.eventually hih_nhds] with t ht
      rw [ht]
      have hfun : (fun s : ℂ => G (z + t • v + s • v))
          = fun s : ℂ => (fun u : ℂ => G (z + u • v)) (t + s) := by
        funext s; simp only [add_smul, add_assoc]
      rw [hfun, iteratedDeriv_comp_const_add j (fun u : ℂ => G (z + u • v)) t]
      simp
    rw [Function.iterate_succ_apply',
      slope_eq_deriv_slice v (slope_iterate_analyticAt v j hGz).differentiableAt,
      hslice.deriv_eq, ← iteratedDeriv_succ]

/-- The directional iterate equals the iterated Fréchet derivative on the constant tuple. -/
private theorem slope_iterate_eq_iteratedFDeriv (v : E) {G : E → ℂ} {z₀ : E}
    (hG : AnalyticAt ℂ G z₀) (j : ℕ) :
    ∀ᶠ z in 𝓝 z₀, (slope v)^[j] G z = iteratedFDeriv ℂ j G z (fun _ : Fin j => v) := by
  induction j with
  | zero =>
    filter_upwards with z
    simp only [Function.iterate_zero, id_eq, iteratedFDeriv_zero_apply]
  | succ j ih =>
    filter_upwards [hG.eventually_analyticAt, ih.eventually_nhds] with z hGz hih_nhds
    set L := ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => E) ℂ (fun _ : Fin j => v) with hL
    have hcd : ContDiffAt ℂ 1 (iteratedFDeriv ℂ j G) z :=
      (hGz.contDiffAt).iteratedFDeriv_right (by exact_mod_cast le_top)
    have hh : HasFDerivAt (iteratedFDeriv ℂ j G) (fderiv ℂ (iteratedFDeriv ℂ j G) z) z :=
      (hcd.differentiableAt one_ne_zero).hasFDerivAt
    have hLh : HasFDerivAt (fun w => L (iteratedFDeriv ℂ j G w))
        (L.comp (fderiv ℂ (iteratedFDeriv ℂ j G) z)) z := L.hasFDerivAt.comp z hh
    have hgerm : (slope v)^[j] G =ᶠ[𝓝 z] fun w => L (iteratedFDeriv ℂ j G w) := hih_nhds
    rw [Function.iterate_succ_apply']
    show fderiv ℂ ((slope v)^[j] G) z v = _
    rw [hgerm.fderiv_eq, hLh.fderiv]
    rw [iteratedFDeriv_succ_apply_left]
    simp only [ContinuousLinearMap.comp_apply, hL, ContinuousMultilinearMap.apply_apply,
      Fin.tail_def]

/-- **Line directional derivative = iterated Fréchet derivative on the diagonal.** For `g` analytic at
`x`, the `j`-th derivative of the line `t ↦ g (x + t • v)` at `0` equals `iteratedFDeriv ℂ j g x` on the
constant tuple `(v, …, v)`. In particular it vanishes whenever `iteratedFDeriv ℂ j g x = 0`. -/
theorem iteratedDeriv_line_eq (v : E) {g : E → ℂ} {x : E} (hg : AnalyticAt ℂ g x) (j : ℕ) :
    iteratedDeriv j (fun t : ℂ => g (x + t • v)) 0 = iteratedFDeriv ℂ j g x (fun _ : Fin j => v) :=
  (slope_iterate_eq_iteratedDeriv v hg j).self_of_nhds.symm.trans
    (slope_iterate_eq_iteratedFDeriv v hg j).self_of_nhds

end LineDeriv

/-- `iteratedDeriv r (t ↦ tʳ · φ t) 0 = r! · φ 0`: only the term differentiating `tʳ` exactly `r` times
survives at `0`. -/
theorem iteratedDeriv_pow_mul (r : ℕ) {φ : ℂ → ℂ} (hφ : ContDiffAt ℂ (⊤ : WithTop ℕ∞) φ 0) :
    iteratedDeriv r (fun t : ℂ => t ^ r * φ t) 0 = (r.factorial : ℂ) * φ 0 := by
  have hpow : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun t : ℂ => t ^ r) 0 := by
    exact (contDiffAt_id.pow r)
  rw [show (fun t : ℂ => t ^ r * φ t) = (fun t : ℂ => t ^ r) * φ from rfl,
    iteratedDeriv_mul (hpow.of_le le_top) (hφ.of_le le_top)]
  rw [Finset.sum_eq_single r]
  · rw [iteratedDeriv_fun_pow_zero, if_pos rfl, Nat.sub_self, iteratedDeriv_zero,
      Nat.choose_self]
    push_cast; ring
  · intro i _ hir
    rw [iteratedDeriv_fun_pow_zero, if_neg hir, Nat.cast_zero, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self r)) h

/-- The leading coefficient of the normal form: `pderiv0^[r] ((z 0)ʳ · N) 0 = r! · N 0`. -/
theorem pderiv0_iterate_pow_mul_eval {N : (Fin (n + 1) → ℂ) → ℂ}
    (hN : AnalyticAt ℂ N 0) (r : ℕ) :
    (pderiv0)^[r] (fun z => (z 0) ^ r * N z) 0 = (r.factorial : ℂ) * N 0 := by
  have hcoord : AnalyticAt ℂ (fun z : Fin (n + 1) → ℂ => z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt 0
  have hGan : AnalyticAt ℂ (fun z => (z 0) ^ r * N z) 0 := (hcoord.pow r).mul hN
  have hline : AnalyticAt ℂ (fun t : ℂ => t • e0 n) 0 :=
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (e0 n)).analyticAt 0
  have hline0 : (fun t : ℂ => t • e0 n) 0 = 0 := by simp
  rw [(pderiv0_iterate_eq_iteratedDeriv hGan r).self_of_nhds]
  have hslice : (fun t : ℂ => ((0 : Fin (n + 1) → ℂ) + t • e0 n) 0 ^ r * N (0 + t • e0 n))
      = fun t : ℂ => t ^ r * N (t • e0 n) := by
    funext t
    simp only [zero_add]
    congr 2
    simp [e0]
  rw [hslice, iteratedDeriv_pow_mul (φ := fun t => N (t • e0 n)) r
    (hN.comp_of_eq hline hline0).contDiffAt]
  simp

end BlowupNormalForm
