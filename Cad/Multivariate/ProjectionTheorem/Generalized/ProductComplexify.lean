import Cad.Multivariate.ProjectionTheorem.Generalized.OrderCLE
import Cad.Multivariate.ProjectionTheorem.Generalized.Lifting
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassZariskiAxioms

/-!
# Product-form complexification

The complexification machinery (`analyticAt_complexify`, …) is stated over `Fin n → ℝ`/`Fin n → ℂ`,
but the single-cluster pipeline lives on the *product* parameter space
`CParam s e = (Fin s → ℂ) × (Fin e → ℂ)`. This file transports the complexification across the
reindexing equivalence `(Fin (s + e) → 𝕜) ≃L[𝕜] (Fin s → 𝕜) × (Fin e → 𝕜)`, using
`order_comp_continuousLinearEquiv` for the order half.
-/

noncomputable section

open Filter
open scoped Topology

/-- The reindexing continuous linear equivalence
`(Fin (s + e) → 𝕜) ≃L[𝕜] (Fin s → 𝕜) × (Fin e → 𝕜)`. -/
def reindexCLE (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s e : ℕ) :
    (Fin (s + e) → 𝕜) ≃L[𝕜] (Fin s → 𝕜) × (Fin e → 𝕜) :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin (s + e) => 𝕜) finSumFinEquiv).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi 𝕜 (Fin s) (Fin e) (fun _ => 𝕜))

lemma reindexCLE_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s e : ℕ)
    (u : Fin (s + e) → 𝕜) :
    reindexCLE 𝕜 s e u =
      (fun i => u (finSumFinEquiv (Sum.inl i)), fun j => u (finSumFinEquiv (Sum.inr j))) := by
  rfl

/-- `ofReal ∘ 0 = 0` as functions `Fin n → ℂ`. -/
@[simp] lemma ofReal_comp_zero (n : ℕ) :
    (Complex.ofReal ∘ (0 : Fin n → ℝ)) = (0 : Fin n → ℂ) := by
  funext i; simp

/-- The reindexing equivalence commutes with the coordinatewise real embedding. -/
lemma reindexCLE_ofReal (s e : ℕ) (w : Fin (s + e) → ℝ) :
    reindexCLE ℂ s e (Complex.ofReal ∘ w) =
      (Complex.ofReal ∘ (reindexCLE ℝ s e w).1, Complex.ofReal ∘ (reindexCLE ℝ s e w).2) := by
  rw [reindexCLE_apply, reindexCLE_apply]; rfl

/-- **Product-form complexification.** A real-analytic `F` on the product base
`(Fin s → ℝ) × (Fin e → ℝ)` extends to a holomorphic `F_ℂ` on `CParam s e`, agreeing on the real
slice and preserving the vanishing order at `0`. -/
theorem analyticAt_complexify_prod {s e : ℕ}
    (F : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hF : AnalyticAt ℝ F 0) :
    ∃ F_ℂ : CParam s e → ℂ,
      AnalyticAt ℂ F_ℂ 0 ∧
      (∀ᶠ p in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
        F_ℂ (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2) = Complex.ofReal (F p)) ∧
      order ℂ F_ℂ 0 = order ℝ F 0 := by
  set R := reindexCLE ℝ s e with hR
  set Cℂ := reindexCLE ℂ s e with hCℂ
  -- the function pulled back to `Fin (s+e) → ℝ`
  set f : (Fin (s + e) → ℝ) → ℝ := F ∘ R with hf
  have hR0 : R 0 = 0 := map_zero R
  have hf_an : AnalyticAt ℝ f 0 :=
    hF.comp_of_eq (R.toContinuousLinearMap.analyticAt 0) hR0
  obtain ⟨f_ℂ, hf_ℂ_an, hf_ℂ_agree, hf_ℂ_order⟩ := analyticAt_complexify f 0 hf_an
  rw [ofReal_comp_zero] at hf_ℂ_an hf_ℂ_order
  refine ⟨f_ℂ ∘ Cℂ.symm, ?_, ?_, ?_⟩
  · -- analyticity at 0
    have hCsymm0 : Cℂ.symm 0 = 0 := map_zero _
    exact hf_ℂ_an.comp_of_eq (Cℂ.symm.toContinuousLinearMap.analyticAt 0) hCsymm0
  · -- real-slice agreement
    have hpull : ∀ᶠ p in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
        f_ℂ (Complex.ofReal ∘ R.symm p) = Complex.ofReal (f (R.symm p)) := by
      have hcont : Filter.Tendsto R.symm (𝓝 0) (𝓝 0) := by
        simpa using (R.symm.continuous.tendsto (0 : (Fin s → ℝ) × (Fin e → ℝ)))
      exact hcont.eventually hf_ℂ_agree
    filter_upwards [hpull] with p hp
    have hcomm : Cℂ.symm (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2) = Complex.ofReal ∘ R.symm p := by
      have h := reindexCLE_ofReal s e (R.symm p)
      rw [← hR, ← hCℂ, R.apply_symm_apply p] at h
      rw [ContinuousLinearEquiv.symm_apply_eq]
      exact h.symm
    show f_ℂ (Cℂ.symm (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2)) = Complex.ofReal (F p)
    rw [hcomm, hp]
    congr 1
    show f (R.symm p) = F p
    rw [hf]; simp [R.apply_symm_apply p]
  · -- order
    rw [order_comp_continuousLinearEquiv Cℂ.symm f_ℂ 0, map_zero, hf_ℂ_order, hf,
      order_comp_continuousLinearEquiv R F 0, hR0]

/-- **Product-domain L1 (real restriction of the order).** For a holomorphic `F_ℂ` on
`CParam s e × ℂ` whose restriction to the real slice is a given real-analytic `F` on
`((Fin s → ℝ) × (Fin e → ℝ)) × ℝ` (agreeing near `x₀`), the multivariate complex vanishing order at
the embedded real point equals the real order at `x₀` — at a **general** real `x₀`. This is the
product-domain analogue of `order_real_eq_order_complex` (single `Fin`-index), obtained by reindexing
both sides through `Pℝ, Pℂ : Fin (s+e+1) → · ≃L ((Fin s→·)×(Fin e→·))×·` (which commute with the real
embedding) and applying the single-index L1. -/
theorem order_real_eq_order_complex_prod {s e : ℕ}
    (F : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ → ℝ)
    (F_ℂ : CParam s e × ℂ → ℂ)
    (x₀ : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ)
    (hF : AnalyticAt ℝ F x₀)
    (hF_ℂ : AnalyticAt ℂ F_ℂ
      ((Complex.ofReal ∘ x₀.1.1, Complex.ofReal ∘ x₀.1.2), (x₀.2 : ℂ)))
    (hagree : ∀ᶠ x in 𝓝 x₀,
      F_ℂ ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2), (x.2 : ℂ)) = Complex.ofReal (F x)) :
    order ℂ F_ℂ ((Complex.ofReal ∘ x₀.1.1, Complex.ofReal ∘ x₀.1.2), (x₀.2 : ℂ))
      = order ℝ F x₀ := by
  classical
  set Pℝ : (Fin (s + e + 1) → ℝ) ≃L[ℝ] ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ :=
    (reindexCLE ℝ (s + e) 1).trans
      ((reindexCLE ℝ s e).prodCongr (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)) with hPℝ
  set Pℂ : (Fin (s + e + 1) → ℂ) ≃L[ℂ] CParam s e × ℂ :=
    (reindexCLE ℂ (s + e) 1).trans
      ((reindexCLE ℂ s e).prodCongr (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ)) with hPℂ
  set emb : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ → CParam s e × ℂ :=
    fun x => ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2), (x.2 : ℂ)) with hemb
  have hcomm : ∀ u : Fin (s + e + 1) → ℝ, Pℂ (Complex.ofReal ∘ u) = emb (Pℝ u) := by
    intro u
    simp only [hPℝ, hPℂ, hemb, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodCongr_apply, reindexCLE_ofReal,
      ContinuousLinearEquiv.coe_funUnique, Function.eval]
    rfl
  set u₀ : Fin (s + e + 1) → ℝ := Pℝ.symm x₀ with hu₀
  have hPℝu₀ : Pℝ u₀ = x₀ := Pℝ.apply_symm_apply x₀
  have hf_an : AnalyticAt ℝ (F ∘ Pℝ) u₀ :=
    hF.comp_of_eq (Pℝ.toContinuousLinearMap.analyticAt u₀) hPℝu₀
  have hf_ℂ_an : AnalyticAt ℂ (F_ℂ ∘ Pℂ) (Complex.ofReal ∘ u₀) :=
    hF_ℂ.comp_of_eq (Pℂ.toContinuousLinearMap.analyticAt _) (by rw [hcomm u₀, hPℝu₀])
  have hagree' : ∀ᶠ x in 𝓝 u₀,
      (F_ℂ ∘ Pℂ) (Complex.ofReal ∘ x) = Complex.ofReal ((F ∘ Pℝ) x) := by
    have htend : Filter.Tendsto Pℝ (𝓝 u₀) (𝓝 x₀) := by
      have := Pℝ.continuous.tendsto u₀; rwa [hPℝu₀] at this
    filter_upwards [htend.eventually hagree] with x hx
    show F_ℂ (Pℂ (Complex.ofReal ∘ x)) = Complex.ofReal (F (Pℝ x))
    rw [hcomm x]; exact hx
  have hLHS : order ℂ F_ℂ (emb x₀) = order ℂ (F_ℂ ∘ Pℂ) (Complex.ofReal ∘ u₀) := by
    rw [order_comp_continuousLinearEquiv Pℂ F_ℂ (Complex.ofReal ∘ u₀), hcomm u₀, hPℝu₀]
  have hRHS : order ℝ F x₀ = order ℝ (F ∘ Pℝ) u₀ := by
    rw [order_comp_continuousLinearEquiv Pℝ F u₀, hPℝu₀]
  rw [hLHS, hRHS]
  exact order_real_eq_order_complex (F ∘ Pℝ) (F_ℂ ∘ Pℂ) u₀ hf_an hf_ℂ_an hagree'

/-- **Product-form complexification of a pseudopolynomial family.** A real polynomial family on the
product base, with analytic coefficients and degree `≤ N`, complexifies to a family on `CParam s e`
with analytic coefficients agreeing on the real slice. -/
theorem complexify_pseudopoly_prod {s e : ℕ} (N : ℕ)
    (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hdeg : ∀ w, (g w).natDegree ≤ N)
    (hcoeff_an : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0) :
    ∃ gℂ : CParam s e → Polynomial ℂ,
      (∀ i, AnalyticAt ℂ (fun z => (gℂ z).coeff i) 0) ∧
      (∀ i, ∀ᶠ p in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
        (gℂ (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2)).coeff i
          = Complex.ofReal ((g p).coeff i)) := by
  have hex : ∀ i, ∃ cℂ : CParam s e → ℂ,
      AnalyticAt ℂ cℂ 0 ∧
      (∀ᶠ p in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
        cℂ (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2) = Complex.ofReal ((g p).coeff i)) :=
    fun i => by
      obtain ⟨cℂ, han, hagree, _⟩ :=
        analyticAt_complexify_prod (fun w => (g w).coeff i) (hcoeff_an i)
      exact ⟨cℂ, han, hagree⟩
  choose cℂ hcℂ_an hcℂ_agree using hex
  have hco : ∀ (z : CParam s e) (j : ℕ),
      (∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (cℂ i z)).coeff j
        = if j ≤ N then cℂ j z else 0 := by
    intro z j
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (N + 1)) j (fun i => cℂ i z)]
    simp [Finset.mem_range, Nat.lt_succ_iff]
  refine ⟨fun z => ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (cℂ i z), ?_, ?_⟩
  · intro j
    refine (?_ : AnalyticAt ℂ (fun z => if j ≤ N then cℂ j z else 0) 0).congr
      (.of_forall fun z => (hco z j).symm)
    by_cases hj : j ≤ N
    · simpa only [hj, if_true] using hcℂ_an j
    · simpa only [hj, if_false] using analyticAt_const
  · intro j
    filter_upwards [hcℂ_agree j] with p hp
    rw [hco (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2) j]
    by_cases hj : j ≤ N
    · rw [if_pos hj, hp]
    · rw [if_neg hj, Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdeg p) (not_le.mp hj)), Complex.ofReal_zero]

end
