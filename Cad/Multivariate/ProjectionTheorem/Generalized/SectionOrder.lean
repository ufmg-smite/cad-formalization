import Cad.Multivariate.ProjectionTheorem.Generalized.ProductComplexify

/-!
# Section-order complexification

`complexify_section_order_invariant`: if the real witness `P` has constant vanishing order `μ`
**along the section** `{(y,0)}` near `0`, then its complexification `Pℂ` has constant order `μ`
along the complex section near `0`. This is the complex hypothesis `hP_oi` that
`single_cluster_complex` (and `DiscOrder`) consume.

The proof mirrors `complexify_order_invariant`, but the identity theorem is applied in the
**section variable** `y` (where `ℝˢ ⊂ ℂˢ` is a maximal-real uniqueness set), seeded by the vanishing
of the full complex derivative at *real* section points — itself lifted from the real derivative
vanishing via a CParam-basis argument transported through `reindexCLE`.
-/

noncomputable section

open Filter Set
open scoped Topology

variable {s e : ℕ}

/-- The coordinatewise real embedding of the product base into `CParam s e`. -/
def prodEmbedCLM (s e : ℕ) : ((Fin s → ℝ) × (Fin e → ℝ)) →L[ℝ] CParam s e :=
  (realEmbedding s).prodMap (realEmbedding e)

@[simp] lemma prodEmbedCLM_apply (p : (Fin s → ℝ) × (Fin e → ℝ)) :
    prodEmbedCLM s e p = (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2) := by
  simp [prodEmbedCLM, ContinuousLinearMap.coe_prodMap', Prod.map, realEmbedding_apply]

/-- **Identity theorem on `CParam`.** An analytic function on `CParam s e` vanishing on the real
slice near `0` vanishes near `0`. Transported from `order_eq_top_of_real_eq_zero` via `reindexCLE`. -/
lemma eventuallyEq_zero_of_real_eq_zero_prod (h : CParam s e → ℂ) (hh : AnalyticAt ℂ h 0)
    (hreal : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)), h (prodEmbedCLM s e w) = 0) :
    h =ᶠ[𝓝 0] 0 := by
  set C := reindexCLE ℂ s e with hC
  have hh' : AnalyticAt ℂ (h ∘ C) 0 :=
    hh.comp_of_eq (C.toContinuousLinearMap.analyticAt 0) (map_zero C)
  have hgz : ∀ᶠ v in 𝓝 (0 : Fin (s + e) → ℝ), (h ∘ C) (Complex.ofReal ∘ v) = 0 := by
    have hcont : Filter.Tendsto (reindexCLE ℝ s e) (𝓝 0) (𝓝 0) := by
      simpa using ((reindexCLE ℝ s e).continuous.tendsto 0)
    filter_upwards [hcont.eventually hreal] with v hv
    show h (C (Complex.ofReal ∘ v)) = 0
    rw [hC, reindexCLE_ofReal, ← prodEmbedCLM_apply]
    exact hv
  have hbase : (Complex.ofReal ∘ (0 : Fin (s + e) → ℝ)) = (0 : Fin (s + e) → ℂ) := by ext; simp
  have hord : order ℂ (h ∘ C) 0 = ⊤ := by
    have hord0 := order_eq_top_of_real_eq_zero (h ∘ C) 0 (by rw [hbase]; exact hh') hgz
    rwa [hbase] at hord0
  have hzero' : (h ∘ C) =ᶠ[𝓝 0] 0 := eventuallyEq_zero_of_order_eq_top (h ∘ C) 0 hh' hord
  have hcont' : Filter.Tendsto C.symm (𝓝 0) (𝓝 0) := by
    simpa using (C.symm.continuous.tendsto 0)
  filter_upwards [hcont'.eventually hzero'] with z hz
  show h z = 0
  have h2 : (h ∘ C) (C.symm z) = 0 := hz
  rwa [Function.comp_apply, C.apply_symm_apply] at h2

/-- A ℂ-multilinear map on `CParam s e` that vanishes on every tuple of *real* inputs
(image of `prodEmbedCLM`) is zero. Transported from `cml_eq_zero_of_basis_eq_zero` via the
reindexing equivalence `reindexCLE`. -/
lemma cml_eq_zero_of_real_inputs {k : ℕ}
    (g : ContinuousMultilinearMap ℂ (fun _ : Fin k => CParam s e) ℂ)
    (h : ∀ w : Fin k → (Fin s → ℝ) × (Fin e → ℝ),
      g (fun i => prodEmbedCLM s e (w i)) = 0) : g = 0 := by
  set C := reindexCLE ℂ s e with hC
  -- transport `g` to a CMM on `Fin (s+e) → ℂ`
  set g' : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin (s + e) → ℂ) ℂ :=
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℂ (fun _ : Fin k => C) g with hg'
  have hg'_zero : g' = 0 := by
    apply cml_eq_zero_of_basis_eq_zero
    intro v
    show g (fun i => C (Pi.single (v i) (1 : ℂ))) = 0
    have hbasis : ∀ i, C (Pi.single (v i) (1 : ℂ))
        = prodEmbedCLM s e (reindexCLE ℝ s e (Pi.single (v i) (1 : ℝ))) := by
      intro i
      have hofReal : (Pi.single (v i) (1 : ℂ)) = Complex.ofReal ∘ (Pi.single (v i) (1 : ℝ)) := by
        funext l; simp [Pi.single_apply, apply_ite Complex.ofReal]
      rw [hofReal, hC, reindexCLE_ofReal, prodEmbedCLM_apply]
    simp_rw [hbasis]
    exact h _
  have : g = ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℂ (fun _ : Fin k => C.symm) g' := by
    rw [hg']
    rw [← ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_symm]
    exact (ContinuousLinearEquiv.symm_apply_apply _ g).symm
  rw [this, hg'_zero, map_zero]

/-- A ℂ-multilinear map on `CParam s e` vanishing on every tuple of standard basis vectors
(transported through `reindexCLE`) is zero. Finitely-indexed version of
`cml_eq_zero_of_real_inputs`, suitable for finite intersections. -/
lemma cml_eq_zero_of_reindex_basis {k : ℕ}
    (g : ContinuousMultilinearMap ℂ (fun _ : Fin k => CParam s e) ℂ)
    (h : ∀ v : Fin k → Fin (s + e),
      g (fun i => reindexCLE ℂ s e (Pi.single (v i) (1 : ℂ))) = 0) : g = 0 := by
  set C := reindexCLE ℂ s e with hC
  set g' : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin (s + e) → ℂ) ℂ :=
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℂ (fun _ : Fin k => C) g with hg'
  have hg'_zero : g' = 0 := by
    apply cml_eq_zero_of_basis_eq_zero
    intro v
    show g (fun i => C (Pi.single (v i) (1 : ℂ))) = 0
    exact h v
  have : g = ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℂ (fun _ : Fin k => C.symm) g' := by
    rw [hg', ← ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_symm]
    exact (ContinuousLinearEquiv.symm_apply_apply _ g).symm
  rw [this, hg'_zero, map_zero]

/-- **Seed: the full complex derivative vanishes at real section points.** If `Pℂ` agrees with
`ofReal ∘ P` on the real slice near `q` and the real derivative `iteratedFDeriv ℝ j P q` vanishes,
then the complex derivative `iteratedFDeriv ℂ j Pℂ (prodEmbedCLM q)` vanishes. -/
lemma cderiv_zero_at_real_point {j : ℕ}
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (Pℂ : CParam s e → ℂ)
    (U : Set (CParam s e)) (hU : IsOpen U) (hPℂ_an : AnalyticOnNhd ℂ Pℂ U)
    (q : (Fin s → ℝ) × (Fin e → ℝ)) (hqU : prodEmbedCLM s e q ∈ U)
    (hP_cd : ContDiffAt ℝ j P q)
    (hagree : (fun p => Pℂ (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2)) =ᶠ[𝓝 q]
      fun p => Complex.ofReal (P p))
    (hreal : iteratedFDeriv ℝ j P q = 0) :
    iteratedFDeriv ℂ j Pℂ (prodEmbedCLM s e q) = 0 := by
  set zq := prodEmbedCLM s e q with hzq
  have hPℂ_cdOnR : ContDiffOn ℝ (⊤ : ℕ∞) Pℂ U :=
    (hPℂ_an.contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hVopen : IsOpen (prodEmbedCLM s e ⁻¹' U) := hU.preimage (prodEmbedCLM s e).continuous
  -- chain rule for `Pℂ ∘ prodEmbedCLM`, on the open set `U`
  have hchainW := (prodEmbedCLM s e).iteratedFDerivWithin_comp_right (i := j) hPℂ_cdOnR
    hU.uniqueDiffOn hVopen.uniqueDiffOn hqU (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen j hVopen hqU,
    iteratedFDerivWithin_of_isOpen j hU hqU] at hchainW
  have hchain : iteratedFDeriv ℝ j (Pℂ ∘ prodEmbedCLM s e) q =
      (iteratedFDeriv ℝ j Pℂ zq).compContinuousLinearMap (fun _ => prodEmbedCLM s e) := hchainW
  -- agreement transports the real derivative
  have hagree_deriv : iteratedFDeriv ℝ j (Pℂ ∘ prodEmbedCLM s e) q =
      iteratedFDeriv ℝ j (fun p => Complex.ofReal (P p)) q := by
    have : (Pℂ ∘ prodEmbedCLM s e) =ᶠ[𝓝 q] fun p => Complex.ofReal (P p) := by
      filter_upwards [hagree] with p hp
      simpa [Function.comp, prodEmbedCLM_apply] using hp
    exact (this.iteratedFDeriv ℝ j).self_of_nhds
  -- `ofReal ∘ P` derivative is `ofReal ∘ (real derivative) = 0`
  have hofReal_deriv : iteratedFDeriv ℝ j (fun p => Complex.ofReal (P p)) q = 0 := by
    have h : iteratedFDeriv ℝ j (fun p => Complex.ofReal (P p)) q
        = Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j P q) :=
      Complex.ofRealCLM.iteratedFDeriv_comp_left hP_cd le_rfl
    rw [h, hreal]; ext v; simp
  -- combine: the composed-with-prodEmbed multilinear map is zero
  have hcomp_zero : (iteratedFDeriv ℝ j Pℂ zq).compContinuousLinearMap (fun _ => prodEmbedCLM s e) = 0 := by
    rw [← hchain, hagree_deriv, hofReal_deriv]
  -- restrict scalars: the real derivative is the restriction of the complex one
  have hrestr : (iteratedFDeriv ℂ j Pℂ zq).restrictScalars ℝ = iteratedFDeriv ℝ j Pℂ zq :=
    ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
      ((hPℂ_an zq hqU).contDiffAt.of_le (by exact_mod_cast le_top))
  -- so the complex derivative vanishes on all real inputs, hence is zero
  apply cml_eq_zero_of_real_inputs
  intro w
  have h2 := DFunLike.congr_fun hcomp_zero w
  rw [← hrestr] at h2
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.coe_restrictScalars, ContinuousMultilinearMap.zero_apply] using h2

/-- **Section-order complexification.** If the real witness `P` has constant order `μ` along the
section `{(y,0)}` near `0`, its complexification `Pℂ` (analytic, agreeing on the real slice, with
`order ℂ Pℂ 0 = μ`) has constant order `μ` along the complex section near `0`. -/
theorem complexify_section_order_invariant
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (Pℂ : CParam s e → ℂ)
    (U : Set (CParam s e)) (hU : IsOpen U) (hU0 : (0 : CParam s e) ∈ U)
    (hPℂ_an : AnalyticOnNhd ℂ Pℂ U)
    (hP_an : AnalyticAt ℝ P 0)
    (hagree : ∀ᶠ p in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Pℂ (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2) = Complex.ofReal (P p))
    (μ : ℕ)
    (hμ0 : order ℂ Pℂ 0 = μ)
    (hP_real_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = μ) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), order ℂ Pℂ ((y, 0) : CParam s e) = (μ : ℕ∞) := by
  classical
  -- USC: order ≤ μ along the section near 0
  have h_le : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), order ℂ Pℂ ((y, 0) : CParam s e) ≤ μ := by
    have h_open := isOpen_order_le_inter U hU Pℂ hPℂ_an (↑μ)
    have hnhds : {z : CParam s e | z ∈ U ∧ order ℂ Pℂ z ≤ ↑μ}
        ∈ 𝓝 (0 : CParam s e) := h_open.mem_nhds ⟨hU0, le_of_eq hμ0⟩
    have hcont : ContinuousAt (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) 0 := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hnhds] with y hy
    exact hy.2
  -- lower bound: order ≥ μ along the section near 0
  have h_ge : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), (μ : ℕ∞) ≤ order ℂ Pℂ ((y, 0) : CParam s e) := by
    suffices h_dv : ∀ j < μ, ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        iteratedFDeriv ℂ j Pℂ ((y, 0) : CParam s e) = 0 by
      rcases μ with _ | μ
      · filter_upwards with y; simp
      · have hall := (Finset.range (μ + 1)).eventually_all.mpr
          (fun j hj => h_dv j (Finset.mem_range.mp hj))
        filter_upwards [hall] with y hy
        unfold order; split_ifs with hex
        · exact Nat.cast_le.mpr (Nat.le_of_not_lt fun hlt =>
            Nat.find_spec hex (hy _ (Finset.mem_range.mpr hlt)))
        · exact le_top
    intro j hj
    -- vanishing of the full ℂ-derivative at real section points
    have hreal_vanish : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ),
        iteratedFDeriv ℂ j Pℂ ((Complex.ofReal ∘ x, (0 : Fin e → ℂ)) : CParam s e) = 0 := by
      obtain ⟨W, hWsub, hWopen, hW0⟩ := eventually_nhds_iff.mp hagree
      obtain ⟨W2, hW2sub, hW2open, hW20⟩ := eventually_nhds_iff.mp hP_an.eventually_analyticAt
      have hc : Continuous (fun x : Fin s → ℝ => ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ))) := by fun_prop
      have hcU : Continuous (fun x : Fin s → ℝ => prodEmbedCLM s e ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ))) :=
        (prodEmbedCLM s e).continuous.comp hc
      have hpre : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ),
          (((x, 0) : (Fin s → ℝ) × (Fin e → ℝ)) ∈ W ∧ ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ)) ∈ W2)
            ∧ prodEmbedCLM s e ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ)) ∈ U := by
        have h1 := hc.continuousAt.preimage_mem_nhds (hWopen.mem_nhds (by simpa using hW0))
        have h2 := hc.continuousAt.preimage_mem_nhds (hW2open.mem_nhds (by simpa using hW20))
        have h3 := hcU.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hU0))
        filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 using ⟨⟨hx1, hx2⟩, hx3⟩
      filter_upwards [hP_real_oi, hpre] with x hx_oi hx_mem
      obtain ⟨⟨hxW, hxW2⟩, hxU⟩ := hx_mem
      have hPq_cd : ContDiffAt ℝ j P ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ)) :=
        (hW2sub _ hxW2).contDiffAt.of_le le_top
      have hreal0 : iteratedFDeriv ℝ j P ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ)) = 0 :=
        iteratedFDeriv_eq_zero_of_lt_order (by rw [hx_oi]; exact_mod_cast hj)
      have hagree_q : (fun p => Pℂ (Complex.ofReal ∘ p.1, Complex.ofReal ∘ p.2))
          =ᶠ[𝓝 ((x, 0) : (Fin s → ℝ) × (Fin e → ℝ))] fun p => Complex.ofReal (P p) := by
        filter_upwards [hWopen.mem_nhds hxW] with p hp using hWsub p hp
      have := cderiv_zero_at_real_point P Pℂ U hU hPℂ_an (x, 0) hxU hPq_cd hagree_q hreal0
      rwa [prodEmbedCLM_apply, ofReal_comp_zero] at this
    -- identity theorem in the section variable `y`: each (reindexed) basis evaluation vanishes near 0
    have hbasis_zero : ∀ b : Fin j → Fin (s + e), ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        (iteratedFDeriv ℂ j Pℂ ((y, 0) : CParam s e))
          (fun i => reindexCLE ℂ s e (Pi.single (b i) (1 : ℂ))) = 0 := by
      intro b
      set g_b : (Fin s → ℂ) → ℂ :=
        fun y => (iteratedFDeriv ℂ j Pℂ ((y, 0) : CParam s e))
          (fun i => reindexCLE ℂ s e (Pi.single (b i) (1 : ℂ))) with hg_b
      have hincl_an : AnalyticAt ℂ (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) 0 :=
        (ContinuousLinearMap.inl ℂ (Fin s → ℂ) (Fin e → ℂ)).analyticAt 0
      have hderiv_an : AnalyticAt ℂ (iteratedFDeriv ℂ j Pℂ) ((0, 0) : CParam s e) :=
        hPℂ_an.iteratedFDeriv j _ hU0
      have hcomp_an : AnalyticAt ℂ (fun y : Fin s → ℂ => iteratedFDeriv ℂ j Pℂ ((y, 0) : CParam s e))
          0 := hderiv_an.comp_of_eq hincl_an rfl
      have hg_an : AnalyticAt ℂ g_b (0 : Fin s → ℂ) :=
        ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => CParam s e) ℂ
          (fun i : Fin j => reindexCLE ℂ s e (Pi.single (b i) (1 : ℂ)))).analyticAt _).comp hcomp_an
      have hg_real_zero : ∀ᶠ x in 𝓝 (0 : Fin s → ℝ), g_b (Complex.ofReal ∘ x) = 0 := by
        filter_upwards [hreal_vanish] with x hx
        show (iteratedFDeriv ℂ j Pℂ ((Complex.ofReal ∘ x, 0) : CParam s e))
          (fun i => reindexCLE ℂ s e (Pi.single (b i) 1)) = 0
        rw [hx, ContinuousMultilinearMap.zero_apply]
      have hord_top : order ℂ g_b (Complex.ofReal ∘ (0 : Fin s → ℝ)) = ⊤ :=
        order_eq_top_of_real_eq_zero g_b 0
          (by rwa [show Complex.ofReal ∘ (0 : Fin s → ℝ) = (0 : Fin s → ℂ) from by ext; simp])
          hg_real_zero
      rw [show Complex.ofReal ∘ (0 : Fin s → ℝ) = (0 : Fin s → ℂ) from by ext; simp] at hord_top
      exact eventuallyEq_zero_of_order_eq_top g_b 0 hg_an hord_top
    have hall := Finset.univ.eventually_all.mpr (fun b _ => hbasis_zero b)
    filter_upwards [hall] with y hy
    apply cml_eq_zero_of_reindex_basis
    intro v
    exact hy v (Finset.mem_univ _)
  filter_upwards [h_le, h_ge] with y hle hge
  exact le_antisymm hle hge

end
