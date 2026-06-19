import Cad.Multivariate.ProjectionTheorem.Generalized.ClusterAssembly
import Cad.Multivariate.ProjectionTheorem.Generalized.MembershipComplexify
import Cad.Multivariate.ProjectionTheorem.Generalized.ComplexifyGlue
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassZariskiAxioms
import Cad.Multivariate.ProjectionTheorem.Generalized.WeierstrassPrep
import Cad.Multivariate.ProjectionTheorem.Generalized.AnalyticOrderPoly
import Cad.Multivariate.ProjectionTheorem.Generalized.ClusterCover

/-!
# A3 closed: real cluster → complex root structure

`cluster_from_real` is the full A3 front-end. From the **real** section family `g`, witness `P`,
analytic cofactors `A,B` with their elimination membership, and the section order invariance — plus
the per-cluster **localization datum** (the multiplicity `m` of the cluster root at `t = 0`) — it
constructs every input of `single_cluster_from_weierstrass` (complexification + the C-axiom
application) and produces the holomorphic root sections of the section Weierstrass polynomial.

This composes: `complexify_pseudopoly_prod`/`analyticAt_complexify_prod` (frictions #1/#2) →
`map_agree_of_complexify` glue → `complexify_membership` (item (b)) → `weierstrass_preparation_analytic`
(C axiom, item (a)) → `complexify_section_order_invariant` → `single_cluster_from_weierstrass`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **R1 — real section-family order-invariance from a complexification.** Given a real section-family
evaluation `G` on `((Fin s→ℝ)×(Fin e→ℝ))×ℝ` and its holomorphic complexification `F_ℂ` on
`CParam s e × ℂ` (agreeing on the real slice near each branch graph point), if `F_ℂ` is order-invariant
along the **complex** branch `ξ` (`hcoi`, the output of `orderinv_of_weierstrass`/Zariski (2)), and the
real branch `η` is the real restriction of `ξ` (`hreal`, branch reality), then `G` is order-invariant
along the real branch graph `((y,0), η y)`. Pure chaining of `order_real_eq_order_complex_prod` (R1b)
with the complex order-invariance, pulled back along the real embedding. -/
lemma section_orderinv_of_complex
    (G : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ → ℝ)
    (F_ℂ : CParam s e × ℂ → ℂ)
    (ξ : (Fin s → ℂ) → ℂ) (hξ0 : ξ 0 = 0)
    (η : (Fin s → ℝ) → ℝ) (hη0 : η 0 = 0)
    (hcoi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ F_ℂ ((y, 0), ξ y) = order ℂ F_ℂ ((0, 0), ξ 0))
    (hreal : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (↑(η y) : ℂ) = ξ (Complex.ofReal ∘ y))
    (hG_an : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), AnalyticAt ℝ G ((y, 0), η y))
    (hFℂ_an : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      AnalyticAt ℂ F_ℂ ((Complex.ofReal ∘ y, (0 : Fin e → ℂ)), (↑(η y) : ℂ)))
    (hagree : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      ∀ᶠ x in 𝓝 (((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)), η y),
        F_ℂ ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2), (x.2 : ℂ)) = ↑(G x)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      order ℝ G ((y, 0), η y) = order ℝ G ((0, 0), η 0) := by
  -- base point value, through the complexification
  have hbase : order ℝ G ((0, 0), η 0) = order ℂ F_ℂ ((0, 0), ξ 0) := by
    have hR1b0 := order_real_eq_order_complex_prod G F_ℂ ((0, 0), η 0)
      hG_an.self_of_nhds hFℂ_an.self_of_nhds hagree.self_of_nhds
    rw [← hR1b0]
    simp only [ofReal_comp_zero, hη0, Complex.ofReal_zero, hξ0]
  -- pull the complex order-invariance back along the real embedding
  have htend : Filter.Tendsto (fun y : Fin s → ℝ => (Complex.ofReal ∘ y : Fin s → ℂ))
      (𝓝 0) (𝓝 0) := by
    have h := (realEmbedding s).continuous.tendsto (0 : Fin s → ℝ)
    rw [map_zero] at h; simpa [realEmbedding_apply] using h
  filter_upwards [hreal, hG_an, hFℂ_an, hagree, htend.eventually hcoi]
    with y hr hGa hFa hag hco
  have hR1b := order_real_eq_order_complex_prod G F_ℂ ((y, 0), η y) hGa hFa hag
  rw [← hR1b]
  simp only [ofReal_comp_zero]
  rw [hr, hco, hbase]

/-- **A3 closed.** Real data + per-cluster localization datum ⟹ complex single-cluster root
structure. -/
theorem cluster_from_real (m : ℕ) (hm_pos : 0 < m)
    -- real section family with degree bound and analytic coefficients
    (Ng : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (hg_deg : ∀ w, (g w).natDegree ≤ Ng)
    (hg_coeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    -- witness
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hP_an : AnalyticAt ℝ P 0) (hP_ne : order ℝ P 0 ≠ ⊤)
    -- analytic cofactors + elimination membership
    (NA NB : ℕ) (A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hA_deg : ∀ w, (A w).natDegree ≤ NA) (hB_deg : ∀ w, (B w).natDegree ≤ NB)
    (hA_coeff : ∀ i, AnalyticAt ℝ (fun w => (A w).coeff i) 0)
    (hB_coeff : ∀ i, AnalyticAt ℝ (fun w => (B w).coeff i) 0)
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w))
    -- section order invariance (real)
    (hP_oi_real : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0)
    -- localization datum: the cluster root at `t = 0` has multiplicity `m`
    (hm_root : (g 0).rootMultiplicity 0 = m)
    -- section degree constancy (so `g(y,0) ≠ 0` near `0`)
    (hg_deg_const : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree) :
    ∃ (ξ : (Fin s → ℂ) → ℂ) (δ₀ : ℝ),
      AnalyticAt ℂ ξ 0 ∧ ξ 0 = 0 ∧ 0 < δ₀ ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ α : ℂ, ‖α‖ < δ₀ →
        (((g (y, 0)).map (algebraMap ℝ ℂ)).IsRoot α ↔ α = ξ (realEmbedding s y))) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
        ((g (y, 0)).map (algebraMap ℝ ℂ)).rootMultiplicity (ξ (realEmbedding s y)) = m) ∧
      -- order-invariance data: the holomorphic complexification `F_ℂ` of the section-family
      -- evaluation, agreeing on the real slice, order-invariant along the complex branch `ξ`
      ∃ F_ℂ : CParam s e × ℂ → ℂ,
        AnalyticAt ℂ F_ℂ 0 ∧
        (∀ᶠ x in 𝓝 (0 : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ),
          F_ℂ ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2), (x.2 : ℂ))
            = Complex.ofReal ((g x.1).eval x.2)) ∧
        (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
          order ℂ F_ℂ ((y, 0), ξ y) = order ℂ F_ℂ ((0, 0), ξ 0)) := by
  -- complexify `g`, `A`, `B`, `P`
  obtain ⟨gℂ, hgℂ_coeff, hgℂ_agree⟩ := complexify_pseudopoly_prod Ng g hg_deg hg_coeff
  obtain ⟨Aℂ_fam, hAℂ_coeff, hAℂ_agree⟩ := complexify_pseudopoly_prod NA A hA_deg hA_coeff
  obtain ⟨Bℂ_fam, hBℂ_coeff, hBℂ_agree⟩ := complexify_pseudopoly_prod NB B hB_deg hB_coeff
  obtain ⟨Pℂ, hPℂ_an, hPℂ_agree, hPℂ_order⟩ := analyticAt_complexify_prod P hP_an
  set g_poly := polyOfFamily Ng gℂ with hg_poly
  set Aℂ := polyOfFamily NA Aℂ_fam with hAℂ
  set Bℂ := polyOfFamily NB Bℂ_fam with hBℂ
  have hg_poly_an : AnalyticCoeffs g_poly := analyticCoeffs_polyOfFamily Ng gℂ hgℂ_coeff
  have hAℂ_an : AnalyticCoeffs Aℂ := analyticCoeffs_polyOfFamily NA Aℂ_fam hAℂ_coeff
  have hBℂ_an : AnalyticCoeffs Bℂ := analyticCoeffs_polyOfFamily NB Bℂ_fam hBℂ_coeff
  -- `Polynomial.map`-level agreements
  have hg_map := map_agree_of_complexify Ng g gℂ hg_deg hgℂ_agree
  have hA_map := map_agree_of_complexify NA A Aℂ_fam hA_deg hAℂ_agree
  have hB_map := map_agree_of_complexify NB B Bℂ_fam hB_deg hBℂ_agree
  have hP_map : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Pℂ (prodEmbedCLM s e w) = algebraMap ℝ ℂ (P w) := by
    filter_upwards [hPℂ_agree] with w hw
    rw [prodEmbedCLM_apply, Complex.coe_algebraMap]; exact hw
  -- item (b): the eventual `polyToFun` membership
  have hmem_poly := complexify_membership g A B P g_poly Aℂ Bℂ Pℂ hg_poly_an hAℂ_an hBℂ_an
    hPℂ_an hg_map hA_map hB_map hP_map hmem
  -- item (a): the C axiom
  have hGℂ_an : AnalyticAt ℂ (polyToFun s e g_poly) 0 := polyToFun_analyticAt g_poly hg_poly_an
  have hG0 : (fun t : ℂ => polyToFun s e g_poly ((0 : CParam s e), t))
      = fun t => ((g 0).map (algebraMap ℝ ℂ)).eval t := by
    have h0 := hg_map.self_of_nhds
    rw [show prodEmbedCLM s e (0 : (Fin s → ℝ) × (Fin e → ℝ)) = 0 from map_zero _] at h0
    funext t
    rw [polyToFun_apply]
    simp only []
    rw [h0]
  have hg0_ne : g 0 ≠ 0 := by
    intro h; rw [h, rootMultiplicity_zero] at hm_root; omega
  have hm_ord : analyticOrderAt (fun t : ℂ => ((g 0).map (algebraMap ℝ ℂ)).eval t) 0 = (m : ℕ∞) := by
    have hgo := analyticOrderAt_polynomial_eval_ofReal hg0_ne (0 : ℝ)
    rw [map_zero] at hgo
    rw [hgo]; exact_mod_cast hm_root
  have hord : analyticOrderAt (fun t : ℂ => polyToFun s e g_poly ((0 : CParam s e), t)) 0 = (m : ℕ∞) := by
    rw [hG0]; exact hm_ord
  obtain ⟨u, a, hu_an, hu0, ha_an, ha0, hfac_raw⟩ :=
    weierstrass_preparation_analytic (polyToFun s e g_poly) hGℂ_an m hord
  have hfac : polyToFun s e g_poly =ᶠ[𝓝 0]
      fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt := by
    filter_upwards [hfac_raw] with zt hzt
    rw [hzt, polyToFun_weierstrassPolyFun]
  -- `hP_ne` for the complexification
  have hP_ne_C : order ℂ Pℂ 0 ≠ ⊤ := by rw [hPℂ_order]; exact hP_ne
  -- section order (complex), via the localized lemma
  obtain ⟨V, hVsub, hVopen, hV0⟩ := eventually_nhds_iff.mp hPℂ_an.eventually_analyticAt
  set μ := (order ℝ P 0).toNat with hμdef
  have hμ_eq : order ℝ P 0 = (μ : ℕ∞) := (ENat.coe_toNat hP_ne).symm
  have hP_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ Pℂ ((y, 0) : CParam s e) = order ℂ Pℂ ((0, 0) : CParam s e) := by
    have hμ0 : order ℂ Pℂ 0 = (μ : ℕ∞) := by rw [hPℂ_order, hμ_eq]
    have hreal_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = (μ : ℕ∞) := by
      filter_upwards [hP_oi_real] with y hy; rw [hy, hμ_eq]
    have hsec := complexify_section_order_invariant P Pℂ V hVopen hV0
      (fun z hz => hVsub z hz) hP_an hPℂ_agree μ hμ0 hreal_oi
    filter_upwards [hsec] with y hy
    rw [hy, show ((0, 0) : CParam s e) = 0 from rfl, hμ0]
  -- assemble the single cluster (Theorem 4.1.1: a single holomorphic branch `ψ`)
  obtain ⟨ψ, hψ_an, hψ0, hroots, hmults, horderinv⟩ :=
    single_cluster_from_weierstrass m hm_pos a ha_an ha0 g_poly u hu_an hfac
      Pℂ hPℂ_an hP_ne_C Aℂ Bℂ hAℂ_an hBℂ_an hmem_poly hP_oi
  -- section-level map agreement (specialise `hg_map` to `w = (y, 0)`)
  have hfam_map : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      g_poly.map (Pi.evalRingHom (fun _ => ℂ) ((realEmbedding s y, 0) : CParam s e))
        = (g (y, 0)).map (algebraMap ℝ ℂ) := by
    have htend : Filter.Tendsto (fun y : Fin s → ℝ => ((y, 0) : (Fin s → ℝ) × (Fin e → ℝ)))
        (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun y : Fin s → ℝ => ((y, 0) : (Fin s → ℝ) × (Fin e → ℝ))) := by fun_prop
      simpa using hc.tendsto 0
    filter_upwards [htend.eventually hg_map] with y hy
    rwa [show prodEmbedCLM s e (y, 0) = ((realEmbedding s y, 0) : CParam s e) from by
      rw [prodEmbedCLM_apply]; simp [realEmbedding_apply]] at hy
  -- `g(y,0) ≠ 0` near `0` (degree `≥ m ≥ 1`)
  have hdeg0_pos : 0 < (g 0).natDegree := by
    have hdvd : (X : Polynomial ℝ) ^ m ∣ g 0 := by
      have h := Polynomial.pow_rootMultiplicity_dvd (g 0) 0
      rwa [map_zero, sub_zero, hm_root] at h
    have hle := Polynomial.natDegree_le_of_dvd hdvd hg0_ne
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one] at hle
    omega
  have hfam_ne : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).map (algebraMap ℝ ℂ) ≠ 0 := by
    filter_upwards [hg_deg_const] with y hdy
    have hne : g (y, 0) ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hdy; omega
    exact (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hne
  -- Real-slice covering / multiplicity via the bridges, instantiated at the single branch (`r = 1`).
  have hroots1 : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ ∃ _i : Fin 1, α = ψ y := by
    filter_upwards [hroots] with y hy α
    rw [hy α]; exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
  have hmults1 : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      Function.Injective (fun _i : Fin 1 => ψ y) → ∀ _i : Fin 1,
        (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ y) = m := by
    filter_upwards [hmults] with y hy _ _i; exact hy
  have hmult_match := multmatch_of_weierstrass m a g_poly u hu0 hu_an hfac
    (fun _ : Fin 1 => ψ) (fun _ => m) (fun _ => hψ_an) (fun _ => hψ0) hmults1
    (fun y => (g (y, 0)).map (algebraMap ℝ ℂ)) hfam_ne hfam_map
  obtain ⟨δ₀, hδ₀, hcover⟩ := cover_of_weierstrass m a g_poly u hu0 hu_an hfac
    (fun _ : Fin 1 => ψ) hroots1 (fun y => (g (y, 0)).map (algebraMap ℝ ℂ)) hfam_map
  have hinj1 : ∀ y : Fin s → ℝ, Function.Injective (fun _i : Fin 1 => ψ (realEmbedding s y)) :=
    fun y a b _ => Subsingleton.elim a b
  -- order-invariance data: `F_ℂ = polyToFun g_poly` (complexification of the section evaluation),
  -- order-invariant along `ψ` via `orderinv_of_weierstrass` + the Zariski (2) conjunct `horderinv`.
  have hcoi := orderinv_of_weierstrass m a ha_an g_poly u hu0 hu_an hfac ψ hψ_an hψ0 horderinv
  have hagree_F : ∀ᶠ x in 𝓝 (0 : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ),
      polyToFun s e g_poly ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2), (x.2 : ℂ))
        = Complex.ofReal ((g x.1).eval x.2) := by
    have htend : Filter.Tendsto
        (Prod.fst : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ → (Fin s → ℝ) × (Fin e → ℝ)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_fst.tendsto (0 : ((Fin s → ℝ) × (Fin e → ℝ)) × ℝ))
    filter_upwards [htend.eventually hg_map] with x hx
    have hz1 : ((Complex.ofReal ∘ x.1.1, Complex.ofReal ∘ x.1.2) : CParam s e) = prodEmbedCLM s e x.1 := by
      rw [prodEmbedCLM_apply]
    rw [polyToFun_apply, hz1, hx, show (↑x.2 : ℂ) = algebraMap ℝ ℂ x.2 from rfl,
      Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  refine ⟨ψ, δ₀, hψ_an, hψ0, hδ₀, ?_, ?_, polyToFun s e g_poly, hGℂ_an, hagree_F, hcoi⟩
  · filter_upwards [hcover] with y hy α hα
    rw [hy α hα]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  · filter_upwards [hmult_match] with y hy
    exact hy (hinj1 y) 0

end
