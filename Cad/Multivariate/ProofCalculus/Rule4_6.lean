import Cad.Multivariate.ProofCalculus.Basic

namespace ProofCalculus

theorem nalbach_4_6_part1
    (i : Nat)
    (R : Set (Fin i → ℝ))
    (s : Fin i → ℝ)
    (p : MvPolynomial (Fin i) ℝ) :
    p.eval s ≠ 0 → sample i s R → sgn_inv i R p → ord_inv i R p := by
  intro hps hsample hsgn
  -- `p` is sign-invariant and nonzero at `s ∈ R`, so it is nonzero everywhere on `R`.
  have hne : ∀ c ∈ R, p.eval c ≠ 0 := by
    intro c hc hc0
    have h := hsgn c hc s hsample
    rw [sgn_eq_zero_of_eq_zero hc0] at h
    exact hps (eq_zero_of_sgn_eq_zero h.symm)
  -- a polynomial that does not vanish has vanishing order `0`, so the order is constant.
  intro a ha b hb
  rw [(polyOrder_zero_iff i p a).mpr (hne a ha), (polyOrder_zero_iff i p b).mpr (hne b hb)]

def project (i : Nat) (s : Fin (i + 1) → ℝ) : Fin i → ℝ :=
  fun j => s j.succ

def project_set (i : Nat) (S : Set (Fin (i + 1) → ℝ)) : Set (Fin i → ℝ) := S.image (project i)

/-- Evaluating a specialization at `y` equals evaluating the full polynomial at `Fin.cons y a`. -/
lemma eval_specialize {n : ℕ} (g : PolyR n) (a : Fin n → ℝ) (y : ℝ) :
    (specialize g a).eval y = MvPolynomial.eval (Fin.cons y a) (toMvPoly g) := by
  simp only [specialize, toMvPoly]
  rw [MvPolynomial.eval_eq_eval_mv_eval', (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply g]

-- i + 1 here = i on thesis
theorem nalbach_4_6_part2
    (i : Nat)
    (R : Set (Fin (i + 1) → ℝ))
    (s : Fin (i + 1) → ℝ)
    (p : MvPolynomial (Fin (i + 1)) ℝ) :
    p.eval s = 0 →
    sample (i + 1) s R →
    an_sub i (project_set i R) →
    connected (i + 1) R →
    sgn_inv (i + 1) R p →
    an_del i (project_set i R) (ofMvPoly p) →
    ord_inv (i + 1) R p := by
  intro hps hsample _hsub hconn hsgn hdel
  -- `p` is sign-invariant and vanishes at `s ∈ R`, hence vanishes on all of `R`.
  have hp0 : ∀ r ∈ R, p.eval r = 0 := by
    intro r hr
    have h := hsgn r hr s hsample
    rw [sgn_eq_zero_of_eq_zero hps] at h
    exact eq_zero_of_sgn_eq_zero h
  -- reconstructing a full point from its projection and main coordinate.
  have hcons : ∀ r : Fin (i + 1) → ℝ, Fin.cons (r 0) (project i r) = r :=
    fun r => Fin.cons_self_tail r
  obtain ⟨hdel1, hdel2⟩ := hdel
  obtain ⟨k, θ, m, hθan, hθord, hθcover, hmpos, hθmult⟩ := hdel1
  -- projections of `R` land in the base set; `r 0` is a root of the specialization there.
  have hprojmem : ∀ r ∈ R, project i r ∈ project_set i R :=
    fun r hr => Set.mem_image_of_mem (project i) hr
  have hroot : ∀ r ∈ R, (specialize (ofMvPoly p) (project i r)).IsRoot (r 0) := by
    intro r hr
    show (specialize (ofMvPoly p) (project i r)).eval (r 0) = 0
    rw [eval_specialize, toMvPoly_ofMvPoly, hcons r]
    exact hp0 r hr
  -- *** single section: by connectedness, all of `R` lies over one root function θ i₀ ***
  obtain ⟨i₀, hsec⟩ : ∃ i₀ : Fin k, ∀ r ∈ R, r 0 = θ i₀ (project i r) := by
    -- the index of the root function through the sample `s`
    obtain ⟨i₀, hi₀⟩ :=
      (hθcover (project i s) (hprojmem s hsample) (s 0)).mp (hroot s hsample)
    refine ⟨i₀, ?_⟩
    haveI hpre : PreconnectedSpace ↥R := isPreconnected_iff_preconnectedSpace.mp hconn.2
    -- continuity ingredients on the subspace `↥R`
    have hproj : Continuous (project i) := by
      unfold project; exact continuous_pi (fun j => continuous_apply j.succ)
    have hval0 : Continuous (fun x : ↥R => (x : Fin (i + 1) → ℝ) 0) :=
      (continuous_apply 0).comp continuous_subtype_val
    have hg : ∀ jdx : Fin k,
        Continuous (fun x : ↥R => θ jdx (project i (x : Fin (i + 1) → ℝ))) :=
      fun jdx => (hθan jdx).continuousOn.comp_continuous
        (hproj.comp continuous_subtype_val) (fun x => hprojmem (x : Fin (i + 1) → ℝ) x.2)
    -- `C jdx` = the points of `R` lying on the `jdx`-th root function
    let C : Fin k → Set ↥R :=
      fun jdx => {x | (x : Fin (i + 1) → ℝ) 0 = θ jdx (project i (x : Fin (i + 1) → ℝ))}
    have memC : ∀ (x : ↥R) (jdx : Fin k),
        x ∈ C jdx ↔ (x : Fin (i + 1) → ℝ) 0 = θ jdx (project i (x : Fin (i + 1) → ℝ)) :=
      fun _ _ => Iff.rfl
    have hCclosed : ∀ jdx, IsClosed (C jdx) := fun jdx => isClosed_eq hval0 (hg jdx)
    -- every point of `R` lies on some root function (its main coordinate is a root)
    have hmemC : ∀ x : ↥R, ∃ jdx, x ∈ C jdx := fun x =>
      (hθcover (project i x) (hprojmem (x : Fin (i + 1) → ℝ) x.2) ((x : Fin (i + 1) → ℝ) 0)).mp
        (hroot (x : Fin (i + 1) → ℝ) x.2)
    -- distinct root functions take distinct values (strict ordering)
    have hdistinct : ∀ (x : ↥R) (jdx : Fin k), jdx ≠ i₀ →
        θ jdx (project i (x : Fin (i + 1) → ℝ)) ≠ θ i₀ (project i (x : Fin (i + 1) → ℝ)) := by
      intro x jdx hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_lt (hθord _ (hprojmem (x : Fin (i + 1) → ℝ) x.2) jdx i₀ hlt)
      · exact ne_of_gt (hθord _ (hprojmem (x : Fin (i + 1) → ℝ) x.2) i₀ jdx hgt)
    -- `C i₀` is clopen: closed, and its complement is the (finite) union of the other `C jdx`
    have hcompl : (C i₀)ᶜ = ⋃ jdx ∈ {jdx : Fin k | jdx ≠ i₀}, C jdx := by
      ext x
      constructor
      · intro hx
        obtain ⟨jdx, hjdx⟩ := hmemC x
        have hne : jdx ≠ i₀ := fun h => hx (h ▸ hjdx)
        exact Set.mem_biUnion hne hjdx
      · intro hx hxC
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
        obtain ⟨jdx, hne, hjdx⟩ := hx
        have e1 : (x : Fin (i + 1) → ℝ) 0 = θ jdx (project i (x : Fin (i + 1) → ℝ)) := hjdx
        have e2 : (x : Fin (i + 1) → ℝ) 0 = θ i₀ (project i (x : Fin (i + 1) → ℝ)) := hxC
        exact hdistinct x jdx hne (e1.symm.trans e2)
    have hclosed_compl : IsClosed ((C i₀)ᶜ) := by
      rw [hcompl]
      exact Set.Finite.isClosed_biUnion (Set.toFinite _) (fun jdx _ => hCclosed jdx)
    have hclopen : IsClopen (C i₀) := by
      refine ⟨hCclosed i₀, ?_⟩
      rw [← compl_compl (C i₀)]; exact hclosed_compl.isOpen_compl
    -- by connectedness `C i₀` is everything (it contains the sample)
    rcases isClopen_iff.mp hclopen with hempty | huniv
    · exfalso
      have hmem : (⟨s, hsample⟩ : ↥R) ∈ C i₀ := (memC ⟨s, hsample⟩ i₀).mpr hi₀
      rw [hempty] at hmem; exact Set.notMem_empty _ hmem
    · intro r hr
      have hmem : (⟨r, hr⟩ : ↥R) ∈ C i₀ := by rw [huniv]; exact Set.mem_univ _
      exact (memC ⟨r, hr⟩ i₀).mp hmem
  -- that root function is continuous and a genuine root function, so `p` is order-invariant
  -- on its section, which contains `R`.
  have hθcont : ContinuousOn (θ i₀) (project_set i R) := (hθan i₀).continuousOn
  have hθroot : IsRootFunction (ofMvPoly p) (θ i₀) (project_set i R) :=
    fun a ha => (hθcover a ha (θ i₀ a)).mpr ⟨i₀, rfl⟩
  have hoinv := hdel2 (θ i₀) hθcont hθroot
  have hbridge : ∀ r : Fin (i + 1) → ℝ,
      polyOrder (i + 1) p r = orderFull (ofMvPoly p) (project i r) (r 0) := by
    intro r
    simp only [orderFull, toMvPoly_ofMvPoly]
    rw [hcons r]
  intro a ha b hb
  have mem_a : ((project i a, a 0) : (Fin i → ℝ) × ℝ) ∈ SectionGraph (θ i₀) (project_set i R) :=
    ⟨hprojmem a ha, hsec a ha⟩
  have mem_b : ((project i b, b 0) : (Fin i → ℝ) × ℝ) ∈ SectionGraph (θ i₀) (project_set i R) :=
    ⟨hprojmem b hb, hsec b hb⟩
  rw [hbridge a, hbridge b]
  exact hoinv _ mem_a _ mem_b

end ProofCalculus
