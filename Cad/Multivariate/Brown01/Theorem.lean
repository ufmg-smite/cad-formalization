import Mathlib
import Cad.Multivariate.ProjectionTheorem.Generalized.Projection
import Cad.Multivariate.Brown01.Transfer
import Cad.Multivariate.Brown01.Refine
import Cad.Multivariate.Brown01.Discr

/-!
# Brown's theorem, generalized to elimination ideals — pipeline form

`brown_generalized` is the *pipeline form* of the generalized Brown theorem
(Corollary 5.3 / Theorem 5.5 of `thesis/brown_pipeline_direct.tex`): if `P ≠ 0`
lies in `⟨f, f_z⟩ ∩ R[x]`, and **both** `P` and `lc f` are order-invariant on the
connected analytic submanifold `S`, and `f` vanishes identically at no point of
`S`, then `f` is degree-invariant on `S`.

This is the *direct* proof: it uses a **single** elimination-ideal membership and
avoids both the bivariate homogenization layer and the explicit B\'ezout
"certificate transfer" of the companion notes (`thesis/brown_generalized.tex`,
Theorem 3.1' / Lemma 5.1).  The price is that `lc f` must be order-invariant
rather than merely sign-invariant — which is exactly what the cells of a
McCallum-style CAD supply.

Proof layout (following §5 of `brown_pipeline_direct.tex`):
* order-invariance of `lc f` splits `S` into the case `lc f ≡ 0` and the case
  `lc f` nowhere zero (`lc_dichotomy`); the latter gives constant degree `deg f`;
* in the former, at each `p ∈ S` choose `γ` with `f(p, γ) ≠ 0`, pass to the
  auxiliary polynomial `f* = reflect n (taylor γ f)`, and use the
  cofactor-free `Brown.witness_transfer_shifted` to obtain the order-invariant
  witness `lc(f)^M · P ∈ ⟨f*, (f*)'⟩`.  Refine `S` to a connected analytic
  submanifold `S ∩ N` inside `{f(·, γ) ≠ 0}` (`IsAnalyticSubmanifold.refine_connected`)
  and apply the generalized lifting theorem to `f*`.  The multiplicity of the
  root `0` of `f*` along the unique delineation branch through `0` records the
  degree drop `n - deg f(q, ·)`, which is therefore locally constant;
* a locally constant function on connected `S` is constant.
-/

open Polynomial in
/-- From order-invariance of `g` on `S`, the value of `g` either vanishes
everywhere on `S` or nowhere on `S`.  (Order `0` ⇔ nonvanishing, via
`polyOrder_zero_iff`, so a constant order forces one of the two regimes.)  This
replaces the sign-invariance dichotomy of the companion development. -/
private lemma lc_dichotomy {k : Nat} (g : MvPolynomial (Fin k) ℝ)
    (S : Set (Fin k → ℝ)) (h_ord : OrderInvariantMv g S) :
    (∀ q ∈ S, evalBase q g = 0) ∨ (∀ q ∈ S, evalBase q g ≠ 0) := by
  classical
  by_cases hex : ∃ q ∈ S, evalBase q g = 0
  · left
    obtain ⟨q₀, hq₀, hq₀0⟩ := hex
    intro q hq
    by_contra hne
    have h1 : polyOrder k g q = 0 := (polyOrder_zero_iff k g q).mpr hne
    have h2 : polyOrder k g q₀ = 0 := (h_ord q₀ hq₀ q hq).trans h1
    exact (polyOrder_zero_iff k g q₀).mp h2 hq₀0
  · right
    push_neg at hex
    exact hex

open Polynomial in
/-- Specialization commutes with the shift-and-reflect construction of `f*`. -/
private lemma spec_reflect_taylor {k : Nat} (f : PolyR k) (γ : ℝ) (q : Fin k → ℝ) :
    specialize (reflect f.natDegree (taylor (MvPolynomial.C γ) f)) q
      = reflect f.natDegree (taylor γ (specialize f q)) := by
  show (reflect f.natDegree (taylor (MvPolynomial.C γ) f)).map (evalBase q) = _
  rw [← reflect_map, map_taylor]
  have hc : evalBase q (MvPolynomial.C γ) = γ := by simp
  rw [hc]
  rfl

open Polynomial in
/-- **Hard case, local step**: if `lc f ≡ 0` on `S`, the specialized degree of `f`
is locally constant on `S`.  This is the pointwise argument of the pipeline form,
with the order-invariant witness `lc(f)^M · P`. -/
private theorem brown_degree_locally_constant
    (k : Nat) (f : PolyR k) (P : MvPolynomial (Fin k) ℝ)
    (P_ne_zero : P ≠ 0)
    (hP_mem₁ : Polynomial.C P ∈
      Ideal.span ({ f, f.derivative } : Set (PolyR k)))
    (pos_deg : 0 < f.natDegree)
    (S : Set (Fin k → ℝ))
    (hS : IsAnalyticSubmanifold S)
    (h_ord : OrderInvariantMv P S)
    (h_ord_lc : OrderInvariantMv f.leadingCoeff S)
    (h_lc : ∀ q ∈ S, evalBase q f.leadingCoeff = 0)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (p : Fin k → ℝ) (hp : p ∈ S) :
    ∃ N : Set (Fin k → ℝ), IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ S ∩ N, (specialize f q).natDegree = (specialize f p).natDegree := by
  classical
  -- choose a shift `γ` avoiding the (finitely many) roots of `f(p, ·)`
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, (specialize f p).eval γ ≠ 0 :=
    Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ (hspec_ne p hp)
      (lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk ℝ))
  -- the auxiliary polynomial `f*` and the order-invariant witness `lc(f)^M · P`
  obtain ⟨M, hMtransfer⟩ :=
    Brown.witness_transfer_shifted f pos_deg (MvPolynomial.C γ) P hP_mem₁
  set fstar : PolyR k := reflect f.natDegree (taylor (MvPolynomial.C γ) f) with hfstar_def
  -- the witness is nonzero and order-invariant on `S`
  have hf_ne : f ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at pos_deg; exact absurd pos_deg (lt_irrefl 0)
  have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  have hQ_ne : f.leadingCoeff ^ M * P ≠ 0 := mul_ne_zero (pow_ne_zero M hlc_ne) P_ne_zero
  have hQ_ord : OrderInvariantMv (f.leadingCoeff ^ M * P) S :=
    order_invariant_mul_mv S _ _ (order_invariant_pow_mv S _ M h_ord_lc) h_ord
  -- the formal leading coefficient of `f*` is `f(·, γ)`; its constant coefficient is `lc f`
  have hkey : ∀ q, evalBase q (fstar.coeff f.natDegree) = (specialize f q).eval γ := by
    intro q
    rw [← Polynomial.coeff_map]
    show (specialize fstar q).coeff f.natDegree = _
    rw [hfstar_def, spec_reflect_taylor, coeff_reflect, revAt_le (le_refl f.natDegree),
      Nat.sub_self, taylor_coeff_zero]
  have hfstar_coeff0 : fstar.coeff 0 = f.leadingCoeff := by
    rw [hfstar_def, coeff_reflect, revAt_zero]
    conv_lhs => rw [show f.natDegree = (taylor (MvPolynomial.C γ) f).natDegree
      from (natDegree_taylor f (MvPolynomial.C γ)).symm]
    rw [coeff_natDegree, leadingCoeff_taylor]
  -- the open set where the formal leading coefficient of `f*` survives
  set N₀ : Set (Fin k → ℝ) := {q | evalBase q (fstar.coeff f.natDegree) ≠ 0} with hN₀_def
  have hN₀_open : IsOpen N₀ :=
    isOpen_ne.preimage (MvPolynomial.continuous_eval _)
  have hpN₀ : p ∈ N₀ := by
    show evalBase p (fstar.coeff f.natDegree) ≠ 0
    rw [hkey p]
    exact hγ
  -- `f*` has constant degree `n` over `N₀`
  have hdeg_fstar : ∀ q ∈ N₀, (specialize fstar q).natDegree = f.natDegree := by
    intro q hq
    apply le_antisymm
    · refine Polynomial.natDegree_map_le.trans ?_
      rw [hfstar_def]
      exact natDegree_reflect_le.trans
        (max_le le_rfl (le_of_eq (natDegree_taylor f (MvPolynomial.C γ))))
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [show (specialize fstar q).coeff f.natDegree
          = evalBase q (fstar.coeff f.natDegree) from Polynomial.coeff_map _ _]
      exact hq
  have hne_fstar : ∀ q ∈ N₀, specialize fstar q ≠ 0 := by
    intro q hq h0
    apply hq
    show evalBase q (fstar.coeff f.natDegree) = 0
    rw [← Polynomial.coeff_map]
    show (specialize fstar q).coeff f.natDegree = 0
    rw [h0, Polynomial.coeff_zero]
  -- refine `S` inside `N₀` to a connected analytic submanifold (Brown's Lemma 8.2)
  obtain ⟨N₁, hN₁_open, hpN₁, hN₁_sub, hSN₁_mfld, hSN₁_conn⟩ :=
    hS.refine_connected hp hN₀_open hpN₀
  -- apply the generalized lifting theorem to `f*` on `S ∩ N₁`
  have hdeg_inv : DegreeInvariant fstar (S ∩ N₁) := by
    intro x hx y hy
    rw [hdeg_fstar x (hN₁_sub hx.2), hdeg_fstar y (hN₁_sub hy.2)]
  obtain ⟨hdelin, -⟩ := lifting_theorem_generalized (S ∩ N₁) fstar hSN₁_mfld hSN₁_conn
    hdeg_inv (fun x hx => hne_fstar x (hN₁_sub hx.2))
    (f.leadingCoeff ^ M * P) hQ_ne hMtransfer
    (fun x hx y hy => hQ_ord x hx.1 y hy.1)
  obtain ⟨nb, θ, mult, hθ_an, hθ_ord, hθ_roots, hmult_pos, hmult_const⟩ := hdelin
  -- on `S`, the constant coefficient of `f*` vanishes, so `0` is a root
  have hzero_root : ∀ q ∈ S ∩ N₁, (specialize fstar q).IsRoot 0 := by
    intro q hq
    show (specialize fstar q).eval 0 = 0
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    show (fstar.map (evalBase q)).coeff 0 = 0
    rw [Polynomial.coeff_map, hfstar_coeff0]
    exact h_lc q hq.1
  have hpSN₁ : p ∈ S ∩ N₁ := ⟨hp, hpN₁⟩
  -- the unique branch through `0` at `p`
  obtain ⟨i₀, hi₀⟩ := (hθ_roots p hpSN₁ 0).mp (hzero_root p hpSN₁)
  -- isolate that branch: near `p` (within `S ∩ N₁`) no other branch passes through `0`
  have hsep : ∀ᶠ q in nhdsWithin p (S ∩ N₁), ∀ j, j ≠ i₀ → θ j q ≠ 0 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i₀
    · exact Filter.Eventually.of_forall fun q hcon => absurd hj hcon
    · have hθjp : θ j p ≠ 0 := by
        intro h0
        have heq2 : θ j p = θ i₀ p := by rw [h0]; exact hi₀
        rcases lt_or_gt_of_ne hj with h | h
        · exact absurd heq2 (ne_of_lt (hθ_ord p hpSN₁ j i₀ h))
        · exact absurd heq2.symm (ne_of_lt (hθ_ord p hpSN₁ i₀ j h))
      have htend : Filter.Tendsto (θ j) (nhdsWithin p (S ∩ N₁)) (nhds (θ j p)) :=
        (hθ_an j).continuousOn p hpSN₁
      filter_upwards [htend.eventually (isOpen_ne.mem_nhds hθjp)] with q hq _
      exact hq
  obtain ⟨O, hO_open, hpO, hO_sub⟩ := mem_nhdsWithin.mp hsep
  -- on `S ∩ (N₁ ∩ O)` the degree of `f` is constantly `n - mult i₀`
  have key : ∀ q ∈ S ∩ (N₁ ∩ O),
      (specialize f q).natDegree = f.natDegree - mult i₀ := by
    rintro q ⟨hqS, hqN₁, hqO⟩
    have hqSN₁ : q ∈ S ∩ N₁ := ⟨hqS, hqN₁⟩
    obtain ⟨j, hj⟩ := (hθ_roots q hqSN₁ 0).mp (hzero_root q hqSN₁)
    have hj_eq : j = i₀ := by
      by_contra hne
      exact hO_sub ⟨hqO, hqSN₁⟩ j hne hj.symm
    have hθi₀q : θ i₀ q = 0 := by rw [← hj_eq, ← hj]
    have hm := hmult_const q hqSN₁ i₀
    rw [hθi₀q] at hm
    have hψ_ne : taylor γ (specialize f q) ≠ 0 := by
      rw [Ne, taylor_eq_zero]
      exact hspec_ne q hqS
    have hψ_deg : (taylor γ (specialize f q)).natDegree ≤ f.natDegree := by
      rw [natDegree_taylor]
      exact Polynomial.natDegree_map_le
    have htrail : (specialize fstar q).rootMultiplicity 0
        = f.natDegree - (specialize f q).natDegree := by
      rw [hfstar_def, spec_reflect_taylor, Polynomial.rootMultiplicity_eq_natTrailingDegree',
        Brown.natTrailingDegree_reflect hψ_ne hψ_deg, natDegree_taylor]
    have hdeg_le : (specialize f q).natDegree ≤ f.natDegree :=
      Polynomial.natDegree_map_le
    have hmult_le : mult i₀ ≤ f.natDegree := by omega
    omega
  refine ⟨N₁ ∩ O, hN₁_open.inter hO_open, ⟨hpN₁, hpO⟩, ?_⟩
  intro q hq
  rw [key q hq, key p ⟨hp, hpN₁, hpO⟩]

/-- **Generalized Brown, pipeline form** (Corollary 5.3 / Theorem 5.5 of
`thesis/brown_pipeline_direct.tex`).  A single elimination-ideal membership
`C P ∈ ⟨f, f'⟩`, with `P ≠ 0` and both `P` and `lc f` order-invariant on the
connected analytic submanifold `S`, forces `f` to be degree-invariant on `S`. -/
theorem brown_generalized
    (k : Nat)
    (f : PolyR k)
    (P : MvPolynomial (Fin k) ℝ)
    (P_ne_zero : P ≠ 0)
    (hP_mem₁ : Polynomial.C P ∈
      Ideal.span ({ f, f.derivative } : Set (PolyR k)))
    (pos_deg : 0 < f.natDegree)
    (S : Set (Fin k → ℝ))
    (hS : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (h_ord : OrderInvariantMv P S)
    (h_ord_lc : OrderInvariantMv f.leadingCoeff S)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    : DegreeInvariant f S := by
  classical
  rcases lc_dichotomy f.leadingCoeff S h_ord_lc with h_lc | h_lc_ne
  · -- hard case: `lc f ≡ 0` on `S`
    -- the specialized degree is locally constant on `S` ...
    have hloc : ∀ p ∈ S, ∃ N : Set (Fin k → ℝ), IsOpen N ∧ p ∈ N ∧
        ∀ q ∈ S ∩ N, (specialize f q).natDegree = (specialize f p).natDegree :=
      fun p hp => brown_degree_locally_constant k f P P_ne_zero hP_mem₁ pos_deg
        S hS h_ord h_ord_lc h_lc hspec_ne p hp
    -- ... hence (by connectedness) globally constant
    have hcont : ContinuousOn (fun q => (specialize f q).natDegree) S := by
      intro p hp
      rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
      obtain ⟨N, hN_open, hpN, hconst⟩ := hloc p hp
      exact Filter.mem_of_superset (inter_mem_nhdsWithin S (hN_open.mem_nhds hpN))
        fun q hq => hconst q ⟨hq.1, hq.2⟩
    intro a ha b hb
    exact hS_conn.isPreconnected.constant hcont ha hb
  · -- easy case: `lc f` is nowhere zero on `S`, so the degree is constantly `deg f`
    intro a ha b hb
    show (f.map (evalBase a)).natDegree = (f.map (evalBase b)).natDegree
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne a ha),
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne b hb)]

#print axioms brown_generalized

open Polynomial in
/-- **Brown's Theorem 3.1** (original form, with the discriminant as witness),
recovered from the pipeline form `brown_generalized` with `P = f.discr`.  Now
needs only Fact A (`Brown.discr_mem_span`: `C (disc f) ∈ ⟨f, f'⟩`) — the reverse
membership (Brown's Lemma 8.1) is no longer required — and `lc f` order-invariant
(as holds on the cells of a CAD). -/
theorem brown_original
    (k : Nat)
    (f : PolyR k)
    (pos_deg : 0 < f.natDegree)
    (discr_ne_zero : f.discr ≠ 0)
    (S : Set (Fin k → ℝ))
    (hS : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (h_ord : OrderInvariantMv f.discr S)
    (h_ord_lc : OrderInvariantMv f.leadingCoeff S)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    : DegreeInvariant f S := by
  classical
  have hn_unit : ∀ m : ℕ, m ≠ 0 → IsUnit ((m : MvPolynomial (Fin k) ℝ)) := by
    intro m hm
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial (Fin k) ℝ) m]
    exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hm))
  rcases Nat.lt_or_ge f.natDegree 2 with hn1 | hn2
  · -- `natDegree f = 1`: direct dichotomy on `lc f`
    have hn1' : f.natDegree = 1 := by omega
    have hlc_eq : f.leadingCoeff = f.coeff 1 := by rw [← Polynomial.coeff_natDegree, hn1']
    rcases lc_dichotomy f.leadingCoeff S h_ord_lc with h_lc | h_lc_ne
    · -- `lc f ≡ 0`: the specialized degree is constantly `0`
      have hdeg0 : ∀ x ∈ S, (specialize f x).natDegree = 0 := by
        intro x hx
        apply Nat.le_zero.mp
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        show (f.map (evalBase x)).coeff m = 0
        rw [Polynomial.coeff_map]
        by_cases hm1 : m = 1
        · rw [hm1, ← hlc_eq]; exact h_lc x hx
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
      intro a ha b hb
      rw [hdeg0 a ha, hdeg0 b hb]
    · -- `lc f` nowhere zero: the specialized degree is constantly `1`
      intro a ha b hb
      show (f.map (evalBase a)).natDegree = (f.map (evalBase b)).natDegree
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne a ha),
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne b hb)]
  · -- `natDegree f ≥ 2`: apply `brown_generalized` with `P = f.discr` (Fact A only)
    have mem1 : Polynomial.C f.discr ∈
        Ideal.span ({f, f.derivative} : Set (PolyR k)) :=
      Brown.discr_mem_span f (by omega) (hn_unit _ (by omega))
    exact brown_generalized k f f.discr discr_ne_zero mem1 pos_deg S hS hS_conn h_ord
      h_ord_lc hspec_ne

#print axioms brown_original
