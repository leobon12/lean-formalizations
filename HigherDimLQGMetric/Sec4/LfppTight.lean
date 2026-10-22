import HigherDimLQGMetric.Sec4.Scale
import HigherDimLQGMetric.Sec4.Basic
import HigherDimLQGMetric.Sharp.TightShell
import HigherDimLQGMetric.Main.ExponentBridge
import HigherDimLQGMetric.Config.Geometry
import HigherDimLQGMetric.DGZ.FunctionalsMeas
import HigherDimLQGMetric.Weak.DetLFPPMetric

/-!
# Shell quantities of the normalized LFPP (packet L9b; MA6 P2 for the LFPP family, [1] Lemma 4.3 (3)–(4))

From the corrected [1] Lemma 3.3 (`L6a_tight`, B3 interface; its B2 premise is discharged by `DGZHyp` at
`Q = distExp d ξ` (L10a's `l10a_dgzHyp`) and the adapter `hB2`): on the canonical space
`(DistRd d, normLGFLaw d)` the laws of `𝔞_δ⁻¹ D^δ_h`, `δ ∈ (0,1)`, are tight with continuous-metric limits.
MA6 P2 (W1's generic `TightOver` lemmas) then gives, uniformly in `δ ∈ (0,1)`:

* `l9b_lfpp_across_lower`: the LFPP distance between the spheres `∂B_a(0)`, `∂B_b(0)` is `≥ c 𝔞_δ` with high
  probability;
* `l9b_lfpp_diam_upper`: the internal LFPP diameter of `∂B_1(0)` inside `A_{1/2,2}(0)` (piecewise-`C¹` paths)
  is `≤ C 𝔞_δ` with high probability — by the deterministic confinement `l9b_lfppDistOn_le_of_frontier`
  (MA6 P2's `Ψ_η < Φ′` argument, for LFPP paths) and W1's uniform chain count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined lfppLength)

variable {d : ℕ}

/-! ## The B2 premise and the canonical tight family -/

/-- the B2 → B3 premise of the B3 interfaces at `Q = distExp d ξ` -/
theorem l9b_dgzPremise (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) :
    ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q :=
  ⟨distExp d ξ, l10a_dgzHyp hd hκ hξ hsub, hB2 d κ ξ _⟩

/-- the normalized LFPP metrics as random continuous functions on the canonical space -/
def lfppX (κ : Rd d → ℝ) (ξ δ : ℝ) (g : DistRd d) : C(Rd d × Rd d, ℝ) :=
  toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)

/-- **[1] Lemma 3.3** on the canonical space (from the B3 interface `L6a_tight`). -/
theorem l9b_lfpp_tight (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) :
    (∀ δ ∈ Ioo (0 : ℝ) 1, 0 < aEps κ ξ δ) ∧
      TightOver (normLGFLaw d) (fun δ g => lfppX κ ξ δ g) (Ioo 0 1) := by
  have := l9b_normLGFLaw_prob hd
  obtain ⟨hpos, hm, ht, hlim⟩ := hL6a d ξ κ (l9b_dgzPremise hB2 hd hκ hξ hsub) (normLGFLaw d) id
    (l9b_normLGFLaw_normalized hd).1.isLGFPlusBddCont
  exact ⟨hpos, hm, ht, fun μ hμ => (hlim μ hμ).mono fun D hD => hD.1⟩

theorem l9b_lfppX_apply {κ : Rd d → ℝ} {ξ δ : ℝ} {g : DistRd d}
    (hφ : Continuous (convMollify κ δ g)) (p : Rd d × Rd d) :
    lfppX κ ξ δ g p = (aEps κ ξ δ)⁻¹ * DGZ.lfppMetric ξ (convMollify κ δ g) p.1 p.2 := by
  have hc : Continuous ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) :=
    (DGZ.continuous_lfppMetric hφ ξ).const_smul _
  rw [lfppX, toCMapRd_apply_of_continuous hc]
  rfl

/-- a.s. continuity of the convolution field on the canonical space -/
theorem l9b_canonical_cont (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᵐ g ∂(normLGFLaw d), Continuous (convMollify κ δ g) := by
  have := l9b_normLGFLaw_prob hd
  filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ (normLGFLaw d) id
    (l9b_normLGFLaw_normalized hd)] with g hg
  have hc : Continuous fun z : Rd d => (δ, z) := continuous_const.prodMk continuous_id
  have hf := hg.comp_continuous hc (fun _ => ⟨hδ, mem_univ _⟩)
  simpa only [Function.comp_def, id] using hf

/-! ## Deterministic confinement of short LFPP paths -/

/-- a path starting in an open set and leaving it hits the frontier -/
theorem l9b_exists_frontier_hit {γ : ℝ → Rd d} (hγ : ContinuousOn γ (Icc 0 1))
    {V : Set (Rd d)} (hV : IsOpen V) (h0 : γ 0 ∈ V) (hout : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∉ V) :
    ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ frontier V := by
  set S : Set ℝ := Icc 0 1 ∩ γ ⁻¹' Vᶜ with hS
  have hSc : IsClosed S := hγ.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl
  obtain ⟨t₀, ht₀⟩ := hout
  have hne : S.Nonempty := ⟨t₀, ht₀.1, ht₀.2⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf S with ht₁
  have ht₁S : t₁ ∈ S := hSc.csInf_mem hne hSb
  have hbefore : ∀ t ∈ Ico 0 t₁, γ t ∈ V := by
    intro t ht
    by_contra hcon
    have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans ht₁S.1.2⟩, hcon⟩
    exact absurd (csInf_le hSb htS) (not_le.2 ht.2)
  have ht₁0 : 0 < t₁ := by
    rcases ht₁S.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := ht₁S.2
      rw [← h] at h'
      exact h' h0
  refine ⟨t₁, ht₁S.1, ?_⟩
  rw [hV.frontier_eq]
  refine ⟨?_, ht₁S.2⟩
  have hcw : ContinuousWithinAt γ (Ico 0 t₁) t₁ :=
    (hγ t₁ ht₁S.1).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht₁S.1.2))
  have hmem := hcw.mem_closure_image (by rw [closure_Ico ht₁0.ne]; exact right_mem_Icc.2 ht₁0.le)
  exact closure_mono (image_subset_iff.2 fun t ht => hbefore t ht) hmem

/-- **Confinement** (LFPP form of MA6 P2): if `D(x, y) < a ≤ D(x, w)` for all `w ∈ ∂V` (`D` the whole-space
LFPP metric of a continuous field, `x ∈ V` open), then `x, y` are joined in `V` and `D_V(x, y) ≤ D(x, y)`. -/
theorem l9b_lfppDistOn_le_of_frontier {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {V : Set (Rd d)} (hV : IsOpen V) {x y : Rd d} (hx : x ∈ V) {a : ℝ}
    (hxy : DGZ.lfppMetric ξ φ x y < a) (hfr : ∀ w ∈ frontier V, a ≤ DGZ.lfppMetric ξ φ x w) :
    PcwJoined V x y ∧ lfppDistOn ξ φ V x y ≤ DGZ.lfppMetric ξ φ x y := by
  have key : ∀ c, DGZ.lfppMetric ξ φ x y < c → c ≤ a →
      ∃ γ : ℝ → Rd d, HigherDimLFPP.IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V ∧
        lfppLength ξ φ γ < c := by
    intro c hc hca
    obtain ⟨γ, hγ, -, hlen⟩ := HigherDimLFPP.exists_lfppLength_lt (DGZ.pcwJoined_univ x y) hc
    refine ⟨γ, hγ, ?_, hlen⟩
    by_contra hmaps
    have hout : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∉ V := by
      by_contra hno
      push Not at hno
      exact hmaps hno
    obtain ⟨t, ht, hfront⟩ := l9b_exists_frontier_hit hγ.continuousOn hV
      (by rw [hγ.source]; exact hx) hout
    have h1 : DGZ.lfppMetric ξ φ x (γ t) ≤ ∫ s in (0 : ℝ)..t, HigherDimLFPP.lfppIntegrand ξ φ γ s := by
      have := DGZ.lfppDistOn_le_integral (ξ := ξ) (φ := φ) (W := univ) hγ le_rfl ht.1 ht.2
        (fun _ _ => mem_univ _)
      rwa [hγ.source] at this
    have h2 := DGZ.integral_le_lfppLength (ξ := ξ) hφ hγ le_rfl ht.1 ht.2
    linarith [hfr _ hfront]
  have hlt : DGZ.lfppMetric ξ φ x y < a := hxy
  obtain ⟨γ₀, hγ₀, hγ₀V, -⟩ := key a hxy le_rfl
  refine ⟨⟨γ₀, hγ₀, hγ₀V⟩, le_of_forall_gt_imp_ge_of_dense fun c hc => ?_⟩
  obtain ⟨γ, hγ, hγV, hlen⟩ := key (min c a) (lt_min hc hlt) (min_le_right _ _)
  exact ((HigherDimLFPP.lfppDistOn_le_lfppLength hγ hγV).trans hlen.le).trans (min_le_left _ _)

/-! ## Uniform shell bounds on the canonical space -/

section Canonical

variable {κ : Rd d → ℝ} {ξ : ℝ}

/-- **Across lower bound** (MA6 P2, LFPP family): for `0 < a < b` and `θ > 0` there is `c > 0` with
`normLGFLaw{D^δ(∂B_a, ∂B_b) < c 𝔞_δ} < θ` for every `δ ∈ (0,1)`. -/
theorem l9b_lfpp_across_lower (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hpos : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < aEps κ ξ δ)
    (hT : TightOver (normLGFLaw d) (fun δ g => lfppX κ ξ δ g) (Ioo 0 1))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, normLGFLaw d {g |
      DGZ.lfppSetDist ξ (convMollify κ δ g) univ (sphere 0 a) (sphere 0 b) < c * aEps κ ξ δ} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hOff : ∀ p : Rd d × Rd d, p ∈ sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) b → p.1 ≠ p.2 := by
    intro p hp heq
    have h1 : dist p.1 (0 : Rd d) = a := hp.1
    have h2 : dist p.2 (0 : Rd d) = b := hp.2
    rw [heq] at h1
    linarith
  obtain ⟨s, hs, H⟩ := hT.lower_offDiag ((isCompact_sphere (0 : Rd d) a).prod
    (isCompact_sphere 0 b)) hOff hθ
  refine ⟨s, hs, fun δ hδ => ?_⟩
  refine lt_of_le_of_lt (measure_mono_ae ?_) (H δ hδ)
  filter_upwards [l9b_canonical_cont hd hκ hδ.1] with g hg hbad hgood
  have hA : (sphere (0 : Rd d) a).Nonempty := by
    have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]; omega)
    exact NormedSpace.sphere_nonempty.2 ha.le
  have hB : (sphere (0 : Rd d) b).Nonempty := by
    have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]; omega)
    exact NormedSpace.sphere_nonempty.2 (ha.trans hab).le
  have hle : s * aEps κ ξ δ ≤
      DGZ.lfppSetDist ξ (convMollify κ δ g) univ (sphere 0 a) (sphere 0 b) := by
    refine DGZ.le_lfppSetDist hA hB fun u hu v hv => ?_
    have h := hgood (u, v) ⟨hu, hv⟩
    rw [l9b_lfppX_apply hg] at h
    have hpos' := hpos δ hδ
    have := (lt_inv_mul_iff₀ hpos').1 h
    rw [mul_comm]
    exact this.le
  exact (not_lt.2 hle) hbad

/-- **Sphere-diameter upper bound** (MA6 P2, LFPP family, piecewise-`C¹` internal distances): for `θ > 0`
there is `C > 0` with `normLGFLaw{diam_{A_{1/2,2}}(∂B_1) > C 𝔞_δ} < θ` for every `δ ∈ (0,1)`. -/
theorem l9b_lfpp_diam_upper (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hpos : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < aEps κ ξ δ)
    (hT : TightOver (normLGFLaw d) (fun δ g => lfppX κ ξ δ g) (Ioo 0 1))
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, normLGFLaw d {g |
      C * aEps κ ξ δ < DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2)} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  obtain ⟨s, hs, Hsep⟩ := hT.lower_offDiag
    ((isCompact_sphere (0 : Rd d) 1).prod compact_frontier_unit_ann)
    sphere_frontier_offDiag hθ2
  obtain ⟨b, hb, Hmod⟩ := hT.modulus (isCompact_sphere (0 : Rd d) 1) hs hθ2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    (isCompact_sphere (0 : Rd d) 1) (isConnected_unit_sphere hd) hb
  refine ⟨(N + 1) * s, by positivity, fun δ hδ => ?_⟩
  have hV : IsOpen V := isOpen_ann _ _ _
  have hVc : IsPreconnected V := (config_isConnected_ann hd 0 (by norm_num) (by norm_num)).2
  have hKV : K ⊆ V := unit_sphere_subset_ann
  have hpos' := hpos δ hδ
  have hgood : ∀ g : DistRd d, Continuous (convMollify κ δ g) →
      (∀ p ∈ K ×ˢ frontier V, s < lfppX κ ξ δ g p) →
      (∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → lfppX κ ξ δ g (u, v) < s) →
      DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2) ≤ (N + 1) * s * aEps κ ξ δ := by
    intro g hg hsep hmod
    set φ := convMollify κ δ g with hφdef
    -- short steps: internal distance at most `s 𝔞_δ`
    have hshort : ∀ x y, sharpShortStep K b x y →
        fieldDistIn ξ φ V x y ≤ ENNReal.ofReal (s * aEps κ ξ δ) := by
      intro x y hxy
      have hxV : x ∈ V := hKV hxy.1
      have hD : DGZ.lfppMetric ξ φ x y < s * aEps κ ξ δ := by
        have h := hmod x hxy.1 y hxy.2.1 (by rw [← dist_eq_norm]; exact hxy.2.2.le)
        rw [l9b_lfppX_apply hg] at h
        rw [mul_comm]
        exact (inv_mul_lt_iff₀ hpos').1 h
      have hfr : ∀ w ∈ frontier V, s * aEps κ ξ δ ≤ DGZ.lfppMetric ξ φ x w := by
        intro w hw
        have h := hsep (x, w) ⟨hxy.1, hw⟩
        rw [l9b_lfppX_apply hg] at h
        rw [mul_comm]
        exact ((lt_inv_mul_iff₀ hpos').1 h).le
      obtain ⟨hj, hle⟩ := l9b_lfppDistOn_le_of_frontier hg hV hxV hD hfr
      rw [fieldDistIn_eq_ofReal hg hj]
      exact ENNReal.ofReal_le_ofReal (hle.trans hD.le)
    have hchain : ∀ u ∈ K, ∀ v ∈ K, fieldDistIn ξ φ V u v ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (s * aEps κ ξ δ) :=
      fun u hu v hv => hN u hu v hv (fieldDistIn ξ φ V) (fun x hx => fieldDistIn_self (hKV hx))
        (fieldDistIn_triangle hg) _ hshort
    refine DGZ.lfppDiam_le (by positivity) fun u hu v hv => ?_
    have hj := DGZ.pcwJoined_of_isPreconnected hV hVc (hKV hu) (hKV hv)
    have h := hchain u hu v hv
    rw [fieldDistIn_eq_ofReal hg hj, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    calc lfppDistOn ξ φ V u v ≤ N * (s * aEps κ ξ δ) := h'
      _ ≤ (N + 1) * s * aEps κ ξ δ := by nlinarith
  calc normLGFLaw d {g | (N + 1) * s * aEps κ ξ δ <
        DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2)}
      ≤ normLGFLaw d ({g | ¬ ∀ p ∈ K ×ˢ frontier V, s < lfppX κ ξ δ g p} ∪
          {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → lfppX κ ξ δ g (u, v) < s}) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_canonical_cont hd hκ hδ.1] with g hg hbad
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
        exact (not_lt.2 (hgood g hg hnot.1 hnot.2)) hbad
    _ ≤ normLGFLaw d {g | ¬ ∀ p ∈ K ×ˢ frontier V, s < lfppX κ ξ δ g p} +
        normLGFLaw d {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → lfppX κ ξ δ g (u, v) < s} :=
      measure_union_le _ _
    _ < θ / 2 + θ / 2 := ENNReal.add_lt_add (Hsep δ hδ) (Hmod δ hδ)
    _ = θ := ENNReal.add_halves θ

end Canonical

end HigherDimLQGMetric
