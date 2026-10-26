import HigherDimLFPPAS.Signed.LFPP
import HigherDimLFPPAS.Signed.Sec4
import HigherDimLQGMetric.Sec4.LfppScaleProb
import HigherDimLQGMetric.Sharp.TightWeak

/-!
# LFPP shell bounds from (1.6), for signed seeds (packet C27; MA3 P9 (b))

[3] Lemma 4.3 obtains the LFPP half of its shell events (4.5) from the tightness of `{𝔞_δ⁻¹ D^δ}` over all
`δ ∈ (0, 1)` (Ding–Gwynne–Zhuang, `κ ≥ 0`). For a signed seed the paper's Assumption 1.1 (v), (1.6), replaces it
(MA3 S2, Details P9): only `δ = ε/r → 0` is needed. On the canonical space `(DistRd d, normLGFLaw d)`, (1.6) and the
off-diagonal lower bound and modulus of the limit `D` (the weak-metric tightness `IsWeakExpMetric.scaledLowerOffDiag`,
`scaledModulus` at scale `1`, centre `0`) give the same two uniform estimates for `𝔞_δ⁻¹ D^δ` for all small `δ`:

* `c27_lfpp_lowerOffDiag`: on a compact off-diagonal set, `𝔞_δ⁻¹ D^δ > s` with probability `> 1 − θ`;
* `c27_lfpp_modulus`: a uniform Euclidean modulus on a compact set.

These replace `TightOver.lower_offDiag`/`TightOver.modulus` in the host's `l9b_lfpp_across_lower`,
`l9b_lfpp_diam_upper`, whose proofs are then copied (`c27_lfpp_across_lower`, `c27_lfpp_diam_upper`), and the
scaling transfer of `HigherDimLQGMetric.Sec4.LfppScaleProb` carries them to every centre and every scale `r` with
`ε / r < δ₀` (`c27_lfpp_across_prob`, `c27_lfpp_diam_prob`). No sign condition on the seed is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Coarse

open HigherDimLQGMetric HigherDimLFPPAS.Signed
open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined lfppLength)

variable {d : ℕ}

/-- (1.6) on a compact set: for `η > 0`, `θ > 0`, eventually `|X_i − Y| < η` on `A` outside probability `θ`. -/
theorem c27_conv_close {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → Rd d × Rd d → ℝ} {l : Filter ι} {Y : Ω → Rd d × Rd d → ℝ}
    (hconv : TendstoInProbLU P X l Y) {A : Set (Rd d × Rd d)} (hA : IsCompact A)
    {η : ℝ} (hη : 0 < η) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∀ᶠ i in l, P {ω | ¬ ∀ p ∈ A, |X i ω p - Y ω p| < η} < θ := by
  obtain ⟨R₀, hR₀⟩ := hA.isBounded.subset_closedBall (0 : Rd d × Rd d)
  set R : ℝ := max R₀ 1 with hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hAR : A ⊆ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R := by
    intro p hp
    have hp' : ‖p‖ ≤ R₀ := by
      have := hR₀ hp
      rwa [mem_closedBall, dist_zero_right] at this
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact (norm_fst_le p).trans (hp'.trans (le_max_left _ _))
    · rw [mem_closedBall, dist_zero_right]
      exact (norm_snd_le p).trans (hp'.trans (le_max_left _ _))
  filter_upwards [(hconv R hR0 η hη).eventually (gt_mem_nhds hθ)] with i hi
  refine lt_of_le_of_lt (measure_mono fun ω hω => ?_) hi
  simp only [mem_ofPred_eq, not_forall, not_lt] at hω ⊢
  obtain ⟨p, hpA, hp⟩ := hω
  refine le_trans ?_ (le_biSup (fun p => edist (X i ω p) (Y ω p)) (hAR hpA))
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hp

/-- The sharp weak normalization at scale `1`, centre `0`, of a normalized field is the metric itself. -/
theorem c27_scaledField_one {ξ Q : ℝ} {D : DistRd d → ContMetric d} {g : DistRd d}
    (hg : sphereAvg g 1 0 = 0) (p : Rd d × Rd d) :
    scaledField ξ D (fun r => r ^ (ξ * Q)) 1 0 g p = (D g).1 p := by
  rw [scaledField_apply, hg, Real.one_rpow, inv_one, mul_zero, Real.exp_zero, mul_one, one_mul,
    one_smul, one_smul, add_zero, add_zero]

/-- **Off-diagonal lower bound for the normalized LFPP, small `δ`** (from (1.6); replaces
`TightOver.lower_offDiag`). -/
theorem c27_lfpp_lowerOffDiag (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ}
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {A : Set (Rd d × Rd d)} (hA : IsCompact A) (hAd : ∀ p ∈ A, p.1 ≠ p.2)
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ s : ℝ, 0 < s ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), normLGFLaw d
      {g | ¬ ∀ p ∈ A, s < ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hN := l9b_normLGFLaw_normalized hd
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  obtain ⟨a, ha, H⟩ := IsWeakExpMetric.scaledLowerOffDiag hD hd hA hAd hθ2
  have H1 := H (normLGFLaw d) id hN.1 1 one_pos 0
  refine ⟨a / 2, half_pos ha, ?_⟩
  filter_upwards [c27_conv_close hconv hA (half_pos ha) hθ2] with δ hδ
  calc normLGFLaw d {g | ¬ ∀ p ∈ A, a / 2 < ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p}
      ≤ normLGFLaw d ({g | ¬ ∀ p ∈ A, a < scaledField ξ D (fun r => r ^ (ξ * Q)) 1 0 (id g) p} ∪
          {g | ¬ ∀ p ∈ A, |((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p - (D g).1 p| < a / 2}) := by
        refine measure_mono_ae ?_
        filter_upwards [hN.2] with g hg0 hbad
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
        apply hbad
        intro p hp
        have h1 : a < scaledField ξ D (fun r => r ^ (ξ * Q)) 1 0 g p := hnot.1 p hp
        have h2 := (abs_lt.1 (hnot.2 p hp)).1
        rw [c27_scaledField_one (g := g) hg0] at h1
        linarith
    _ ≤ _ := measure_union_le _ _
    _ < θ / 2 + θ / 2 := ENNReal.add_lt_add H1 hδ
    _ = θ := ENNReal.add_halves θ

/-- **Uniform modulus for the normalized LFPP, small `δ`** (from (1.6); replaces `TightOver.modulus`). -/
theorem c27_lfpp_modulus (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ}
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {K : Set (Rd d)} (hK : IsCompact K) {a : ℝ} (ha : 0 < a) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), normLGFLaw d
      {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) (u, v) < a} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hN := l9b_normLGFLaw_normalized hd
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  obtain ⟨b, hb, H⟩ := IsWeakExpMetric.scaledModulus hD hd hK (half_pos ha) hθ2
  have H1 := H (normLGFLaw d) id hN.1 1 one_pos 0
  refine ⟨b, hb, ?_⟩
  filter_upwards [c27_conv_close hconv (hK.prod hK) (half_pos ha) hθ2] with δ hδ
  calc normLGFLaw d
        {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) (u, v) < a}
      ≤ normLGFLaw d ({g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
            scaledField ξ D (fun r => r ^ (ξ * Q)) 1 0 (id g) (u, v) < a / 2} ∪
          {g | ¬ ∀ p ∈ K ×ˢ K, |((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p - (D g).1 p| < a / 2}) := by
        refine measure_mono_ae ?_
        filter_upwards [hN.2] with g hg0 hbad
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
        apply hbad
        intro u hu v hv huv
        have h1 : scaledField ξ D (fun r => r ^ (ξ * Q)) 1 0 g (u, v) < a / 2 :=
          hnot.1 u hu v hv huv
        have h2 := (abs_lt.1 (hnot.2 (u, v) ⟨hu, hv⟩)).2
        rw [c27_scaledField_one (g := g) hg0] at h1
        linarith
    _ ≤ _ := measure_union_le _ _
    _ < θ / 2 + θ / 2 := ENNReal.add_lt_add H1 hδ
    _ = θ := ENNReal.add_halves θ

/-! ## Shell quantities on the canonical space (copies of `l9b_lfpp_across_lower`, `l9b_lfpp_diam_upper`) -/

/-- **LFPP across lower bound, small `δ`**: for `0 < a < b` and `θ > 0` there is `c > 0` with
`normLGFLaw{D^δ(∂B_a, ∂B_b) < c 𝔞_δ} < θ` for all small `δ` (host `l9b_lfpp_across_lower`, tightness replaced by
(1.6)). -/
theorem c27_lfpp_across_lower (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), normLGFLaw d {g |
      DGZ.lfppSetDist ξ (convMollify κ δ g) univ (sphere 0 a) (sphere 0 b) < c * aEps κ ξ δ} < θ := by
  have hOff : ∀ p : Rd d × Rd d, p ∈ sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) b → p.1 ≠ p.2 := by
    intro p hp heq
    have h1 : dist p.1 (0 : Rd d) = a := hp.1
    have h2 : dist p.2 (0 : Rd d) = b := hp.2
    rw [heq] at h1
    linarith
  obtain ⟨s, hs, H⟩ := c27_lfpp_lowerOffDiag hd hD hconv ((isCompact_sphere (0 : Rd d) a).prod
    (isCompact_sphere 0 b)) hOff hθ
  refine ⟨s, hs, ?_⟩
  filter_upwards [H, self_mem_nhdsWithin] with δ hδ hδ0
  have hpos' : 0 < aEps κ ξ δ := l10a_aEps_pos_seed hd hκ ξ hδ0
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  have hA : (sphere (0 : Rd d) a).Nonempty := NormedSpace.sphere_nonempty.2 ha.le
  have hB : (sphere (0 : Rd d) b).Nonempty := NormedSpace.sphere_nonempty.2 (ha.trans hab).le
  refine lt_of_le_of_lt (measure_mono ?_) hδ
  intro g hbad hgood
  have hle : s * aEps κ ξ δ ≤
      DGZ.lfppSetDist ξ (convMollify κ δ g) univ (sphere 0 a) (sphere 0 b) := by
    refine DGZ.le_lfppSetDist hA hB fun u hu v hv => ?_
    have h : s < (aEps κ ξ δ)⁻¹ * DGZ.lfppMetric ξ (convMollify κ δ g) u v := hgood (u, v) ⟨hu, hv⟩
    have := (lt_inv_mul_iff₀ hpos').1 h
    rw [mul_comm]
    exact this.le
  exact (not_lt.2 hle) hbad

/-- **LFPP sphere-diameter upper bound, small `δ`** (piecewise-`C¹` internal distances): for `θ > 0` there is
`C > 0` with `normLGFLaw{diam_{A_{1/2,2}}(∂B_1) > C 𝔞_δ} < θ` for all small `δ` (host `l9b_lfpp_diam_upper`,
tightness replaced by (1.6)). -/
theorem c27_lfpp_diam_upper (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), normLGFLaw d {g |
      C * aEps κ ξ δ < DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2)} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  obtain ⟨s, hs, Hsep⟩ := c27_lfpp_lowerOffDiag hd hD hconv
    ((isCompact_sphere (0 : Rd d) 1).prod compact_frontier_unit_ann) sphere_frontier_offDiag hθ2
  obtain ⟨b, hb, Hmod⟩ := c27_lfpp_modulus hd hD hconv (isCompact_sphere (0 : Rd d) 1) hs hθ2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    (isCompact_sphere (0 : Rd d) 1) (isConnected_unit_sphere hd) hb
  refine ⟨(N + 1) * s, by positivity, ?_⟩
  filter_upwards [Hsep, Hmod, self_mem_nhdsWithin] with δ hsepδ hmodδ hδ
  have hV : IsOpen V := isOpen_ann _ _ _
  have hVc : IsPreconnected V := (config_isConnected_ann hd 0 (by norm_num) (by norm_num)).2
  have hKV : K ⊆ V := unit_sphere_subset_ann
  have hpos' : 0 < aEps κ ξ δ := l10a_aEps_pos_seed hd hκ ξ hδ
  have hgood : ∀ g : DistRd d, Continuous (convMollify κ δ g) →
      (∀ p ∈ K ×ˢ frontier V, s < ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p) →
      (∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) (u, v) < s) →
      DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2) ≤
        (N + 1) * s * aEps κ ξ δ := by
    intro g hg hsep hmod
    set φ := convMollify κ δ g with hφdef
    -- short steps: internal distance at most `s 𝔞_δ`
    have hshort : ∀ x y, sharpShortStep K b x y →
        fieldDistIn ξ φ V x y ≤ ENNReal.ofReal (s * aEps κ ξ δ) := by
      intro x y hxy
      have hxV : x ∈ V := hKV hxy.1
      have hD' : DGZ.lfppMetric ξ φ x y < s * aEps κ ξ δ := by
        have h : (aEps κ ξ δ)⁻¹ * DGZ.lfppMetric ξ φ x y < s :=
          hmod x hxy.1 y hxy.2.1 (by rw [← dist_eq_norm]; exact hxy.2.2.le)
        rw [mul_comm]
        exact (inv_mul_lt_iff₀ hpos').1 h
      have hfr : ∀ w ∈ frontier V, s * aEps κ ξ δ ≤ DGZ.lfppMetric ξ φ x w := by
        intro w hw
        have h : s < (aEps κ ξ δ)⁻¹ * DGZ.lfppMetric ξ φ x w := hsep (x, w) ⟨hxy.1, hw⟩
        rw [mul_comm]
        exact ((lt_inv_mul_iff₀ hpos').1 h).le
      obtain ⟨hj, hle⟩ := l9b_lfppDistOn_le_of_frontier hg hV hxV hD' hfr
      rw [fieldDistIn_eq_ofReal hg hj]
      exact ENNReal.ofReal_le_ofReal (hle.trans hD'.le)
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
      ≤ normLGFLaw d ({g | ¬ ∀ p ∈ K ×ˢ frontier V, s < ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p} ∪
          {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
            ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) (u, v) < s}) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_canonical_cont_seed hd hκ hδ] with g hg hbad
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
        exact (not_lt.2 (hgood g hg hnot.1 hnot.2)) hbad
    _ ≤ normLGFLaw d {g | ¬ ∀ p ∈ K ×ˢ frontier V, s < ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) p} +
        normLGFLaw d {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g) (u, v) < s} :=
      measure_union_le _ _
    _ < θ / 2 + θ / 2 := ENNReal.add_lt_add hsepδ hmodδ
    _ = θ := ENNReal.add_halves θ

/-! ## Every centre and every scale with `ε / r` small (copy of `HigherDimLQGMetric.Sec4.LfppScaleProb`) -/

/-- **LFPP across lower bound at every scale** with `ε / r < δ₀`: for `0 < a < b`, `θ > 0` there are `c > 0`,
`δ₀ > 0` with `P[D^ε_h(∂B_{ar}(u), ∂B_{br}(u)) < c r 𝔞_{ε/r} e^{ξ h_r(u)}] < θ` for every normalized LGF. -/
theorem c27_lfpp_across_prob (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε r : ℝ, 0 < ε → 0 < r → ε / r < δ₀ → ∀ u : Rd d,
        P {ω | DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (a * r))
          (sphere u (b * r)) < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)} < θ := by
  obtain ⟨c, hc, H⟩ := c27_lfpp_across_lower hd hD hκ hconv ha hab hθ
  obtain ⟨δ₀, hδ₀, Hδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 H
  refine ⟨c, hc, δ₀, hδ₀, ?_⟩
  intro Ω _ P _ h hh ε r hε hr hεr u
  have hδ : ε / r ∈ Ioo (0 : ℝ) δ₀ := ⟨div_pos hε hr, hεr⟩
  have hN := isNormalizedLGF_recentAff hd hh.1 hr u
  let A : Set (DistRd d) := {g | DGZ.lfppSetDist ξ (convMollify κ (ε / r) g) univ
    (sphere 0 a) (sphere 0 b) < c * aEps κ ξ (ε / r)}
  calc P {ω | DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (a * r))
        (sphere u (b * r)) < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)}
      ≤ P ((fun ω => recentAff r u (h ω)) ⁻¹' A) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_ae_convMollify_affine_seed hd hκ hh u hr] with ω ⟨hsc, hc'⟩ hbad
        have hid : ∀ x, convMollify κ ε (h ω) (u + r • x) =
            convMollify κ (ε / r) (recentAff r u (h ω)) x +
              sphereAvg (affineComp r u (h ω)) 1 0 := hsc ε hε
        have hscale := l9b_lfppSetDist_affine (ξ := ξ) hr hid univ (sphere 0 a) (sphere 0 b)
        rw [l9b_image_affine_univ hr, l9b_image_affine_sphere hr, l9b_image_affine_sphere hr,
          mul_comm r a, mul_comm r b, hc'] at hscale
        have hbad' : DGZ.lfppSetDist ξ (convMollify κ ε (h ω)) univ (sphere u (a * r))
            (sphere u (b * r)) < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) :=
          hbad
        rw [hscale] at hbad'
        show DGZ.lfppSetDist ξ (convMollify κ (ε / r) (recentAff r u (h ω))) univ
          (sphere 0 a) (sphere 0 b) < c * aEps κ ξ (ε / r)
        have hk : 0 < r * Real.exp (ξ * sphereAvg (h ω) r u) := by positivity
        have : r * Real.exp (ξ * sphereAvg (h ω) r u) *
            DGZ.lfppSetDist ξ (convMollify κ (ε / r) (recentAff r u (h ω))) univ (sphere 0 a)
              (sphere 0 b) < r * Real.exp (ξ * sphereAvg (h ω) r u) * (c * aEps κ ξ (ε / r)) := by
          calc _ < c * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) := hbad'
            _ = _ := by ring
        exact lt_of_mul_lt_mul_left this hk.le
    _ ≤ normLGFLaw d A := l9b_preimage_le_normLGFLaw hd hN A
    _ < θ := Hδ hδ

/-- **LFPP sphere-diameter upper bound at every scale** with `ε / r < δ₀` (piecewise-`C¹` internal distances):
for `θ > 0` there are `C > 0`, `δ₀ > 0` with
`P[diam_{A_{r/2,2r}(u)}(∂B_r(u); D^ε) > C r 𝔞_{ε/r} e^{ξ h_r(u)}] < θ` for every normalized LGF. -/
theorem c27_lfpp_diam_prob (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε r : ℝ, 0 < ε → 0 < r → ε / r < δ₀ → ∀ u : Rd d,
        P {ω | C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
          DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r))} < θ := by
  obtain ⟨C, hC, H⟩ := c27_lfpp_diam_upper hd hD hκ hconv hθ
  obtain ⟨δ₀, hδ₀, Hδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 H
  refine ⟨C, hC, δ₀, hδ₀, ?_⟩
  intro Ω _ P _ h hh ε r hε hr hεr u
  have hδ : ε / r ∈ Ioo (0 : ℝ) δ₀ := ⟨div_pos hε hr, hεr⟩
  have hN := isNormalizedLGF_recentAff hd hh.1 hr u
  let A : Set (DistRd d) := {g | C * aEps κ ξ (ε / r) <
    DGZ.lfppDiam ξ (convMollify κ (ε / r) g) (sphere 0 1) (ann 0 (1 / 2) 2)}
  calc P {ω | C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
        DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r))}
      ≤ P ((fun ω => recentAff r u (h ω)) ⁻¹' A) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_ae_convMollify_affine_seed hd hκ hh u hr] with ω ⟨hsc, hc'⟩ hbad
        have hid : ∀ x, convMollify κ ε (h ω) (u + r • x) =
            convMollify κ (ε / r) (recentAff r u (h ω)) x +
              sphereAvg (affineComp r u (h ω)) 1 0 := hsc ε hε
        have hscale := l9b_lfppDiam_affine (ξ := ξ) hr hid (sphere 0 1) (ann 0 (1 / 2) 2)
        rw [l9b_image_affine_sphere hr, l9b_image_affine_ann hr, mul_one,
          show r * (1 / 2) = r / 2 by ring, mul_comm r 2, hc'] at hscale
        have hbad' : C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) <
            DGZ.lfppDiam ξ (convMollify κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r)) := hbad
        rw [hscale] at hbad'
        show C * aEps κ ξ (ε / r) < DGZ.lfppDiam ξ (convMollify κ (ε / r) (recentAff r u (h ω)))
          (sphere 0 1) (ann 0 (1 / 2) 2)
        have hk : 0 < r * Real.exp (ξ * sphereAvg (h ω) r u) := by positivity
        have : r * Real.exp (ξ * sphereAvg (h ω) r u) * (C * aEps κ ξ (ε / r)) <
            r * Real.exp (ξ * sphereAvg (h ω) r u) * DGZ.lfppDiam ξ
              (convMollify κ (ε / r) (recentAff r u (h ω))) (sphere 0 1) (ann 0 (1 / 2) 2) := by
          calc _ = C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) := by ring
            _ < _ := hbad'
        exact lt_of_mul_lt_mul_left this hk.le
    _ ≤ normLGFLaw d A := l9b_preimage_le_normLGFLaw hd hN A
    _ < θ := Hδ hδ

end HigherDimLFPPAS.Coarse
