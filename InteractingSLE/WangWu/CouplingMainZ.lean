import InteractingSLE.WangWu.CouplingMain

/-!
# Wang–Wu at `κ = 4`: the characteristic-function martingale of the tested frozen field (Proposition 3.7)

Packet PROVE-WW-A3. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, proof of Proposition 3.7
("`Z_t(p) = exp(i M_t(p) + ½ ⟨M(p)⟩_t)` … a complex local martingale, while `|Z_t(p)| ≤ exp(E_0(p)/2)`"), ruling R31.

For a test function `φ` (`IsTestFn`) and a bounded stopping time `σ₀ < T` of the usual augmentation, with the tested
frozen mean `m_t(φ) = ∫ φ η̄_{t∧σ₀}` and the retained energy `e_t(φ) = Q_{U_{t∧σ₀}}(φ, φ)`:

* `frozenMean_zero_eq`, `retainedGreen_zero_eq`: at time `0` the mean is `η_0` (the boundary data of the seed) and
  the kernel is `G_ℍ`, deterministically;
* `frozenMean_facts_of_goodPair`, `ae_ae_goodPair`: almost surely, for almost every `z`, `t ↦ η̄_{t∧σ₀}(z)` is
  continuous and bounded;
* `continuous_testedMean_min`: hence `t ↦ m_t(φ)` is continuous, almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WangWu

/-! ### Time zero -/

section Zero

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {bm : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- `f_0(z) = z − W_0` off the real line (QuantumZipper's `fwdMap_zero_time'`, reproved to avoid its import). -/
theorem fwdMap_zero_eq_sub (W : ℝ → ℝ) {z : ℂ} (hz : z ≠ W 0) : fwdMap W 0 z = z - W 0 := by
  have hex : ∃ u, IsForwardSol W z 0 u := by
    refine ⟨fun _ => z - W 0, continuousOn_const, fun t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    exact ⟨sub_ne_zero.2 hz, by simp⟩
  unfold fwdMap
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have := (hex.choose_spec.2 0 ⟨le_rfl, le_rfl⟩).2
  simpa using this

theorem fwdMap_rpath_zero (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) {z : ℂ} (hz : z ∈ H) :
    fwdMap (Ito.rpath w) 0 z = z := by
  have hw0 : Ito.rpath w 0 = 0 := by simpa [Ito.rpath] using hP.1
  have hne : z ≠ Ito.rpath w 0 := by
    rw [hw0]; intro h
    have him : (0 : ℝ) < z.im := hz
    rw [h] at him
    simp at him
  rw [fwdMap_zero_eq_sub _ hne, hw0]
  simp

/-- **The mean at time `0`** is the harmonic extension of the seed's boundary data. -/
theorem frozenMean_zero_eq (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) (hζ : 0 < ζ)
    {z : ℂ} (hz : z ∈ H) : frozenMean ρL ρR w vL vR 0 z = condMean ρL ρR xL xR z := by
  have hpos := swallowTime_pos_of_path hP hζ (show 0 < z.im from hz)
  have hpos' : ((0 : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath w) z := by simpa using hpos
  simp only [frozenMean, hpos', ↓reduceIte, meanAt, hP.2.1, hP.2.2.1, hP.1, sub_zero]
  have e : ((0 : ℝ≥0) : ℝ) = 0 := rfl
  rw [e, fwdMap_rpath_zero hP hz]

/-- **The kernel at time `0`** is `G_ℍ`. -/
theorem retainedGreen_zero_eq (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) (hζ : 0 < ζ)
    {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) : retainedGreen w 0 a b = greenH a b := by
  have hpa := swallowTime_pos_of_path hP hζ (show 0 < a.im from ha)
  have hpb := swallowTime_pos_of_path hP hζ (show 0 < b.im from hb)
  have hmem : (0 : ℝ) ∈ K3.vtIdx (Ito.rpath w) ((0 : ℝ≥0) : ℝ) a b :=
    ⟨le_rfl, le_rfl, by rwa [ENNReal.ofReal_zero], by rwa [ENNReal.ofReal_zero]⟩
  have hV : K3.VTe (Ito.rpath w) ((0 : ℝ≥0) : ℝ) a b = K3.vtKer (Ito.rpath w) 0 a b :=
    le_antisymm (iInf₂_le _ hmem) (le_iInf₂ fun t ht => by
      have ht0 : t = 0 := le_antisymm (by exact_mod_cast ht.2.1) ht.1
      rw [ht0])
  unfold retainedGreen K3.VT
  rw [hV, K3.vtKer, fwdMap_rpath_zero hP ha, fwdMap_rpath_zero hP hb,
    ENNReal.toReal_ofReal (greenH_nonneg (le_of_lt (show (0 : ℝ) < a.im from ha) : a ∈ Hbar)
      (le_of_lt (show (0 : ℝ) < b.im from hb) : b ∈ Hbar) hab)]

end Zero

/-! ### Frozen paths on good pairs -/

section GoodPair

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ω : Ω}

/-- On a good pair, the frozen path `t ↦ η̄_{t∧σ₀}(z)` is continuous and bounded by `M`. -/
theorem frozenMean_facts_of_goodPair
    (hP : IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω)) {σ₀ : Ω → ℝ≥0} (hσζ : (σ₀ ω : ℝ≥0∞) < ζ ω) {z : ℂ}
    (hgood : (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀) :
    Continuous (fun t => frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (min t (σ₀ ω)) z) ∧
      ∀ t, |frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
        (min t (σ₀ ω)) z| ≤ meanBound ρL ρR := by
  obtain ⟨⟨hω, hz⟩, hor⟩ := hgood
  refine frozenMean_path_facts hP hσζ hz fun hsσ => ?_
  have hsζ : swallowTime (Ito.rpath (W · ω)) z < ζ ω := lt_of_le_of_lt hsσ hσζ
  rcases hor with hq | hg
  · exfalso
    obtain ⟨q, hq1, -, -, hqζ, hsol⟩ := mem_iUnion.1 hq
    have h1 := lt_swallowTime_of_path hP hqζ hz hsol
    have h2 : (σ₀ ω : ℝ≥0∞) < ((q : ℝ).toNNReal : ℝ≥0∞) := by exact_mod_cast hq1
    exact absurd (hsσ.trans_lt (h2.trans h1)) (lt_irrefl _)
  · obtain ⟨L, hL⟩ := (guardG_iff hP hω hz hsζ).1 hg
    have he := tendsto_nhds_limUnder ⟨L, hL⟩
    have hfr : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z =
        limUnder (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
          (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z) := by
      simp only [frozenMean]
      rw [ite_eq_right_iff.2 fun h => absurd h (not_lt.2 hsσ)]
    rw [hfr]
    exact he

end GoodPair

/-! ### The tested frozen mean on a good path -/

/-- The tested frozen mean `m_t(φ) = ∫ φ(z) η̄_t(z) dz`. -/
def testedMean {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) (φ : ℂ → ℝ) : ℝ :=
  ∫ z, φ z * frozenMean ρL ρR w vL vR t z

/-- **Good paths** for the tested mean up to `σ`: a path of the chain with `σ < ζ` on which, for almost every
`z ∈ ℍ`, the frozen path `t ↦ η̄_{t∧σ}(z)` is continuous and bounded by `M`, and every `η̄_{t∧σ}` is almost
everywhere on `ℍ` a Borel function. -/
def IsGoodPath {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (bm : ℝ≥0 → ℝ) (ζ : ℝ≥0∞)
    (σ : ℝ≥0) : Prop :=
  IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ ∧ (σ : ℝ≥0∞) < ζ ∧
    (∀ᵐ z ∂(volume : Measure ℂ), z ∈ H →
      Continuous (fun t => frozenMean ρL ρR w vL vR (min t σ) z) ∧
        ∀ t, |frozenMean ρL ρR w vL vR (min t σ) z| ≤ meanBound ρL ρR) ∧
    ∀ t, ∃ g : ℂ → ℝ, Measurable g ∧ ∀ᵐ z ∂(volume : Measure ℂ), z ∈ H →
      g z = frozenMean ρL ρR w vL vR (min t σ) z

section TestedMean

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {bm : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {σ : ℝ≥0} {φ ψ : ℂ → ℝ}

theorem IsGoodPath.aestronglyMeasurable (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ)
    (hφ : IsTestFn φ) (t : ℝ≥0) :
    AEStronglyMeasurable (fun z => φ z * frozenMean ρL ρR w vL vR (min t σ) z) volume := by
  obtain ⟨g, hgm, hgeq⟩ := hg.2.2.2 t
  refine (hφ.1.measurable.mul hgm).aestronglyMeasurable.congr ?_
  filter_upwards [hgeq] with z hz
  by_cases h0 : φ z = 0
  · simp [h0]
  · simp only [Pi.mul_apply, hz (hφ.mem_H h0)]

theorem IsGoodPath.norm_le (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ) (hφ : IsTestFn φ) (t : ℝ≥0) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ‖φ z * frozenMean ρL ρR w vL vR (min t σ) z‖ ≤ |φ z| * meanBound ρL ρR := by
  filter_upwards [hg.2.2.1] with z hz
  by_cases h0 : φ z = 0
  · simp [h0]
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((hz (hφ.mem_H h0)).2 t) (abs_nonneg _)

theorem IsGoodPath.integrable (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ) (hφ : IsTestFn φ)
    (t : ℝ≥0) : Integrable (fun z => φ z * frozenMean ρL ρR w vL vR (min t σ) z) :=
  (hφ.integrable.abs.mul_const _).mono' (hg.aestronglyMeasurable hφ t) (hg.norm_le hφ t)

/-- **The tested frozen mean is continuous in time** on a good path. -/
theorem IsGoodPath.continuous_testedMean (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ)
    (hφ : IsTestFn φ) : Continuous fun t => testedMean ρL ρR w vL vR (min t σ) φ :=
  continuous_of_dominated (fun t => hg.aestronglyMeasurable hφ t) (fun t => hg.norm_le hφ t)
    (hφ.integrable.abs.mul_const _) (by
      filter_upwards [hg.2.2.1] with z hz
      by_cases h0 : φ z = 0
      · simp only [h0, zero_mul]; exact continuous_const
      · exact continuous_const.mul (hz (hφ.mem_H h0)).1)

theorem IsGoodPath.abs_testedMean_le (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ)
    (hφ : IsTestFn φ) (t : ℝ≥0) :
    |testedMean ρL ρR w vL vR (min t σ) φ| ≤ (∫ z, |φ z|) * meanBound ρL ρR := by
  rw [← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hg.integrable hφ t).abs
    (hφ.integrable.abs.mul_const _) ?_)
  filter_upwards [hg.norm_le hφ t] with z hz
  rwa [Real.norm_eq_abs] at hz

theorem IsGoodPath.testedMean_lin (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ) (hφ : IsTestFn φ)
    (hψ : IsTestFn ψ) (c d : ℝ) (t : ℝ≥0) :
    testedMean ρL ρR w vL vR (min t σ) (fun a => c * φ a + d * ψ a) =
      c * testedMean ρL ρR w vL vR (min t σ) φ + d * testedMean ρL ρR w vL vR (min t σ) ψ := by
  unfold testedMean
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hg.integrable hφ t).const_mul c)
    ((hg.integrable hψ t).const_mul d)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  ring

/-- At time `0` the tested mean is deterministic: `∫ φ η_0`. -/
theorem IsGoodPath.testedMean_zero (hg : IsGoodPath xL xR ρL ρR w vL vR bm ζ σ) (hφ : IsTestFn φ) :
    testedMean ρL ρR w vL vR (min 0 σ) φ = ∫ z, φ z * condMean ρL ρR xL xR z := by
  have hζ : 0 < ζ := lt_of_le_of_lt zero_le hg.2.1
  rw [min_eq_left zero_le]
  unfold testedMean
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases h0 : φ z = 0
  · simp [h0]
  · simp only [frozenMean_zero_eq hg.1 hζ (hφ.mem_H h0)]

/-- At time `0` the retained form is `∬ φ G_ℍ ψ`, deterministically. -/
theorem retainedGreenForm_zero (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR bm ζ) (hζ : 0 < ζ)
    (hφ : IsTestFn φ) (hψ : IsTestFn ψ) :
    retainedGreenForm w 0 φ ψ = ∫ a, ∫ b, φ a * greenH a b * ψ b := by
  have hT : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by rwa [ENNReal.coe_zero]
  have heq : (fun p : ℂ × ℂ => φ p.1 * retainedGreen w 0 p.1 p.2 * ψ p.2) =ᵐ[(volume : Measure ℂ).prod
      volume] fun p : ℂ × ℂ => φ p.1 * greenH p.1 p.2 * ψ p.2 := by
    filter_upwards [FieldMart.ae_ne_diag] with p hp
    by_cases h0 : φ p.1 = 0 ∨ ψ p.2 = 0
    · rcases h0 with h0 | h0 <;> simp [h0]
    · push Not at h0
      rw [retainedGreen_zero_eq hP hζ (hφ.mem_H h0.1) (hψ.mem_H h0.2) hp]
  have hint := (integrable_formIntegrand hP hφ hψ hT).congr heq
  rw [retainedGreenForm_eq_integral_prod hP hφ hψ hT,
    ← integral_prod (fun p : ℂ × ℂ => φ p.1 * greenH p.1 p.2 * ψ p.2) hint]
  exact integral_congr_ae heq

end TestedMean

/-! ### Good paths are almost sure -/

section AeGood

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Almost every path is good** for a bounded stopping time `σ₀ < T` of the usual augmentation. -/
theorem ae_isGoodPath [IsProbabilityMeasure P] (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {σ₀ : Ω → ℝ≥0} (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N) :
    ∀ᵐ ω ∂P, IsGoodPath xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (B · ω)
      (ζ ω) (σ₀ ω) := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  obtain ⟨Yv, hYm, -, -, hYae⟩ := exists_frozenMean_version (ρL := ρL) (ρR := ρR) hE hσ₀ hσ₀ζ hσ₀N
  obtain ⟨G, hG0, hGae, hGsub⟩ := exists_goodSet hE hσ₀ζ
  have hW𝓖 : AdaptedBefore 𝓖 ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hE.2.1
  have hVL𝓖 : ∀ i, AdaptedBefore 𝓖 ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.2.2.1 i)
  have hVR𝓖 : ∀ i, AdaptedBefore 𝓖 ζ (VR i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.2.2.2.1 i)
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGsub ω hω).1.2.2.2.1
  -- for each `z ∈ ℍ`, almost every `(z, ω)` is a good pair
  have hgood : ∀ z ∈ H, ∀ᵐ ω ∂P, (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀ := by
    intro z hz
    obtain ⟨hlim, -⟩ := exists_martingale_frozenMean (ρL := ρL) (ρR := ρR) hE hz hσ₀ hσ₀ζ hσ₀N
    filter_upwards [hlim, hGae] with ω hl hω
    obtain ⟨hP, hσζ⟩ := hGsub ω hω
    refine ⟨⟨hω, hz⟩, ?_⟩
    by_cases hs : (σ₀ ω : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z
    · left
      obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hs hσζ)
      have hc1' : (σ₀ ω : ℝ) < c := by exact_mod_cast hc1
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc1'
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hq1.le
      have hqc : ((q : ℝ).toNNReal : ℝ≥0∞) < c := by
        exact_mod_cast (Real.toNNReal_lt_iff_lt_coe hq0).2 hq2
      have hqm := hqc.trans hc2
      refine mem_iUnion.2 ⟨q, ?_, ?_⟩
      · show σ₀ ω < (q : ℝ).toNNReal
        exact Real.lt_toNNReal_iff_coe_lt.2 hq1
      · exact (mem_aliveProd_iff hP hω hz (hqm.trans_le (min_le_right _ _))).2
          (hqm.trans_le (min_le_left _ _))
    · right
      have hsσ := not_lt.1 hs
      exact (guardG_iff hP hω hz (lt_of_le_of_lt hsσ hσζ)).2 ⟨_, hl hsσ⟩
  -- Fubini
  have hgm := measurableSet_goodPair (ρL := ρL) (ρR := ρR) hW𝓖 hVL𝓖 hVR𝓖 hGc hG0 hσ₀
  have e : {x : ℂ × Ω | x.1 ∈ H → x ∈ goodPair ρL ρR W VL VR ζ G σ₀} =
      (Prod.fst ⁻¹' H)ᶜ ∪ goodPair ρL ρR W VL VR ζ G σ₀ := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
    tauto
  have hmeas : MeasurableSet {x : ℂ × Ω | x.1 ∈ H → x ∈ goodPair ρL ρR W VL VR ζ G σ₀} := by
    rw [e]
    exact (isOpen_H.measurableSet.preimage measurable_fst).compl.union hgm
  have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂P, z ∈ H →
      (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀ := Eventually.of_forall fun z => by
    by_cases hz : z ∈ H
    · filter_upwards [hgood z hz] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hz
  have h2 := (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P)
    (p := fun z ω => z ∈ H → (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀) hmeas).1 h1
  filter_upwards [hGae, h2, hYae] with ω hω hgp hY
  obtain ⟨hP, hσζ⟩ := hGsub ω hω
  refine ⟨hP, hσζ, ?_, fun t => ⟨fun z => Yv t z ω, (hYm t).comp measurable_prodMk_right, ?_⟩⟩
  · filter_upwards [hgp] with z hz hzH using frozenMean_facts_of_goodPair hP hσζ (hz hzH)
  · filter_upwards [hY] with z hz hzH using hz hzH t

end AeGood

/-! ### The exponential identity for nonnegative test functions -/

section ExpNonneg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- An adapted process almost surely equal, at each time, to a martingale is a martingale. -/
theorem martingale_of_ae_eq {𝓖 : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓖 P)
    (hY : StronglyAdapted 𝓖 Y) (h : ∀ t, Y t =ᵐ[P] X t) : Martingale Y 𝓖 P :=
  ⟨hY, fun i j hij => (condExp_congr_ae (h j)).trans ((hX.2 i j hij).trans (h i).symm)⟩

/-- An almost sure property holds on an event of `𝓖_0` (usual augmentation) of full measure. -/
theorem exists_measurableSet_usualAugmentation_zero {𝓕 : Filtration ℝ≥0 mΩ} {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ E : Set Ω, MeasurableSet[usualAugmentation 𝓕 P 0] E ∧ (∀ᵐ ω ∂P, ω ∈ E) ∧ ∀ ω ∈ E, p ω := by
  have hnull : P (toMeasurable P {ω | p ω}ᶜ) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.1 hp
  refine ⟨(toMeasurable P {ω | p ω}ᶜ)ᶜ,
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable _ _) hnull 0).compl, ?_,
    fun ω hω => ?_⟩
  · rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simpa using hω
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

variable {nL nR : ℕ} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The real exponential identity for a nonnegative test function**: for `ψ ≥ 0`, a bounded stopping time
`σ₀ < T`, `s ≤ t` and `S ∈ 𝓖_s`, `∫_S exp(m_t(ψ) + e_t(ψ)/2) = ∫_S exp(m_s(ψ) + e_s(ψ)/2)` (the exponential
martingale `exp(M − ⟨M⟩/2)` of the centred tested mean, whose bracket is `e_0 − e_t` by Lemma 3.6). -/
theorem setIntegral_exp_testedMean_eq [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N)
    {ψ : ℂ → ℝ} (hψ : IsTestFn ψ) (hψ0 : ∀ a, 0 ≤ ψ a) {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω}
    (hS : MeasurableSet[usualAugmentation 𝓕 P s] S) :
    ∫ ω in S, Real.exp (testedMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
        (min t (σ₀ ω)) ψ + retainedGreenEnergy (W · ω) (min t (σ₀ ω)) ψ / 2) ∂P =
      ∫ ω in S, Real.exp (testedMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
        (min s (σ₀ ω)) ψ + retainedGreenEnergy (W · ω) (min s (σ₀ ω)) ψ / 2) ∂P := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hψ' := hψ
  obtain ⟨hψc, hψs, δ, hδ, hψδ⟩ := hψ'
  have hψH : ∀ z, z ∉ H → ψ z = 0 := fun z hz => by
    by_contra h; exact hz (hψ.mem_H h)
  obtain ⟨M₁, hM₁, hM₁e⟩ := exists_martingale_testedMean (ρL := ρL) (ρR := ρR) hE hσ₀ hσ₀ζ hσ₀N
    hψc.measurable hψ.integrable hψH
  obtain ⟨N₁, hN₁, hN₁e⟩ := exists_martingale_testedMean_sq_add_energy (ρL := ρL) (ρR := ρR) hE hσ₀
    hσ₀ζ hσ₀N hψc hψs hδ hψδ
  set m : ℝ≥0 → Ω → ℝ := fun t ω => testedMean ρL ρR (W · ω) (fun i => (VL i · ω))
    (fun i => (VR i · ω)) (min t (σ₀ ω)) ψ with hm
  set e : ℝ≥0 → Ω → ℝ := fun t ω => retainedGreenEnergy (W · ω) (min t (σ₀ ω)) ψ with he
  obtain ⟨E, hE0, hEae, hEsub⟩ := exists_measurableSet_usualAugmentation_zero (𝓕 := 𝓕) (P := P)
    (p := fun ω => IsGoodPath xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω) (σ₀ ω) ∧ (∀ t, M₁ t ω = m t ω) ∧ ∀ t, N₁ t ω = m t ω ^ 2 + e t ω)
    (by filter_upwards [ae_isGoodPath hE hσ₀ hσ₀ζ hσ₀N, hM₁e, hN₁e] with ω h1 h2 h3
        exact ⟨h1, h2, h3⟩)
  set c₀ : ℝ := ∫ z, ψ z * condMean ρL ρR xL xR z with hc₀
  set e₀ : ℝ := ∫ a, ∫ b, ψ a * greenH a b * ψ b with he₀
  have hEt : ∀ u : ℝ≥0, MeasurableSet[𝓖 u] E := fun u => 𝓖.mono zero_le _ hE0
  -- facts on `E`
  have hgood : ∀ ω ∈ E, IsGoodPath xL xR ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
      (B · ω) (ζ ω) (σ₀ ω) := fun ω hω => (hEsub ω hω).1
  have hm0 : ∀ ω ∈ E, m 0 ω = c₀ := fun ω hω => (hgood ω hω).testedMean_zero hψ
  have he0 : ∀ ω ∈ E, e 0 ω = e₀ := fun ω hω => by
    have hg := hgood ω hω
    simp only [he, min_eq_left zero_le]
    exact retainedGreenForm_zero hg.1 (lt_of_le_of_lt zero_le hg.2.1) hψ hψ
  have he_nonneg : ∀ ω ∈ E, ∀ u, 0 ≤ e u ω := fun ω hω u => by
    have hg := hgood ω hω
    have hT : ((min u (σ₀ ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right u (σ₀ ω)) hg.2.1
    simp only [he, retainedGreenEnergy_eq_form, retainedGreenForm_eq_integral_prod hg.1 hψ hψ hT]
    exact integral_nonneg fun p => mul_nonneg (mul_nonneg (hψ0 _) (retainedGreen_nonneg _ _ _ _))
      (hψ0 _)
  -- the centred processes
  set M : ℝ≥0 → Ω → ℝ := fun u => E.indicator fun ω => M₁ u ω - c₀ with hMdef
  set A : ℝ≥0 → Ω → ℝ := fun u => E.indicator fun ω => e₀ - (N₁ u ω - M₁ u ω ^ 2) with hAdef
  have hMa : ∀ u ω, ω ∈ E → M u ω = m u ω - c₀ := fun u ω hω => by
    simp only [hMdef, indicator_of_mem hω, (hEsub ω hω).2.1 u]
  have hAa : ∀ u ω, ω ∈ E → A u ω = e₀ - e u ω := fun u ω hω => by
    simp only [hAdef, indicator_of_mem hω, (hEsub ω hω).2.1 u, (hEsub ω hω).2.2 u]
    ring
  have hM₁m : ∀ u, StronglyMeasurable[𝓖 u] (M₁ u) := fun u => hM₁.stronglyAdapted u
  have hN₁m : ∀ u, StronglyMeasurable[𝓖 u] (N₁ u) := fun u => hN₁.stronglyAdapted u
  have hMad : StronglyAdapted 𝓖 M := fun u =>
    ((hM₁m u).sub stronglyMeasurable_const).indicator (hEt u)
  have hAad : StronglyAdapted 𝓖 A := fun u =>
    (stronglyMeasurable_const.sub ((hN₁m u).sub ((hM₁m u).pow 2))).indicator (hEt u)
  have hMmart : Martingale M 𝓖 P := by
    refine martingale_of_ae_eq (hM₁.sub (martingale_const 𝓖 P c₀)) hMad fun u => ?_
    filter_upwards [hEae] with ω hω
    simp only [hMdef, indicator_of_mem hω, Pi.sub_apply]
  have hM2mart : Martingale (fun u ω => M u ω ^ 2 - A u ω) 𝓖 P := by
    have hX := (hN₁.sub (hM₁.smul (2 * c₀))).add (martingale_const 𝓖 P (c₀ ^ 2 - e₀))
    refine martingale_of_ae_eq hX (fun u => ((hMad u).pow 2).sub (hAad u)) fun u => ?_
    filter_upwards [hEae] with ω hω
    simp only [hMdef, hAdef, indicator_of_mem hω, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  -- bounds and regularity, everywhere
  set K : ℝ := (∫ z, |ψ z|) * meanBound ρL ρR + |c₀| with hK
  have hMb : ∀ u ω, |M u ω| ≤ K := fun u ω => by
    by_cases hω : ω ∈ E
    · rw [hMa u ω hω]
      exact (abs_sub _ _).trans (add_le_add ((hgood ω hω).abs_testedMean_le hψ u) le_rfl)
    · simp only [hMdef, indicator_of_notMem hω, abs_zero]
      exact add_nonneg (mul_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (meanBound_nonneg ρL ρR)) (abs_nonneg _)
  have hMc : ∀ ω, Continuous fun u => M u ω := fun ω => by
    by_cases hω : ω ∈ E
    · have e1 : (fun u => M u ω) = fun u => m u ω - c₀ := funext fun u => hMa u ω hω
      rw [e1]
      exact ((hgood ω hω).continuous_testedMean hψ).sub continuous_const
    · have e1 : (fun u => M u ω) = fun _ => 0 := funext fun u => by
        simp only [hMdef, indicator_of_notMem hω]
      rw [e1]; exact continuous_const
  have hA0 : ∀ ω, A 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ E
    · rw [hAa 0 ω hω, he0 ω hω, sub_self]
    · simp only [hAdef, indicator_of_notMem hω]
  have hAmono : ∀ ω, Monotone fun u => A u ω := fun ω => by
    by_cases hω : ω ∈ E
    · intro u v huv
      simp only [hAa u ω hω, hAa v ω hω]
      have hg := hgood ω hω
      exact sub_le_sub_left (antitone_retainedGreenForm_min hg.1 hg.2.1 hψ hψ hψ0 hψ0 huv) _
    · intro u v _
      simp only [hAdef, indicator_of_notMem hω, le_refl]
  have hAc : ∀ ω, Continuous fun u => A u ω := fun ω => by
    by_cases hω : ω ∈ E
    · have e1 : (fun u => A u ω) = fun u => e₀ - e u ω := funext fun u => hAa u ω hω
      rw [e1]
      have hg := hgood ω hω
      exact continuous_const.sub (continuous_retainedGreenForm_min hg.1 hg.2.1 hψ hψ)
    · have e1 : (fun u => A u ω) = fun _ => 0 := funext fun u => by
        simp only [hAdef, indicator_of_notMem hω]
      rw [e1]; exact continuous_const
  have hAK : ∀ u ω, A u ω ≤ |e₀| := fun u ω => by
    by_cases hω : ω ∈ E
    · rw [hAa u ω hω]
      linarith [he_nonneg ω hω u, le_abs_self e₀]
    · simp only [hAdef, indicator_of_notMem hω]; exact abs_nonneg _
  have hexp := martingale_exp_of_continuous_bracket hMmart hM2mart hMb hMc hA0 hAmono hAc hAK 1
  have hset := hexp.setIntegral_eq hst hS
  -- back to the frozen objects
  have hconv : ∀ u : ℝ≥0, ∫ ω in S, Real.exp (m u ω + e u ω / 2) ∂P =
      Real.exp (c₀ + e₀ / 2) * ∫ ω in S, Real.exp (1 * M u ω - 1 ^ 2 * A u ω / 2) ∂P := fun u => by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hEae] with ω hω
    rw [hMa u ω hω, hAa u ω hω, ← Real.exp_add]
    congr 1
    ring
  show ∫ ω in S, Real.exp (m t ω + e t ω / 2) ∂P = ∫ ω in S, Real.exp (m s ω + e s ω / 2) ∂P
  rw [hconv t, hconv s, hset]

end ExpNonneg

end WangWu

end InteractingSLE
