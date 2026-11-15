/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowLoc

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the stopped Lyapunov martingale

Packet PROVE-G12C. Up to the stopping time `lowStop` of `G12LowLoc.lean`, the Itô coordinates of an evolution stay
in the compact set `lowKc` (PROVE-G12's box, the inner gap `o ≥ δ'_n`, and `e ≥ 0`), which lies in the region of
the Lyapunov observable. Hence:

* `martingale_lowObs`: `lowObs(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen` is a martingale of the usual augmentation;
* `intervalIntegrable_itoGen_lowObs`: on a good path the generator is integrable on `[0, σ]` (it is a continuous
  combination of the force densities, which are integrable);
* pathwise identities of the coordinates on the good event (`lowO_coord`, `lowE_coord`, `lowDelta_le_gap`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (GCoord gDriftLin gDriftLin₀ g12Dens coordG densG gapStopG locG kbG coordAtG densAtG clockAt kcG)
open Supp8.GB5 (IsGBGood isFilteredBrownianReal_brownG_gb continuous_brownG_gb measurableSet_good_usual'
  abs_le_norm_state nonneg_of_le_hitBelow continuousOn_stateAt_gb)

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {k j₀ : Fin nR} {S : ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {q : ℝ≥0} {C n : ℕ}

/-! ### The compact set -/

/-- PROVE-G12's compact set, with the inner gap `o ≥ δ'_n` and `e ≥ 0`. -/
def lowKc (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k j₀ : Fin nR)
    (n : ℕ) : Set (GCoord nL nR × ℝ) :=
  kcG κ xL xR ρL ρR j₀ n ∩ {p | lowDelta xR k n ≤ lowO κ xL xR ρL ρR k p} ∩ {p | 0 ≤ lowE k j₀ p}

theorem isCompact_lowKc : IsCompact (lowKc κ xL xR ρL ρR k j₀ n) :=
  ((G12.isCompact_kcG κ xL xR ρL ρR j₀ n).inter_right
    (isClosed_le continuous_const (contDiff_lowO κ xL xR ρL ρR k (n := 0)).continuous)).inter_right
    (isClosed_le continuous_const (contDiff_lowE (nL := nL) k j₀ (n := 0)).continuous)

theorem lowDelta_pos (hxk : 0 < xR k) : 0 < lowDelta xR k n := lt_min (G12.dlt_pos n) hxk

theorem lowO_initG : lowO κ xL xR ρL ρR k (G12.initG xL xR) = xR k := by
  simp [lowO, G12.initG, gDriftLin]

theorem lowKc_subset (hxk : 0 < xR k) (hkj : xR k < xR j₀) :
    lowKc κ xL xR ρL ρR k j₀ n ⊆ lowRegion κ xL xR ρL ρR k j₀ := by
  rintro p ⟨⟨hp, ho⟩, he⟩
  refine ⟨(lowDelta_pos hxk).trans_le ho, ?_⟩
  rcases hp with rfl | hp
  · show 0 < xR j₀ - xR k
    linarith
  · obtain ⟨-, -, -, -, -, -, -, h8⟩ := hp
    have hk : k ∈ G12.offY xR j₀ := by simp [G12.offY, hkj.ne]
    have h1 := (G12.dlt_pos n).trans_le (h8 k hk)
    have he' : 0 ≤ p.1.2.1 j₀ - p.1.2.1 k := he
    rw [abs_of_nonneg he'] at h1
    exact h1

/-! ### The coordinates on good paths -/

section Path

variable (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)

include hgood in
theorem lowO_coord {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    lowO κ xL xR ρL ρR k (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) = VR k t ω - W t ω := by
  have hN := G12.w_eq_gDriftLin (j₀ := j₀) (hgood ω hω).1 ht
  simp only [lowO, coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
  rw [hN]
  simp only [coordAtG]

omit [MeasurableSpace Ω] in
theorem lowE_coord {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    lowE k j₀ (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) = VR j₀ t ω - VR k t ω := by
  simp only [lowE, coordG, hω, ↓reduceIte, coordAtG]

include hgood in
/-- **Up to `σ` the inner gap is at least `δ'_n`.** -/
theorem lowDelta_le_gap {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0}
    (ht : t ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) :
    lowDelta xR k n ≤ VR k t ω - W t ω := by
  set σ := lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω with hσ
  have hF := (hgood ω hω).1.isForcePath
  have hσζ : (σ : ℝ≥0∞) < ζ ω := lt_zeta_of_le hgood (fun ω => lowStop_le_locG ω) hω le_rfl
  rcases (zero_le (a := σ)).eq_or_lt with h0 | h0
  · have ht0 : t = 0 := le_antisymm (h0 ▸ ht) bot_le
    rw [ht0, hF.vR_zero, hF.w_zero, sub_zero]
    exact min_le_right _ _
  have hO := lowStop_le_oStop (κ := κ) (ρL := ρL) (xR := xR) (ρR := ρR) (k := k) (j₀ := j₀) (S := S)
    (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (q := q) (C := C) (n := n) ω
  simp only [lowOStop, hω, ↓reduceIte] at hO
  have hf : ContinuousOn (fun s => (Coupling.stateAt W VL VR s ω).2.2 k - (Coupling.stateAt W VL VR s ω).1 -
      lowDelta xR k n) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    ((hF.continuousOn_vR k).sub hF.continuousOn_w).sub continuousOn_const
  have h := nonneg_of_le_hitBelow hf hσζ hO h0 ht
  simp only [Coupling.stateAt] at h
  linarith

include hgood in
/-- **Up to `σ` the coordinates stay in `lowKc`.** -/
theorem mem_lowKc (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀) (hkj : k ≤ j₀)
    (hkjx : xR k < xR j₀) {ω : Ω}
    {t : ℝ≥0} (ht : t ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) :
    (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) ∈ lowKc κ xL xR ρL ρR k j₀ n := by
  by_cases hω : ω ∈ G
  · have htl := ht.trans (lowStop_le_locG ω)
    have htζ : (t : ℝ≥0∞) < ζ ω := lt_zeta_of_le hgood (fun ω => lowStop_le_locG ω) hω ht
    refine ⟨⟨G12.mem_kcG_of_le_locG hgood hTn hy htl, ?_⟩, ?_⟩
    · show lowDelta xR k n ≤ lowO κ xL xR ρL ρR k _
      rw [lowO_coord hgood hω htζ]
      exact lowDelta_le_gap hgood hω ht
    · show 0 ≤ lowE k j₀ _
      rw [lowE_coord hω]
      exact sub_nonneg.2 ((hgood ω hω).1.isForcePath.monotone_vR htζ hkj)
  · have hc : (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) = G12.initG xL xR := by
      simp [coordG, Sec2.TwoSeed.brownG, hω, G12.initG]
    rw [hc]
    refine ⟨⟨mem_insert _ _, ?_⟩, ?_⟩
    · show lowDelta xR k n ≤ lowO κ xL xR ρL ρR k _
      rw [lowO_initG]
      exact min_le_right _ _
    · show 0 ≤ xR j₀ - xR k
      linarith

end Path

/-! ### The stopped martingale -/

section Mart

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀) (hxk : 0 < xR k) (hkj : k ≤ j₀) (hkjx : xR k < xR j₀)

include hE hGm hGc hgood hT hTn hy hxk hkj hkjx in
/-- **The stopped Lyapunov martingale.** -/
theorem martingale_lowObs (α Y₀ : ℝ) :
    Martingale (fun t ω =>
      lowObs κ xL xR ρL ρR k j₀ α Y₀
          (coordG xL xR G W VL VR j₀ (min t (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω)) ω,
            Sec2.TwoSeed.brownG G B (min t (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) : ℝ≥0),
          Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ α Y₀)
            (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
            (densG G W VL VR j₀ s ω)) (usualAugmentation 𝓕 P) P :=
  martingale_of_le_locG hE hGm hGc hgood hTn hy (isStoppingTime_lowStop hE hGm hGc hgood hT)
    (fun ω => lowStop_le_locG ω) (isOpen_lowRegion κ xL xR ρL ρR k j₀)
    (contDiffOn_lowObs κ xL xR ρL ρR k j₀ α Y₀) isCompact_lowKc (lowKc_subset hxk hkjx)
    (fun _ _ ht => mem_lowKc hgood hTn hy hkj hkjx ht)

include hgood hTn hy hxk hkj hkjx in
/-- **The generator is integrable along a good path up to `σ`**: it is a combination, with coefficients continuous on
`[0, σ]`, of the force densities. -/
theorem intervalIntegrable_itoGen_lowObs (hκ : 0 ≤ κ) (α Y₀ : ℝ) {ω : Ω} (hω : ω ∈ G) :
    IntervalIntegrable (fun s : ℝ => Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ α Y₀)
      (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG G W VL VR j₀ s ω))
      volume 0 (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) := by
  set σ := lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω with hσdef
  have hF := (hgood ω hω).1.isForcePath
  have hσle : ∀ ω, lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω ≤ locG xR j₀ G W VL VR B ζ T n ω :=
    fun ω => lowStop_le_locG ω
  have hlife : G11.IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) σ := isMarkLife_of_le hgood hy hσle hω
  have hmaps : MapsTo Real.toNNReal (Icc 0 (σ : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun r hr =>
    Sec2.toNNReal_lt_of_mem_Icc hlife.1 hr
  have hcw : ContinuousOn (fun s : ℝ => W s.toNNReal ω) (Icc 0 (σ : ℝ)) :=
    hF.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps
  have hcv : ∀ j, ContinuousOn (fun s : ℝ => VR j s.toNNReal ω) (Icc 0 (σ : ℝ)) := fun j =>
    (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps
  -- the gaps on `[0, σ]`
  have hmem : ∀ s ∈ Icc (0 : ℝ) σ,
      (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) ∈
        lowRegion κ xL xR ρL ρR k j₀ := fun s hs =>
    lowKc_subset hxk hkjx (mem_lowKc hgood hTn hy hkj hkjx (Sec2.toNNReal_le_of_mem_Icc hs))
  have hO : ∀ s ∈ Icc (0 : ℝ) σ, lowO κ xL xR ρL ρR k
      (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) =
        VR k s.toNNReal ω - W s.toNNReal ω := fun s hs => lowO_coord hgood hω (hmaps hs)
  have hE' : ∀ s ∈ Icc (0 : ℝ) σ, lowE k j₀
      (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) =
        VR j₀ s.toNNReal ω - VR k s.toNNReal ω := fun s _ => lowE_coord hω _
  have hopos : ∀ s ∈ Icc (0 : ℝ) σ, 0 < VR k s.toNNReal ω - W s.toNNReal ω := fun s hs => by
    rw [← hO s hs]; exact (hmem s hs).1
  have hepos : ∀ s ∈ Icc (0 : ℝ) σ, 0 < VR j₀ s.toNNReal ω - VR k s.toNNReal ω := fun s hs => by
    rw [← hE' s hs]; exact (hmem s hs).2
  -- the coefficients
  set Yf : ℝ → ℝ := fun s => Real.log (VR k s.toNNReal ω - W s.toNNReal ω) -
    Real.log (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) with hYf
  have hYc : ContinuousOn Yf (Icc 0 (σ : ℝ)) :=
    (((hcv k).sub hcw).log fun s hs => (hopos s hs).ne').sub
      (((hcv j₀).sub (hcv k)).log fun s hs => (hepos s hs).ne')
  have hc1 : ContinuousOn (fun s => lowH1 α Y₀ (Yf s) / (VR k s.toNNReal ω - W s.toNNReal ω))
      (Icc 0 (σ : ℝ)) :=
    ((continuous_lowH1 α Y₀).comp_continuousOn hYc).div ((hcv k).sub hcw) fun s hs => (hopos s hs).ne'
  have hc2 : ContinuousOn (fun s => lowH1 α Y₀ (Yf s) / (VR j₀ s.toNNReal ω - VR k s.toNNReal ω))
      (Icc 0 (σ : ℝ)) :=
    ((continuous_lowH1 α Y₀).comp_continuousOn hYc).div ((hcv j₀).sub (hcv k)) fun s hs => (hepos s hs).ne'
  have hc3 : ContinuousOn (fun s => 1 / 2 * (κ * (lowH2 α Y₀ (Yf s) - lowH1 α Y₀ (Yf s)) /
      (VR k s.toNNReal ω - W s.toNNReal ω) ^ 2)) (Icc 0 (σ : ℝ)) := by
    refine continuousOn_const.mul (ContinuousOn.div (continuousOn_const.mul
      (((continuous_lowH2 α Y₀).comp_continuousOn hYc).sub ((continuous_lowH1 α Y₀).comp_continuousOn hYc)))
      (((hcv k).sub hcw).pow 2) fun s hs => pow_ne_zero 2 (hopos s hs).ne')
  -- the density terms
  have hdens : ∀ s, densG G W VL VR j₀ s ω = g12Dens j₀ (W s.toNNReal ω) (fun i => VL i s.toNNReal ω)
      (fun j => VR j s.toNNReal ω) := fun s => by
    simp only [densG, hω, ↓reduceIte, densAtG]
  have hRi : ∀ j, IntervalIntegrable (fun s : ℝ => 2 / (VR j s.toNNReal ω - W s.toNNReal ω)) volume 0 σ :=
    fun j => hF.intervalIntegrable_forceR hlife.1 j
  have hLi : ∀ i, IntervalIntegrable (fun s : ℝ => 2 / (VL i s.toNNReal ω - W s.toNNReal ω)) volume 0 σ :=
    fun i => hF.intervalIntegrable_forceL hlife.1 i
  have hell : IntervalIntegrable (fun s => gDriftLin₀ ρL ρR (densG G W VL VR j₀ s ω)) volume 0 σ := by
    have a1 : IntervalIntegrable (fun s : ℝ => ∑ i, ρL i * (2 / (VL i s.toNNReal ω - W s.toNNReal ω)))
        volume 0 σ := by
      simpa only [Finset.sum_fn] using
        IntervalIntegrable.sum (univ : Finset (Fin nL)) fun i _ => (hLi i).const_mul (ρL i)
    have a2 : IntervalIntegrable (fun s : ℝ => ∑ j, ρR j * (2 / (VR j s.toNNReal ω - W s.toNNReal ω)))
        volume 0 σ := by
      simpa only [Finset.sum_fn] using
        IntervalIntegrable.sum (univ : Finset (Fin nR)) fun j _ => (hRi j).const_mul (ρR j)
    have := (a1.const_mul (-(1 / 2))).sub (a2.const_mul (1 / 2))
    refine this.congr fun s _ => ?_
    simp only [hdens, gDriftLin₀, g12Dens]
  have hX1 : IntervalIntegrable (fun s => (densG G W VL VR j₀ s ω).2.1 k - gDriftLin₀ ρL ρR
      (densG G W VL VR j₀ s ω)) volume 0 σ := by
    refine ((hRi k).congr fun s _ => ?_).sub hell
    simp only [hdens, g12Dens]
  have hX2 : IntervalIntegrable (fun s => (densG G W VL VR j₀ s ω).2.1 j₀ - (densG G W VL VR j₀ s ω).2.1 k)
      volume 0 σ := by
    refine ((hRi j₀).sub (hRi k)).congr fun s _ => ?_
    simp only [hdens, g12Dens]
  have huIcc : uIcc (0 : ℝ) σ = Icc (0 : ℝ) σ := uIcc_of_le σ.coe_nonneg
  have hsum := ((hX1.continuousOn_mul (huIcc ▸ hc1)).sub (hX2.continuousOn_mul (huIcc ▸ hc2))).add
    ((huIcc ▸ hc3).intervalIntegrable)
  refine hsum.congr fun s hs => ?_
  have hs' : s ∈ Icc (0 : ℝ) σ := by
    rw [uIoc_of_le σ.coe_nonneg] at hs; exact ⟨hs.1.le, hs.2⟩
  rw [itoGen_lowObs κ xL xR ρL ρR k j₀ α Y₀ hκ (hmem s hs'), hO s hs', hE' s hs']
  have h1 := (hopos s hs').ne'
  have h2 := (hepos s hs').ne'
  simp only [hYf]
  field_simp

end Mart

end G12Low

end Supp7

end InteractingSLE
