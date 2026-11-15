/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Mart
import InteractingSLE.Spec.Sec7.LocalExtBGraph
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# The local comparison of Aux. lemma 55: the Girsanov drift of the seed weights through the local stop

Packet PROVE-LOCEXT-A3, item 1 (c). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L206, pp. 248–249):
(HL7) `a_t = κ^{−1/2} ∑_{j∈J} ρ_j/(W_t − V^j_t)` and "under `ℚ`, `B^ℚ_{t∧S} = B_{t∧S} + ∫₀^{t∧S} a_s ds` is Brownian motion
stopped at `S`".

* `capTime`: the local stop capped at the lifetime, as an `ℝ≥0`-valued stopping time of the usual augmentation (equal to
  `stopTime` on the good event);
* `srcTheta`: the Girsanov drift `Sec2.weightDrift` of the change of weights `(ρL; ρR) → (seed weights)` cut at
  `capTime` and at the level `7r` (the distant marks stay at distance `≥ 7r` before the stop);
* `srcTheta_eq_of_lt`: before the stop, `θ_t = A(t) = srcDrift` (the drift (HL7) of the distant marks); `θ_t = 0` after;
* `drift_srcTheta_eq`, `quadInt_srcTheta_eq`: `∫₀ᵗ θ = ∫₀^{t∧S} A`, `∫₀ᵗ θ² = ∫₀^{t∧S} A²` on the good event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec2 Girsanov

/-! ### The capped local stop as a real time -/

section Cap

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The local stop capped at the lifetime, as an `ℝ≥0`-valued time. -/
def capTime (r : ℝ) (G : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  (capStop r G ζ W ω).untopD 0

theorem capStop_ne_top (ω : Ω) : capStop r G ζ W ω ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top ((min_le_left _ _).trans localStop_le_stopHorizon)

theorem coe_capTime (ω : Ω) : (capTime r G ζ W ω : WithTop ℝ≥0) = capStop r G ζ W ω := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (capStop_ne_top (r := r) (G := G) (ζ := ζ) (W := W) ω)
  rw [capTime, ← ha, WithTop.untopD_coe]

theorem capTime_le_zeta (ω : Ω) : (capTime r G ζ W ω : ℝ≥0∞) ≤ ζ ω := by
  have h := capStop_le (G := G) (ζ := ζ) (W := W) r ω
  rw [← coe_capTime] at h
  exact h

theorem capTime_le_horizon (ω : Ω) : capTime r G ζ W ω ≤ stopHorizon r := by
  have h : capStop r G ζ W ω ≤ stopHorizon r := (min_le_left _ _).trans localStop_le_stopHorizon
  rw [← coe_capTime] at h
  exact WithTop.coe_le_coe.1 h

theorem capTime_eq_stopTime (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {ω : Ω} (hω : ω ∈ G) :
    capTime r G ζ W ω = stopTime r G ζ W ω := by
  have h := capStop_eq_localStop hG hF hr hseed hω
  rw [← coe_capTime, ← coe_stopTime] at h
  exact WithTop.coe_injective h

theorem isStoppingTime_capTime (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (capTime r G ζ W ω : WithTop ℝ≥0) := by
  have hE' := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have h1 : IsStoppingTime (usualAugmentation 𝓕 P) (localStop r G ζ W) := by
    have := isStoppingTime_stopTime (r := r) hE hGm hG0 hG
    simp_rw [coe_stopTime] at this
    exact this
  have h2 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ζ ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hE'.2.1
  simp_rw [coe_capTime]
  exact h1.min h2

theorem measurableSet_le_capTime (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (s : ℝ≥0) : MeasurableSet[usualAugmentation 𝓕 P s] {ω | (capTime r G ζ W ω : ℝ≥0∞) ≤ s} := by
  have h := isStoppingTime_capTime (r := r) hE hGm hG0 hG s
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, ENNReal.coe_le_coe, WithTop.coe_le_coe]

end Cap

/-! ### The Girsanov drift of the seed weights -/

section Theta

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

variable (κ xL xR ρL ρR r W VL VR ζ G) in
/-- **The Girsanov drift of the seed weights**: the change of weights `(ρL; ρR) → (seed weights)` cut at the capped
local stop and at the level `7r`. -/
def srcTheta : ℝ≥0 → Ω → ℝ :=
  weightDrift κ (7 * r) ρL (seedWtL xL ρL) ρR (seedWtR xR ρR) (fun ω => (capTime r G ζ W ω : ℝ≥0∞)) ζ W VL VR

/-- **The distant marks are `7r` away before the stop.** -/
theorem gap_of_lt_capTime (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {ω : Ω} (hω : ω ∈ G)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capTime r G ζ W ω) :
    (∀ i, seedWtL xL ρL i ≠ ρL i → 7 * r ≤ |W t ω - VL i t ω|) ∧
      ∀ i, seedWtR xR ρR i ≠ ρR i → 7 * r ≤ |W t ω - VR i t ω| := by
  have hg := hG ω hω
  have hp' := hg.isSLEPathUpTo
  have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans_le (capTime_le_zeta ω)
  have htS : (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [capTime_eq_stopTime hG hF hr hseed hω] at ht
    rw [← coe_stopTime_of_mem hω]
    exact WithTop.coe_le_coe.2 (ENNReal.coe_lt_coe.1 ht).le
  have hwt : |W t ω| ≤ r / 4 := abs_le_of_le_localStopPath hp'.continuousOn_w hp'.w_zero hr.1.le htS htζ
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hxi : xL i ≠ 0 := fun h0 => hi (by simp [seedWtL, h0])
    exact (seven_mul_le_sub_vL hp' hF hr hxi htζ hwt).trans (le_abs_self _)
  · have hxi : xR i ≠ 0 := fun h0 => hi (by simp [seedWtR, h0])
    rw [abs_sub_comm]
    exact (seven_mul_le_vR_sub hp' hF hr hxi htζ hwt).trans (le_abs_self _)

/-- **Before the stop the Girsanov drift is the source drift** (HL7): `θ_t = A(t)`. -/
theorem srcTheta_eq_of_lt (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {ω : Ω} (hω : ω ∈ G)
    {t : ℝ≥0} (ht : t < stopTime r G ζ W ω) :
    srcTheta κ xL xR ρL ρR r W VL VR ζ G t ω = srcDrift κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t := by
  have hg := hG ω hω
  have hp' := hg.isSLEPathUpTo
  have hct : (t : ℝ≥0∞) < capTime r G ζ W ω := by
    rw [capTime_eq_stopTime hG hF hr hseed hω]; exact_mod_cast ht
  have hδ : (0 : ℝ) < 7 * r := by have := hr.1; positivity
  have htS : ((t : ℝ).toNNReal : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [Real.toNNReal_coe, ← coe_stopTime_of_mem hω]
    exact WithTop.coe_le_coe.2 ht.le
  rw [srcTheta, weightDrift_eq_of_lt hδ (capTime_le_zeta ω) hp'.continuousOn_w hp'.continuousOn_vL
      hp'.continuousOn_vR (fun t' ht' => gap_of_lt_capTime hG hF hr hseed hω ht') hct,
    show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl,
    srcDrift_eq_distDrift_of_isGoodPath hg.1 hg.2 hF hr hseed t.coe_nonneg htS, Real.toNNReal_coe]
  unfold distDrift
  have hL : ∑ i, (seedWtL xL ρL i - ρL i) / (W t ω - VL i t ω) =
      -∑ i ∈ distSetL xL, ρL i / (W t ω - VL i t ω) := by
    rw [distSetL, Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : xL i = 0 <;> simp [seedWtL, h, neg_div]
  have hR : ∑ i, (seedWtR xR ρR i - ρR i) / (W t ω - VR i t ω) =
      -∑ i ∈ distSetR xR, ρR i / (W t ω - VR i t ω) := by
    rw [distSetR, Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : xR i = 0 <;> simp [seedWtR, h, neg_div]
  rw [hL, hR]
  ring

/-- After the capped stop the Girsanov drift vanishes. -/
theorem srcTheta_eq_zero_of_lt {t : ℝ≥0} {ω : Ω} (h : capTime r G ζ W ω < t) :
    srcTheta κ xL xR ρL ρR r W VL VR ζ G t ω = 0 :=
  cutDrift_eq_zero (τ := fun ω => (capTime r G ζ W ω : ℝ≥0∞)) (by exact_mod_cast h)

/-- **Splitting an integral at a stop**: `∫₀ᵗ f = ∫₀^{t∧S} g` when `f = g` on `(0, S)` and `f = 0` after `S`. -/
theorem integral_eq_of_stop {f g : ℝ → ℝ} {S t : ℝ≥0} (hf : IntervalIntegrable f volume 0 t)
    (hfg : ∀ u : ℝ, 0 < u → u < S → f u = g u) (hf0 : ∀ u : ℝ, (S : ℝ) < u → f u = 0) :
    ∫ u in (0 : ℝ)..t, f u = ∫ u in (0 : ℝ)..((min t S : ℝ≥0) : ℝ), g u := by
  set m : ℝ := ((min t S : ℝ≥0) : ℝ) with hm
  have hm0 : 0 ≤ m := NNReal.coe_nonneg _
  have hmt : m ≤ t := by rw [hm]; exact_mod_cast min_le_left t S
  have hmS : m ≤ S := by rw [hm]; exact_mod_cast min_le_right t S
  have h1 : IntervalIntegrable f volume 0 m := hf.mono_set (by
    rw [uIcc_of_le hm0, uIcc_of_le (hm0.trans hmt)]; exact Icc_subset_Icc le_rfl hmt)
  have h2 : IntervalIntegrable f volume m t := hf.mono_set (by
    rw [uIcc_of_le hmt, uIcc_of_le (hm0.trans hmt)]; exact Icc_subset_Icc hm0 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hz : ∫ u in m..(t : ℝ), f u = 0 := by
    rcases le_total t S with htS | htS
    · have : m = t := by rw [hm, min_eq_left htS]
      rw [this, intervalIntegral.integral_same]
    · have hmS' : m = S := by rw [hm, min_eq_right htS]
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun u hu => ?_)]
      · simp
      · rw [uIoc_of_le hmt] at hu
        exact hf0 u (hmS' ▸ hu.1)
  rw [hz, add_zero]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (S : ℝ)] with u huS hu
  rw [uIoc_of_le hm0] at hu
  exact hfg u hu.1 (lt_of_le_of_ne (hu.2.trans hmS) huS)

variable (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hF : IsOrderedForceWord xL xR)
  (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)

include hG hF hr hseed in
/-- **The drift of `θ` on the good event**: `∫₀ᵗ θ = ∫₀^{t∧S} A`. -/
theorem drift_srcTheta_eq (hθ : IsStronglyProgressive (usualAugmentation 𝓕 P) (srcTheta κ xL xR ρL ρR r W VL VR ζ G))
    {C : ℝ} (hθb : ∀ t ω, |srcTheta κ xL xR ρL ρR r W VL VR ζ G t ω| ≤ C) {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    drift (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t ω =
      ∫ u in (0 : ℝ)..((min t (stopTime r G ζ W ω) : ℝ≥0) : ℝ),
        srcDrift κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) u := by
  refine integral_eq_of_stop (intervalIntegrable_time hθ hθb ω 0 t) (fun u hu0 huS => ?_) (fun u hu => ?_)
  · have hlt : u.toNNReal < stopTime r G ζ W ω := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]; exact huS
    rw [srcTheta_eq_of_lt hG hF hr hseed hω hlt, Real.coe_toNNReal _ hu0.le]
  · refine srcTheta_eq_zero_of_lt ?_
    rw [capTime_eq_stopTime hG hF hr hseed hω, ← NNReal.coe_lt_coe,
      Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hu.le)]
    exact hu

include hG hF hr hseed in
/-- **The quadratic integral of `θ` on the good event**: `∫₀ᵗ θ² = ∫₀^{t∧S} A²`. -/
theorem quadInt_srcTheta_eq (hθ : IsStronglyProgressive (usualAugmentation 𝓕 P) (srcTheta κ xL xR ρL ρR r W VL VR ζ G))
    {C : ℝ} (hθb : ∀ t ω, |srcTheta κ xL xR ρL ρR r W VL VR ζ G t ω| ≤ C) {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    quadInt (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t ω =
      ∫ u in (0 : ℝ)..((min t (stopTime r G ζ W ω) : ℝ≥0) : ℝ),
        srcDrift κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) u ^ 2 := by
  have hint : IntervalIntegrable (fun u : ℝ => srcTheta κ xL xR ρL ρR r W VL VR ζ G u.toNNReal ω ^ 2) volume 0 t :=
    (intervalIntegrable_const (c := C ^ 2)).mono_fun'
      ((measurable_time_of_progressive hθ ω).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => by
        show ‖srcTheta κ xL xR ρL ρR r W VL VR ζ G u.toNNReal ω ^ 2‖ ≤ C ^ 2
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ _) 2)
  refine integral_eq_of_stop hint (fun u hu0 huS => ?_) (fun u hu => ?_)
  · have hlt : u.toNNReal < stopTime r G ζ W ω := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]; exact huS
    rw [srcTheta_eq_of_lt hG hF hr hseed hω hlt, Real.coe_toNNReal _ hu0.le]
  · rw [srcTheta_eq_zero_of_lt, zero_pow two_ne_zero]
    rw [capTime_eq_stopTime hG hF hr hseed hω, ← NNReal.coe_lt_coe,
      Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hu.le)]
    exact hu

end Theta

end LocalExt

end InteractingSLE
