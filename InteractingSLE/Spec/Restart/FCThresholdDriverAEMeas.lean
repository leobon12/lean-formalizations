/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCThresholdDriver
import InteractingSLE.Spec.Restart.StoppedK2ClauseFrz
import InteractingSLE.Spec.Sec7.Lemma71CMeas

/-!
# Reading a driver from capacity-parametrized prefixes

The left difference quotient of the normalized mapping-out functions recovers
the driver. Unlike `IsSegCurve`, this construction only needs a continuous path
on its available capacity interval; it makes no transience assertion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Restart.FCPlumb

open Sec7.Lemma71C

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The mapping-out function, zero at points outside its domain. -/
def fcPrefixMap (Γ : Ω → ℝ≥0 → ℂ) (q : ℝ≥0) (z : ℂ) : Ω → ℂ :=
  {ω | z ∈ H \ fillH (Γ ω '' Icc 0 q)}.indicator
    fun ω => ConformalImage.mapOut (fillH (Γ ω '' Icc 0 q)) z

/-- The driver read by the two limits in the mapping-out difference quotient. -/
def fcReadDriver (Γ : Ω → ℝ≥0 → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  if q = 0 then 0 else limUnder atTop fun N : ℕ => limUnder atTop fun k : ℕ =>
    (fcPrefixMap Γ q (zPt N) ω - 2 / (((k : ℂ) + 1) *
      (fcPrefixMap Γ q (zPt N) ω -
        fcPrefixMap Γ ((q : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal (zPt N) ω))).re

/-- Closed dyadic hits of a continuous measurable prefix are measurable. -/
theorem isDyadicHitMeasurable_fcPrefix {Γ : Ω → ℝ≥0 → ℂ}
    (hc : ∀ ω, Continuous (Γ ω)) (hm : ∀ t, Measurable fun ω => Γ ω t) (q : ℝ≥0) :
    IsDyadicHitMeasurable (fun ω => Γ ω '' Icc 0 q) := by
  intro n i
  have he : {ω | (dyadicSquare n i ∩ Γ ω '' Icc 0 q).Nonempty} =
      ⋂ a : ℕ, ⋃ j : ℕ, ⋃ k : ℕ,
        {ω | dyTime j k ≤ q ∧ Metric.infDist (Γ ω (dyTime j k)) (dyadicSquare n i) <
          1 / ((a : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    have hh : (dyadicSquare n i ∩ Γ ω '' Icc 0 q).Nonempty ↔
        ∃ s ≤ q, Γ ω s ∈ dyadicSquare n i := by
      constructor
      · rintro ⟨z, hz, s, hs, rfl⟩
        exact ⟨s, hs.2, hz⟩
      · rintro ⟨s, hs, hz⟩
        exact ⟨_, hz, s, ⟨zero_le, hs⟩, rfl⟩
    exact hh.trans (exists_mem_iff_dyTime (hc ω).continuousOn
      (isClosed_dyadicSquare n i) (PairData.dyadicSquare_nonempty n i))
  rw [he]
  exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun k => (MeasurableSet.const _).inter
      (measurableSet_lt ((Metric.continuous_infDist_pt _).measurable.comp (hm _)) measurable_const)

/-- The stopped-domain mapping-out coordinates are measurable. -/
theorem measurable_fcPrefixMap {Γ : Ω → ℝ≥0 → ℂ}
    (hc : ∀ ω, Continuous (Γ ω)) (hm : ∀ t, Measurable fun ω => Γ ω t)
    (h0 : ∀ ω, Γ ω 0 = 0) (q : ℝ≥0) (z : ℂ) : Measurable (fcPrefixMap Γ q z) := by
  apply measurable_indicator_mapOut (isDyadicHitMeasurable_fcPrefix hc hm q)
    (fun ω => isCompact_Icc.image (hc ω))
  intro ω
  exact (isPreconnected_Icc.image _ (hc ω).continuousOn).union 0
    ⟨0, ⟨le_rfl, zero_le⟩, h0 ω⟩ zero_mem_lowerHalf isPreconnected_lowerHalf

/-- No stochastic regularity assumption is needed to read measurable driver coordinates. -/
theorem measurable_fcReadDriver {Γ : Ω → ℝ≥0 → ℂ}
    (hc : ∀ ω, Continuous (Γ ω)) (hm : ∀ t, Measurable fun ω => Γ ω t)
    (h0 : ∀ ω, Γ ω 0 = 0) (q : ℝ≥0) : Measurable (fcReadDriver Γ q) := by
  change Measurable (fun ω => fcReadDriver Γ q ω)
  by_cases hq : q = 0
  · simp only [fcReadDriver, hq, ite_true]
    exact measurable_const
  · simp only [fcReadDriver, hq, ite_false]
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.limUnder
    intro N
    apply StronglyMeasurable.limUnder
    intro k
    have h₁ := measurable_fcPrefixMap hc hm h0 q (zPt N)
    have h₂ := measurable_fcPrefixMap hc hm h0
      ((q : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal (zPt N)
    exact (Complex.measurable_re.comp
      (h₁.sub (measurable_const.div (measurable_const.mul (h₁.sub h₂))))).stronglyMeasurable

omit mΩ in
/-- The prefix formula recovers every continuous driver of the given path before
its lifetime. No assertion at the terminal hull is needed. -/
theorem fcReadDriver_eq {Γ : Ω → ℝ≥0 → ℂ} {ω : Ω} {W : ℝ≥0 → ℝ} {U : ℝ≥0∞}
    (hW : Continuous W) (hW0 : W 0 = 0) (hg : IsGeneratingTrace W U (Γ ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < U) : fcReadDriver Γ q ω = W q := by
  by_cases hq0 : q = 0
  · simp only [fcReadDriver, hq0, ite_true, hW0]
  have hqp : (0 : ℝ) < q := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hq0)
  let Wr : ℝ → ℝ := fun r => W r.toNNReal
  have hWr : Continuous Wr := hW.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simpa [Wr] using hW0
  have hK (r : ℝ≥0) (hr : r ≤ q) :
      fwdHull Wr r = fillH (Γ ω '' Icc 0 r) := by
    have hc : ContinuousOn (Γ ω) (Icc 0 r) := hg.2.1.mono fun t ht =>
      (ENNReal.coe_le_coe.2 (ht.2.trans hr)).trans hq.le
    exact (fillH_eq_iff_isFilling_of_isClosed (isCompact_Icc.image_of_continuousOn hc).isBounded
      (isCompact_Icc.image_of_continuousOn hc).isClosed (QuantumZipper.fwdHull_mono.2 _)).1
        (hg.2.2 r ((ENNReal.coe_le_coe.2 hr).trans_lt hq))
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hWr q).subset_ball 0
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R
  have he : ∀ᶠ N : ℕ in atTop,
      (limUnder atTop fun k : ℕ =>
        (fcPrefixMap Γ q (zPt N) ω - 2 / (((k : ℂ) + 1) *
          (fcPrefixMap Γ q (zPt N) ω -
            fcPrefixMap Γ ((q : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal (zPt N) ω))).re) = W q := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hzK (r : ℝ) (hr : r ≤ q) : zPt N ∉ fwdHull Wr r := by
      intro hz
      have hb := hR (QuantumZipper.fwdHull_mono.1 hr hz)
      rw [Metric.mem_ball, dist_zero_right, norm_zPt] at hb
      have hNN : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hmap (r : ℝ) (hr : r ∈ Icc 0 (q : ℝ)) :
        fcPrefixMap Γ r.toNNReal (zPt N) ω = fwdMap Wr r (zPt N) + Wr r := by
      have hrq : r.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hr.2
      have hKe := hK r.toNNReal hrq
      rw [Real.coe_toNNReal _ hr.1] at hKe
      have hm : zPt N ∈ H \ fillH (Γ ω '' Icc 0 r.toNNReal) := by
        rw [← hKe]
        exact ⟨zPt_mem_H N, hzK r hr.2⟩
      rw [fcPrefixMap, indicator_of_mem (show ω ∈ {ω | zPt N ∈
        H \ fillH (Γ ω '' Icc 0 r.toNNReal)} from hm)]
      have hHP := isHPHull_fwdHull hWr hr.1
      have hM := ConformalImage.isMapOut_mapOut hHP
      rw [← hKe]
      exact IsMapOut.eqOn hHP hM (isMapOut_fwdMap hWr hWr0 hr.1)
        ⟨zPt_mem_H N, hzK r hr.2⟩
    have ht := tendsto_drvQuot hWr hqp (zPt_mem_H N) (hzK q le_rfl) hmap
    simpa only [Wr, Real.toNNReal_coe] using ht.limUnder_eq
  simp only [fcReadDriver, hq0, ite_false]
  exact (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)).limUnder_eq

open Sec2.Assembly

/-- The measurable driver read from the path, frozen at its lifetime and decoded
through the existing continuous-path code. It is continuous at every sample. -/
def fcTraceDriver (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) (q : ℝ≥0) (ω : Ω) : ℝ :=
  FCDet.decDrv (enc (fun t => StoppedK2.frz U (fcReadDriver Γ) t ω)) q

omit mΩ in
theorem continuous_fcTraceDriver (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) (ω : Ω) :
    Continuous (fcTraceDriver Γ U · ω) := FCDet.continuous_decDrv _

omit mΩ in
theorem fcTraceDriver_zero (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) (ω : Ω) :
    fcTraceDriver Γ U 0 ω = 0 := FCDet.decDrv_zero _

/-- The freezing operation is measurable even at its random terminal time. -/
theorem measurable_fcTraceDriver {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hc : ∀ ω, Continuous (Γ ω)) (hm : ∀ t, Measurable fun ω => Γ ω t)
    (h0 : ∀ ω, Γ ω 0 = 0) (hU : Measurable U) (q : ℝ≥0) :
    Measurable (fcTraceDriver Γ U q) := by
  let 𝓕 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  have ha : AdaptedBefore 𝓕 U (fcReadDriver Γ) := fun t A hA =>
    (measurableSet_lt measurable_const hU).inter ((measurable_fcReadDriver hc hm h0 t) hA)
  exact (FCDet.measurable_decDrv q).comp (Sec2.Assembly2.measurable_enc.comp
    (measurable_pi_iff.2 fun t => StoppedK2.measurable_frz ha t))

omit mΩ in
/-- On an available path, the frozen reconstruction agrees with its actual
continuous driver before the lifetime. The endpoint is recovered by left limits. -/
theorem fcTraceDriver_eq {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} {ω : Ω} {W : ℝ≥0 → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hg : IsGeneratingTrace W (U ω) (Γ ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < U ω) : fcTraceDriver Γ U q ω = W q := by
  let Y : ℝ≥0 → Ω → ℝ := fun t _ => W t
  have he (t : ℝ≥0) : StoppedK2.frz U (fcReadDriver Γ) t ω = StoppedK2.frz U Y t ω := by
    unfold StoppedK2.frz
    split_ifs with ht
    · exact fcReadDriver_eq hW hW0 hg ht
    · congr 1
      funext k
      unfold Sec7.Aux122Disint.killAt
      split_ifs with hk
      · exact fcReadDriver_eq hW hW0 hg hk
      · rfl
  have hU0 : 0 < U ω := lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ q) hq
  have hc : Continuous (StoppedK2.frz U Y · ω) := by
    by_cases htop : U ω = ⊤
    · simpa only [StoppedK2.frz_of_eq_top htop, Y] using hW
    · exact StoppedK2.continuous_frz hU0 htop hW.continuousOn
  have hz : StoppedK2.frz U Y 0 ω = 0 := by
    rw [StoppedK2.frz_of_lt (by simpa using hU0)]
    exact hW0
  unfold fcTraceDriver
  simp_rw [he]
  rw [FCDet.decDrv_enc hc hz]
  exact StoppedK2.frz_of_lt hq

end InteractingSLE.Restart.FCPlumb
