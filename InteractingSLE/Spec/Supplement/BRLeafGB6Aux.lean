/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BRLeafTips
import InteractingSLE.Spec.Supplement.BRLeafCond
import InteractingSLE.Spec.Supplement.BRLeafLift
import InteractingSLE.Spec.Sec5.CfRegQ
import InteractingSLE.Spec.Supplement.GB6TraceLaw
import InteractingSLE.Spec.Sec7.LocalExtGChart
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# GB6 for the flow's own prefix: pathwise and kernel lemmas

Packet PROVE-T14-BR (for `Theorem14.GW2Later.GB6PrefixPairStatement`).

* `pieceRegular_of_lt`, `mem_H_of_isInteriorStop`, `loewner_stopDrv_eq`: a flow piece stopped at a deterministic own
  time `s` before its lifetime is a regular piece; an interior stop (`GW2Later.IsInteriorStop`) means `α(s) ∈ ℍ`; the
  Loewner chart of the stopped driver at `s` is the one of the driver.
* `ae_isGB6KernelGood_gffLaw`: under the GFF law of a sorted admissible word with tail data at `(jL, jR)`, the GB6
  canonical-space point `(g, F (c, g), (jL, jR))` is good (`gb6_kernel` pushed to the law).
* `mem_counterflowCompletedRange_of_sphereInv`: a chart point identified with a physical counterflow point lies in the
  completed counterflow range.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace BRLeaf

open Exist.StagedLaw GW2Later

section Piece

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ}

/-- A generating trace up to `ζ` generates up to every earlier horizon. -/
theorem isGeneratingTrace_of_le (hα : IsGeneratingTrace w ζ α) {S : ℝ≥0∞} (hS : S ≤ ζ) : IsGeneratingTrace w S α :=
  ⟨hα.1, hα.2.1.mono fun _ ht => le_trans ht hS, fun t ht => hα.2.2 t (lt_of_lt_of_le ht hS)⟩

/-- **A piece stopped before its lifetime is regular.** -/
theorem pieceRegular_of_lt (hα : IsGeneratingTrace w ζ α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {s : ℝ≥0∞} (hs : s < ζ) : GW1P.PieceRegular w s :=
  ⟨hw0, hw.mono fun _ ht => lt_of_le_of_lt ht hs, α, isGeneratingTrace_of_le hα hs.le,
    fun h => absurd (h ▸ hs) (not_lt.2 le_top)⟩

/-- **An interior stop is an interior trace point.** -/
theorem mem_H_of_isInteriorStop (hα : IsGeneratingTrace w ζ α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {s : ℝ≥0∞} (hs : s < ζ) (hint : IsInteriorStop w s) : α s.toNNReal ∈ H := by
  obtain ⟨p, hpH, hp⟩ := hint
  have hsT : s ≠ ⊤ := ne_top_of_lt hs
  have hs' : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by rwa [ENNReal.coe_toNNReal hsT]
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs'
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg _) hst₂.le
  have hreg := pieceRegular_of_lt hα hw hw0 hs
  have hc1 : ContinuousOn (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) s).toNNReal) (Icc 0 t₂) :=
    hreg.continuous_stoppedReal.1.continuousOn
  have hc2 : ContinuousOn (fun r : ℝ => w r.toNNReal) (Icc 0 t₂) := by
    refine hw.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    refine lt_of_le_of_lt ?_ ht₂
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal t₂
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)
  have heq : EqOn (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) s).toNNReal) (fun r : ℝ => w r.toNNReal)
      (Icc 0 (s.toNNReal : ℝ)) := fun r hr => by
    have hle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ s := by
      rw [← ENNReal.coe_toNNReal hsT]
      exact ENNReal.coe_le_coe.2 (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)
    simp only [min_eq_left hle, ENNReal.toNNReal_coe]
  have hF : ∀ z, fwdMapInv (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) s).toNNReal) (s.toNNReal : ℝ) z =
      fwdMapInv (fun r : ℝ => w r.toNNReal) (s.toNNReal : ℝ) z :=
    LocalExt.fwdMapInv_congr_of_continuousOn hc1 hc2 (NNReal.coe_nonneg _) hst₂ heq
  have htip := hα.tendsto_fwdMapInv_mul_I hw hw0 hs'
  have hp' : Tendsto (fun y : ℝ => fwdMapInv (fun r : ℝ => w r.toNNReal) (s.toNNReal : ℝ) (y * Complex.I))
      (𝓝[>] 0) (𝓝 p) := by
    refine hp.congr fun y => ?_
    show fwdMapInv _ _ _ = _
    exact hF _
  rw [tendsto_nhds_unique htip hp']
  exact hpH

/-- **The Loewner chart of a piece stopped at `s` before its lifetime** is the chart of the piece at `s`. -/
theorem loewner_stopDrv_eq (hα : IsGeneratingTrace w ζ α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {s : ℝ≥0∞} (hs : s < ζ) :
    Chart.id.loewner (stopDrv s (w, ζ)) (stopTime s (w, ζ)) =
      Chart.id.loewner (fun r : ℝ => w r.toNNReal) (s.toNNReal : ℝ) := by
  have hm : min s ζ = s := min_eq_left hs.le
  have hsT : s ≠ ⊤ := ne_top_of_lt hs
  have hs' : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by rwa [ENNReal.coe_toNNReal hsT]
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs'
  have hreg := pieceRegular_of_lt hα hw hw0 hs
  have hsd : stopDrv s (w, ζ) = fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) s).toNNReal := by
    funext r; simp only [stopDrv, retOf, hm]
  have hst : stopTime s (w, ζ) = (s.toNNReal : ℝ) := by simp only [stopTime, hm]
  rw [hsd, hst]
  have hc1 : ContinuousOn (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) s).toNNReal) (Icc 0 t₂) :=
    hreg.continuous_stoppedReal.1.continuousOn
  have hc2 : ContinuousOn (fun r : ℝ => w r.toNNReal) (Icc 0 t₂) := by
    refine hw.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    refine lt_of_le_of_lt ?_ ht₂
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal t₂
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)
  refine LocalExt.id_loewner_congr hc1 hc2 (NNReal.coe_nonneg _) hst₂ fun r hr => ?_
  have hle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ s := by
    rw [← ENNReal.coe_toNNReal hsT]
    exact ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)
  simp only [min_eq_left hle, ENNReal.toNNReal_coe]

end Piece

/-! ### The GB6 kernel-good event under a word's GFF law -/

section Kernel

open Supp8.GB6 Restart Sec2.Assembly

/-- **The GB6 canonical-space point of a word's GFF sample is good** (`gb6_kernel` under the law of
`g ↦ (g, F (c, g), (jL, jR))`). -/
theorem ae_isGB6KernelGood_gffLaw {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hC : CompleteSixteenDivStatement)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode (16 / κ) 0 F)
    {c : BoundaryWord} (hcs : c.IsSorted) (hadm : IsGB6AdmData κ c) {jL jR : ℝ} (htail : IsGB6TailData κ c jL jR) :
    ∀ᵐ g ∂c.gffLaw, IsGB6KernelGood (g, F (c, g), (jL, jR)) := by
  have hκ' : 0 < 16 / κ := by positivity
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (c, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  set ι : DistOn upperHalfPlaneOpens → GB6Space := fun g => (g, F (c, g), (jL, jR)) with hιdef
  have hι : Measurable ι := measurable_id.prodMk (hFc.prodMk measurable_const)
  set Q' := c.gffLaw.map ι with hQ'
  have : IsProbabilityMeasure Q' := (Measure.isProbabilityMeasure_map_iff hι.aemeasurable).2 inferInstance
  have hgff : IsGFFWithBoundaryData Q' gb6Field c.fn c.jumps := by
    refine Sec5.CfRegQ.isGFFWithBoundaryData_of_map_eq (c.isGFFWithBoundaryData_gffLaw hcs) measurable_gb6Field ?_
    rw [hQ', Measure.map_map measurable_gb6Field hι]
    rfl
  have hgood₀ := ae_isGoodDrvCode_gffLaw hκ' hF hcs
  have hgood : ∀ᵐ x ∂Q', IsGoodDrvCode (gb6Code x) := by
    refine (ae_map_iff hι.aemeasurable (measurable_gb6Code measurableSet_isGoodDrvCode)).2 ?_
    exact hgood₀
  have hmatch : ∀ᵐ x ∂Q', IsDriverCodeMatch (F (c, gb6Field x)) (fun t => gb6WCl t x) (gb6L x) := by
    have hE := measurableSet_driverCodeMatch (G := fun p : Unit × GB6Space => F (c, gb6Field p.2))
      (hF.1.comp (measurable_const.prodMk (measurable_gb6Field.comp measurable_snd))) measurable_gb6WCl
      measurable_gb6L
    have hE' : MeasurableSet {x : GB6Space | IsDriverCodeMatch (F (c, gb6Field x)) (fun t => gb6WCl t x)
        (gb6L x)} := (measurable_const.prodMk measurable_id : Measurable fun x : GB6Space => ((), x)) hE
    refine (ae_map_iff hι.aemeasurable hE').2 ?_
    filter_upwards [hgood₀] with g hg
    exact isDriverCodeMatch_drvDec hg
  have htailQ : ∀ᵐ x ∂Q', IsGB6TailData κ c (gb6JL x) (gb6JR x) := by
    have hm : Measurable fun x : GB6Space => (c, gb6JL x, gb6JR x) :=
      measurable_const.prodMk (measurable_gb6JL.prodMk measurable_gb6JR)
    refine (ae_map_iff hι.aemeasurable (hm (measurableSet_isGB6TailData κ))).2 ?_
    exact Eventually.of_forall fun _ => htail
  have hfl : IsFlowLineDriver (16 / κ) c.fn c.jumps 0 Q' gb6Field gb6WCl gb6L :=
    hF.2.1 c hcs Q' gb6Field gb6WCl gb6L hgff measurable_gb6WCl measurable_gb6L continuousOn_gb6WCl hmatch
  have hk := (gb6_kernel hκ hκ4 hC hF hcs hadm hgff hfl hgood hmatch htailQ).2
  exact (ae_map_iff hι.aemeasurable measurableSet_isGB6KernelGood).1 hk

end Kernel

/-! ### Points of the completed counterflow range -/

/-- A chart point identified with the physical counterflow point `sphereInv (γ t)` is in the completed range. -/
theorem mem_counterflowCompletedRange_of_sphereInv {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ≥0} {p : ℂ}
    (h : Supp8.GB6.sphereInv (γ t : OnePoint ℂ) = (p : OnePoint ℂ)) : p ∈ counterflowCompletedRange W := by
  by_cases h0 : γ t = 0
  · rw [h0, Supp8.GB6.sphereInv_coe] at h
    simp only [↓reduceIte] at h
    exact absurd h.symm (OnePoint.coe_ne_infty p)
  · rw [Supp8.GB6.sphereInv_coe_of_ne h0] at h
    have hp : p = -(γ t)⁻¹ := (OnePoint.coe_injective h).symm
    rw [counterflowCompletedRange]
    refine mem_union_left _ ?_
    rw [CounterflowRange.tipSet_infinitySourceChart_top hγ hW hW0]
    exact ⟨t, h0, hp⟩

end BRLeaf

end Theorem14

end InteractingSLE
