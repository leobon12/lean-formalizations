/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRGermLine
import InteractingSLE.Spec.Exist.StagedLaw2Flow

/-!
# GW4: actual line charts are read from the physical past

Freeze the relative driver at the clipped line clock. The existing physical
random-time reader makes every evaluation of this path measurable. The
parameterized Loewner-flow theorem then gives both the actual forward map
and its domain events, with no new chart-measurability hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar GW4Rel Supp8.RelSafe Supp8.GB6LineL Exist.StagedLaw

/-- The actual component chart's forward map and domain are measurable in
the original physical history at the line time. -/
theorem measurable_componentLineChart {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0) (z : ℂ) :
    Measurable[physFilt Frame.measurable_gw4Rec hWm ν t]
        (fun ω => (componentLineChart F Wd GT R V t ω).1 z) ∧
      MeasurableSet[physFilt Frame.measurable_gw4Rec hWm ν t]
        {ω | z ∈ (componentLineChart F Wd GT R V t ω).dom} := by
  let a : Ω → ℝ≥0 := fun ω => (lineClock F Wd GT V t ω).toNNReal
  have ha : Measurable[physFilt Frame.measurable_gw4Rec hWm ν t] a :=
    ENNReal.measurable_toNNReal.comp
      (Frame.measurable_min_physClockG hF hGT hWm hGTm hGTae hver t)
  have hRc := hver.1.1.2.1
  have hR0 := hver.1.1.2.2.1
  have hY : ∀ u : ℝ≥0, Measurable[physFilt Frame.measurable_gw4Rec hWm ν t]
      (fun ω => R (min u (a ω)) ω) := fun u =>
    measurable_apply_randTime hRc (a := lineClock F Wd GT V t) (measurable_const.min ha)
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self)
      (fun d B hB => Frame.measurableSet_le_min_inter_drv hF hGT hWm hGTm hGTae hver t le_rfl hB)
  let Y : Ω → ℝ → ℝ := fun ω s => R (min s.toNNReal (a ω)) ω
  have hYc : ∀ ω, Continuous (Y ω) := fun ω =>
    (hRc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hY0 : ∀ ω, Y ω 0 = 0 := by
    intro ω
    simpa only [Y, Real.toNNReal_zero, zero_min] using hR0 ω
  have hEq : ∀ ω, EqOn (wpath R ω) (Y ω) (Icc 0 (a ω : ℝ)) := by
    intro ω s hs
    dsimp only [wpath, Y]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hMap := @Exist.StagedLaw.measurable_fwdMap_param Ω
    (physFilt Frame.measurable_gw4Rec hWm ν t) Y hYc (fun s => hY s.toNNReal) hY0
    (fun ω => (a ω : ℝ)) (measurable_coe_nnreal_real.comp ha) (fun ω => (a ω).coe_nonneg)
    (fun _ => z) measurable_const
  constructor
  · have heq : (fun ω => (componentLineChart F Wd GT R V t ω).1 z) =
        fun ω => fwdMap (Y ω) (a ω) z :=
      funext fun ω => Ito.fwdMap_congr_of_eqOn (hEq ω)
    rw [heq]
    exact hMap.1
  · have hAlive : {ω | ∃ u, QuantumZipper.IsForwardSol (wpath R ω) z (a ω) u} =
        {ω | ∃ u, QuantumZipper.IsForwardSol (Y ω) z (a ω) u} := by
      ext ω
      exact exists_congr fun u => Ito.isForwardSol_iff_of_eqOn (hEq ω) u
    have hDom : {ω | z ∈ (componentLineChart F Wd GT R V t ω).dom} =
        {ω | 0 < z.im} ∩ {ω | ∃ u, QuantumZipper.IsForwardSol (wpath R ω) z (a ω) u} := by
      ext ω
      have hW : Continuous (wpath R ω) := (hRc ω).comp continuous_real_toNNReal
      have hW0 : wpath R ω 0 = 0 := by
        simpa only [wpath, Real.toNNReal_zero] using hR0 ω
      change z ∈ (Chart.id.loewner (wpath R ω) (a ω)).dom ↔
        (0 < z.im ∧ ∃ u, QuantumZipper.IsForwardSol (wpath R ω) z (a ω) u)
      rw [Chart.mem_dom_loewner_iff hW hW0 (a ω).coe_nonneg]
    rw [hDom, hAlive]
    exact (MeasurableSet.const _).inter hMap.2

/-- The indicator of the actual reference forward map on its domain has
the exact measurability used by the conditioned increment-law theorem. -/
theorem measurable_componentLineChart_indicator {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0)
    {G : Set Ω} (hG : MeasurableSet[physFilt Frame.measurable_gw4Rec hWm ν t] G) (z : ℂ) :
    Measurable[physFilt Frame.measurable_gw4Rec hWm ν t]
      ((G ∩ {ω | z ∈ (componentLineChart F Wd GT R V t ω).dom}).indicator
        fun ω => (componentLineChart F Wd GT R V t ω).1 z) := by
  obtain ⟨hf, hd⟩ := measurable_componentLineChart hF hGT hWm hGTm hGTae hver t z
  exact hf.indicator (hG.inter hd)

end InteractingSLE.Theorem14.GW4Fix
