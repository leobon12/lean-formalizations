/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepMean
import InteractingSLE.Spec.Sec7.PocketSideInResidualLaw
import InteractingSLE.GFF.LocalSets.Prop39

/-!
# Constructing the global old-chart increment law from retained kernels

PROVE-POCKET-SIDEIN. Use the uncut global increment before restricting its
identity to a geometric candidate event. The residual field is the actual
old-chart pullback. Its mean is almost surely the exact pulled difference
of the two physical means. The retained physical kernels and record
inclusions remain source inputs. No margin or side-height bound is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- The uncut increment in the old coordinate. A future-dependent collar
event does not enter this definition. -/
def globalOldChartAddedSet {Ω : Type*} (old current : Ω → Chart) (ω : Ω) : Set ℂ :=
  H \ Restart.MarkovChart.chartPre (old ω) (current ω).dom

/-- The complement of the global increment is the full pulled current domain. -/
theorem compl_globalOldChartAddedSet {Ω : Type*} (old current : Ω → Chart) (ω : Ω) :
    H \ globalOldChartAddedSet old current ω =
      Restart.MarkovChart.chartPre (old ω) (current ω).dom :=
  sdiff_sdiff_cancel_left (Restart.MarkovChart.chartPre_subset_H _ _)

/-- The global increment has the regularity needed for the local-set law. -/
theorem globalOldChartAddedSet_regular {Ω : Type*} {old current : Ω → Chart}
    (hOld : ∀ ω, (old ω).IsConformal) (ω : Ω) :
    globalOldChartAddedSet old current ω ⊆ H ∧
      IsOpen (H \ globalOldChartAddedSet old current ω) := by
  refine ⟨sdiff_subset, ?_⟩
  rw [compl_globalOldChartAddedSet]
  exact Restart.MarkovChart.isOpen_chartPre (hOld ω) (current ω).dom.isOpen

/-- The two physical retained kernels produce the global increment law.
The current record must contain the increment's germ; it measures both
physical means. No germ measurability of their pulled difference is assumed.
The conclusion may subsequently be restricted to any candidate event `M`. -/
theorem hasOldChartIncrementLaw_of_retained_kernels
    {Ω : Type*} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ)
    {old current : Ω → Chart} (hOld : ∀ ω, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] {ω | z ∈ (old ω).dom})
    (hfwd : ∀ z, Measurable[ℋ₀]
      ({ω | z ∈ (old ω).dom}.indicator fun ω => (old ω).1 z))
    (hNested : ∀ ω, ((current ω).dom : Set ℂ) ⊆ (old ω).dom)
    {h gOld gNow : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hMeanOld : Measurable[ℋ₁] gOld) (hMeanNow : Measurable[ℋ₁] gNow)
    (hHarmOld : ∀ᵐ ω ∂P, IsHarmonicDistOn (gOld ω) (old ω).dom)
    (hHarmNow : ∀ᵐ ω ∂P, IsHarmonicDistOn (gNow ω) (current ω).dom)
    (hOldKernel : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => ((old ω).dom : Set ℂ))
      (fun ω => h ω - gOld ω))
    (hCurrentKernel : IsCondZeroBoundaryGFF P ℋ₁ (fun ω => ((current ω).dom : Set ℂ))
      (fun ω => h ω - gNow ω))
    (hAdded : Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet old current))
    (hGerm : germSigma (globalOldChartAddedSet old current)
      (fun ω => Chart.pullField (hOld ω) (h ω - gOld ω)) ≤ ℋ₁) (M : Set Ω) :
    HasOldChartIncrementLaw P M old current gOld gNow := by
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  have hdom₁ : ∀ z, MeasurableSet[ℋ₁] {ω | z ∈ (old ω).dom} :=
    fun z => hInfo _ (hdom z)
  have hfwd₁ : ∀ z, Measurable[ℋ₁]
      ({ω | z ∈ (old ω).dom}.indicator fun ω => (old ω).1 z) :=
    fun z => (hfwd z).mono hInfo le_rfl
  have hSubOld : Measurable fun ω => h ω - gOld ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hh).sub
        ((LQGMetric.measurable_distOn_apply φ).comp (hMeanOld.mono hℋ₁ le_rfl))
  have hSubNow : Measurable fun ω => h ω - gNow ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hh).sub
        ((LQGMetric.measurable_distOn_apply φ).comp (hMeanNow.mono hℋ₁ le_rfl))
  let residual := fun ω => Chart.pullField (hOld ω) (h ω - gOld ω)
  let increment := fun ω => Chart.pullField (hOld ω) (gNow ω - gOld ω)
  have hResidual : Measurable residual := measurable_pullField_of_retained_chart hOld
    (fun z => hℋ₀ _ (hdom z)) (fun z => (hfwd z).mono hℋ₀ le_rfl) hSubOld
  have hResidualLaw := Chart.isCondZeroBoundaryGFF_pullField_random
    hℋ₀ hOld hdom hfwd hSubOld hOldKernel
  have hZero : IsZeroBoundaryGFF upperHalfPlaneOpens residual P :=
    isZeroBoundaryGFF_of_conditional_halfPlane hℋ₀ hResidual hResidualLaw
  have hDiff : Measurable[ℋ₁] fun ω => gNow ω - gOld ω := by
    let : MeasurableSpace Ω := ℋ₁
    exact LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hMeanNow).sub
        ((LQGMetric.measurable_distOn_apply φ).comp hMeanOld)
  have hIncrement : Measurable[ℋ₁] increment :=
    @measurable_pullField_of_retained_chart Ω ℋ₁ old hOld hdom₁ hfwd₁ _ hDiff
  have hRegular : ∀ᵐ ω ∂P, globalOldChartAddedSet old current ω ⊆ H ∧
      IsOpen (H \ globalOldChartAddedSet old current ω) :=
    Eventually.of_forall (globalOldChartAddedSet_regular hOld)
  have hHarmonic : ∀ᵐ ω ∂P, IsHarmonicDistOn (increment ω)
      (H \ globalOldChartAddedSet old current ω) := by
    filter_upwards [hHarmOld, hHarmNow] with ω hO hN
    rw [compl_globalOldChartAddedSet]
    exact Restart.MarkovChart.isHarmonicDistOn_pullField (hOld ω)
      (IsHarmonicDistOn.sub' (current ω).dom.isOpen hN
        (IsHarmonicDistOn.mono hO (hNested ω)))
  have hDifference (ω : Ω) : residual ω - increment ω =
      Chart.pullField (hOld ω) (h ω - gNow ω) := by
    ext φ
    simp only [residual, increment, sub_apply, Chart.pullField_apply]
    ring
  have hCurrentLaw := isCondZeroBoundaryGFF_pullField_subdomain hℋ₁ hOld hdom₁ hfwd₁
    (fun ω => (current ω).dom.isOpen) (fun ω => (hNested ω).trans (hOld ω).dom_subset)
    (fun ω => by rw [sdiff_eq_empty.2 (hNested ω)]; exact isOpen_empty)
    hSubNow hCurrentKernel
  have hKernel : IsCondZeroBoundaryGFF P ℋ₁
      (fun ω => H \ globalOldChartAddedSet old current ω)
      (fun ω => residual ω - increment ω) := by
    simpa only [hDifference, compl_globalOldChartAddedSet] using hCurrentLaw
  obtain ⟨g, hg, hEq⟩ := exists_localSetMean_eq_of_retained_kernel hℋ₁ hZero hAdded
    hIncrement hGerm hRegular hHarmonic hKernel
  refine ⟨globalOldChartAddedSet old current, residual, g, hZero,
    hAdded.mono hℋ₁ le_rfl, hRegular, hg, ?_⟩
  filter_upwards [hEq] with ω hEq hω
  refine ⟨?_, fun _ => hEq⟩
  simp only [globalOldChartAddedSet, oldChartAddedSet, ite_eq_left hω]

end InteractingSLE.Sec7.PocketStopSide
