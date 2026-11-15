/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlAdded
import InteractingSLE.Spec.Sec7.R5OutEngine

/-!
# The conditioned increment law in a reference component

PROVE-R5-OUTER, R88. The reference kernel may live on a disconnected
complement. A chart of one of its components still reads a zero-boundary
GFF on the half-plane. This follows directly from the existing random-chart
transport with an open complementary piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Out

open LocalSets PocketStopSide WholeField R5Enl

/-- Nested retained kernels give the increment law in a component chart. -/
theorem hasOldChartIncrementLaw_of_component_kernels
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
    {Uold : Ω → Set ℂ} (hUoldo : ∀ ω, IsOpen (Uold ω))
    (hUoldH : ∀ ω, Uold ω ⊆ H)
    (hCut : ∀ ω, IsOpen (Uold ω \ (old ω).dom))
    (hOldSub : ∀ ω, ((old ω).dom : Set ℂ) ⊆ Uold ω)
    (hOldKernel : IsCondZeroBoundaryGFF P ℋ₀ Uold (fun ω => h ω - gOld ω))
    (hCurrentKernel : IsCondZeroBoundaryGFF P ℋ₁ (fun ω => ((current ω).dom : Set ℂ))
      (fun ω => h ω - gNow ω))
    (hAdded : Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet old current)) (M : Set Ω) :
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
  have hResidualLaw' := isCondZeroBoundaryGFF_pullField_subdomain hℋ₀ hOld hdom hfwd
    hUoldo hUoldH hCut hSubOld hOldKernel
  have hPre : (fun ω => Restart.MarkovChart.chartPre (old ω) (Uold ω)) = fun _ => H := by
    funext ω
    ext z
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, hOldSub ω ((hOld ω).inv_mem_dom hz)⟩⟩
  have hResidualLaw : IsCondZeroBoundaryGFF P ℋ₀ (fun _ => H) residual := by
    rw [hPre] at hResidualLaw'
    exact hResidualLaw'
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
  obtain ⟨g, hg, hEq⟩ := exists_localSetMean_eq_of_retained_kernel_noGerm hℋ₁ hZero hAdded
    hIncrement hRegular hHarmonic hKernel
  refine ⟨globalOldChartAddedSet old current, residual, g, hZero,
    hAdded.mono hℋ₁ le_rfl, hRegular, hg, ?_⟩
  filter_upwards [hEq] with ω hEq hω
  refine ⟨?_, fun _ => hEq⟩
  simp only [globalOldChartAddedSet, oldChartAddedSet, ite_eq_left hω]


variable {Ω : Type*} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω}

/-- The reference-component increment law conditioned on the event where the chart is defined. -/
theorem hasOldChartIncrementLawOn_of_component_kernels [IsProbabilityMeasure P]
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[ℋ₀] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    {U : Ω → Set ℂ} (hUo : ∀ ω ∈ G, IsOpen (U ω)) (hNested : ∀ ω ∈ G, U ω ⊆ (old ω).dom)
    {h gOld gNow : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hMeanOld : Measurable[ℋ₁] gOld) (hMeanNow : Measurable[ℋ₁] gNow)
    (hHarmOld : ∀ᵐ ω ∂P, ω ∈ G → IsHarmonicDistOn (gOld ω) (old ω).dom)
    (hHarmNow : ∀ᵐ ω ∂P, ω ∈ G → IsHarmonicDistOn (gNow ω) (U ω))
    {Uold : Ω → Set ℂ} (hUoldo : ∀ ω ∈ G, IsOpen (Uold ω))
    (hUoldH : ∀ ω ∈ G, Uold ω ⊆ H)
    (hCut : ∀ ω ∈ G, IsOpen (Uold ω \ (old ω).dom))
    (hOldSub : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ Uold ω)
    (hOldKernel : IsCondZeroBoundaryGFF P ℋ₀ Uold (fun ω => h ω - gOld ω))
    (hCurrentKernel : IsCondZeroBoundaryGFF P ℋ₁ U (fun ω => h ω - gNow ω))
    (hAdded : Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet (oldOn G old) (curOn G U)))
    {M : Set Ω} (hMG : M ⊆ G) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = U ω) :
    HasOldChartIncrementLawOn P M old current gOld gNow := by
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  have hGm : MeasurableSet G := hℋ₀ _ hG
  have hUH : ∀ ω ∈ G, U ω ⊆ H := fun ω hω => (hNested ω hω).trans (hOld ω hω).dom_subset
  have hcurG : ∀ ω ∈ G, ((curOn G U ω).dom : Set ℂ) = U ω := fun ω hω =>
    dom_curOn_of_mem hω (hUo ω hω) (hUH ω hω)
  refine ⟨G, hGm, hMG, fun hP => ?_⟩
  have hNested' : ∀ ω, ((curOn G U ω).dom : Set ℂ) ⊆ (oldOn G old ω).dom := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [hcurG ω hω, oldOn_of_mem hω]
      exact hNested ω hω
    · rw [dom_curOn_of_notMem hω, oldOn_of_notMem hω, dom_chart_id]
  have hHarmOld' : ∀ᵐ ω ∂P[|G], IsHarmonicDistOn (gOld ω) (oldOn G old ω).dom := by
    refine ae_cond_of_ae hGm ?_
    filter_upwards [hHarmOld] with ω hω hG'
    rw [oldOn_of_mem hG']
    exact hω hG'
  have hHarmNow' : ∀ᵐ ω ∂P[|G], IsHarmonicDistOn (gNow ω) (curOn G U ω).dom := by
    refine ae_cond_of_ae hGm ?_
    filter_upwards [hHarmNow] with ω hω hG'
    rw [hcurG ω hG']
    exact hω hG'
  classical
  let UoldG : Ω → Set ℂ := fun ω => if ω ∈ G then Uold ω else H
  have hOldKernel' : IsCondZeroBoundaryGFF (P[|G]) ℋ₀ UoldG
      (fun ω => h ω - gOld ω) := by
    refine isCondZeroBoundaryGFF_cond hℋ₀ hG
      (measurable_sub_of_le hℋ₁ hh hMeanOld) hOldKernel ?_
    exact Eventually.of_forall fun ω hω => (ite_eq_left hω).symm
  have hUoldo' : ∀ ω, IsOpen (UoldG ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [UoldG, ite_eq_left hω] using hUoldo ω hω
    · simpa only [UoldG, ite_eq_right hω] using QuantumZipper.isOpen_H
  have hUoldH' : ∀ ω, UoldG ω ⊆ H := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [UoldG, ite_eq_left hω] using hUoldH ω hω
    · simpa only [UoldG, ite_eq_right hω] using (Subset.rfl : H ⊆ H)
  have hCut' : ∀ ω, IsOpen (UoldG ω \ (oldOn G old ω).dom) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [UoldG, ite_eq_left hω, oldOn_of_mem hω] using hCut ω hω
    · rw [show UoldG ω = H from ite_eq_right hω,
        oldOn_of_notMem hω, dom_chart_id, sdiff_self]
      exact isOpen_empty
  have hOldSub' : ∀ ω, ((oldOn G old ω).dom : Set ℂ) ⊆ UoldG ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [UoldG, ite_eq_left hω, oldOn_of_mem hω] using hOldSub ω hω
    · rw [show UoldG ω = H from ite_eq_right hω, oldOn_of_notMem hω, dom_chart_id]
  have hCurrentKernel' : IsCondZeroBoundaryGFF (P[|G]) ℋ₁ (fun ω => ((curOn G U ω).dom : Set ℂ))
      (fun ω => h ω - gNow ω) :=
    isCondZeroBoundaryGFF_cond hℋ₁ (hInfo _ hG) (measurable_sub_of_le hℋ₁ hh hMeanNow) hCurrentKernel
      (Eventually.of_forall fun ω hG' => (hcurG ω hG').symm)
  have hlaw := @hasOldChartIncrementLaw_of_component_kernels Ω ℋ₀ ℋ₁ mΩ (P[|G]) hP hInfo hℋ₁
    (oldOn G old) (curOn G U) (isConformal_oldOn hOld)
    (fun z => measurableSet_mem_dom_oldOn hG (hdom z))
    (fun z => measurable_indicator_fwd_oldOn hG (hfwd z)) hNested' h gOld gNow hh hMeanOld hMeanNow
    hHarmOld' hHarmNow' UoldG hUoldo' hUoldH' hCut' hOldSub' hOldKernel' hCurrentKernel' hAdded M
  refine HasOldChartIncrementLaw.congr_on hlaw (Eventually.of_forall fun ω hM => ?_)
  exact ⟨oldOn_of_mem (hMG hM), by rw [hcurG ω (hMG hM), hcur ω hM], rfl, rfl⟩


end InteractingSLE.Sec7.R5Out
