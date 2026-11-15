/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBBdry
import InteractingSLE.GFF.PushforwardLoewner
import InteractingSLE.Spec.Restart.ChartMeasRandom

/-!
# Measurable boundary values of GB6's relative map

The random-open-domain limit theorem already proved for chart transport gives
measurability of the boundary extension, also at random real points. Only
measurability of the original driver's evaluations is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Supp8.GB6.CoordB

/-- The relative domain is the inversion of the original unbounded component. -/
theorem mem_relDomain_iff (U : ℝ → ℝ) (s : ℝ) (z : ℂ) :
    z ∈ relDomain U s ↔ z ∈ H ∧ -z⁻¹ ∉ QuantumZipper.fwdHull U s := by
  constructor
  · rintro ⟨hz, hza⟩
    exact ⟨hz, fun h => hza ⟨-z⁻¹, h, neg_inv_neg_inv z⟩⟩
  · rintro ⟨hz, hzk⟩
    refine ⟨hz, ?_⟩
    rintro ⟨w, hw, he⟩
    have : -z⁻¹ = w := by rw [← he, neg_inv_neg_inv]
    exact hzk (this ▸ hw)

theorem isOpen_relDomain {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s) :
    IsOpen (relDomain U s) := by
  apply isOpen_iff_mem_nhds.2
  intro z hz
  obtain ⟨hzH, hzK⟩ := (mem_relDomain_iff U s z).1 hz
  have hI : ContinuousAt (fun w : ℂ => -w⁻¹) z :=
    (continuousAt_inv₀ (ne_zero_of_mem_H hzH)).neg
  have hD : -z⁻¹ ∈ H \ QuantumZipper.fwdHull U s := ⟨neg_inv_mem_H hzH, hzK⟩
  have he : ∀ᶠ w in 𝓝 z, -w⁻¹ ∈ H \ QuantumZipper.fwdHull U s := hI.eventually
    ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hU hs).mem_nhds hD)
  filter_upwards [QuantumZipper.isOpen_H.mem_nhds hzH, he] with w hwH hwD
  exact (mem_relDomain_iff U s w).2 ⟨hwH, hwD.2⟩

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {V : ℝ≥0 → Ω → ℝ}
  (hVm : ∀ t, Measurable (V t)) (hVc : ∀ ω, Continuous (V · ω)) (hV0 : ∀ ω, V 0 ω = 0)

include hVm hVc hV0

/-- A fixed-point domain event of the relative chart is measurable. -/
theorem measurableSet_mem_relDomain (s : ℝ≥0) (z : ℂ) :
    MeasurableSet {ω | z ∈ relDomain (Ito.rpath (V · ω)) s} := by
  let 𝓕 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  by_cases hzH : z ∈ H
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) s} =
        {ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom} := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, true_and]
      change _ ↔ -z⁻¹ ∈ (Chart.id.loewner (Ito.rpath (V · ω)) s).dom
      rw [← SetLike.mem_coe, loewner_dom_eq (Chart.continuous_rpath_of_continuous (hVc ω))
        (Chart.rpath_zero_of (hV0 ω)) s.coe_nonneg]
      exact ⟨fun h => ⟨neg_inv_mem_H hzH, h⟩, fun h => h.2⟩
    rw [he]
    exact Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := 𝓕) (fun t => hVm t) hVc hV0 s _
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) s} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, false_and, mem_empty_iff_false]
    rw [he]
    exact MeasurableSet.empty

/-- Fixed-point evaluations of the relative chart on its domain are measurable. -/
theorem measurable_indicator_relMap (s : ℝ≥0) (z : ℂ) :
    Measurable ({ω | z ∈ relDomain (Ito.rpath (V · ω)) s}.indicator
      fun ω => relMap (Ito.rpath (V · ω)) s z) := by
  let 𝓕 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  by_cases hzH : z ∈ H
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) s} =
        {ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom} := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, true_and]
      change _ ↔ -z⁻¹ ∈ (Chart.id.loewner (Ito.rpath (V · ω)) s).dom
      rw [← SetLike.mem_coe, loewner_dom_eq (Chart.continuous_rpath_of_continuous (hVc ω))
        (Chart.rpath_zero_of (hV0 ω)) s.coe_nonneg]
      exact ⟨fun h => ⟨neg_inv_mem_H hzH, h⟩, fun h => h.2⟩
    have hm := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := 𝓕)
      (fun t => hVm t) hVc hV0 s (-z⁻¹)
    have hEq : ({ω | z ∈ relDomain (Ito.rpath (V · ω)) s}.indicator
        fun ω => relMap (Ito.rpath (V · ω)) s z) =
        fun ω => -(({ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom}.indicator
          fun ω => (Chart.loewnerChartAt V s ω).1 (-z⁻¹)) ω)⁻¹ := by
      funext ω
      rw [he]
      by_cases hω : -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom
      · rw [indicator_of_mem (show ω ∈ {ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom} from hω),
          indicator_of_mem (show ω ∈ {ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom} from hω)]
        rfl
      · rw [indicator_of_notMem (show ω ∉ {ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom} from hω),
          indicator_of_notMem (show ω ∉ {ω | -z⁻¹ ∈ (Chart.loewnerChartAt V s ω).dom} from hω),
          inv_zero, neg_zero]
    rw [hEq]
    exact hm.inv.neg
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) s} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, false_and, mem_empty_iff_false]
    rw [he, indicator_empty]
    exact measurable_const

/-- Boundary values at measurable random safe points are measurable, including
real points. This reuses the existing random-domain forward-limit theorem. -/
theorem measurable_relBdry (s : ℝ≥0) {z : Ω → ℂ} (hz : Measurable z)
    (hsafe : ∀ ω, z ω ∈ relSafe (Ito.rpath (V · ω)) s) :
    Measurable fun ω => relBdry (Ito.rpath (V · ω)) s (z ω) :=
  Restart.measurable_of_tendsto_nhdsWithin
    (fun ω => isOpen_relDomain (Chart.continuous_rpath_of_continuous (hVc ω)) s.coe_nonneg)
    (measurableSet_mem_relDomain hVm hVc hV0 s)
    (measurable_indicator_relMap hVm hVc hV0 s) hz
    (fun ω => relSafe_subset_closure_relDomain _ _ (hsafe ω))
    (fun ω => tendsto_relMap_relBdry (Chart.continuous_rpath_of_continuous (hVc ω))
      (Chart.rpath_zero_of (hV0 ω)) s.coe_nonneg (hsafe ω))

/-- A measurable version restricted to any measurable safe event. -/
theorem measurable_indicator_relBdry (s : ℝ≥0) {E : Set Ω} (hE : MeasurableSet E)
    {z : Ω → ℂ} (hz : Measurable z) (hsafe : ∀ ω ∈ E, z ω ∈ relSafe (Ito.rpath (V · ω)) s) :
    Measurable (E.indicator fun ω => relBdry (Ito.rpath (V · ω)) s (z ω)) := by
  apply measurable_of_restrict_of_restrict_compl hE
  · have hm := measurable_relBdry (V := fun t (ω : E) => V t ω.val)
      (fun t => (hVm t).comp measurable_subtype_coe) (fun ω => hVc ω.val)
      (fun ω => hV0 ω.val) s (hz.comp measurable_subtype_coe) (fun ω => hsafe ω.val ω.property)
    convert hm using 1
    funext ω
    exact indicator_of_mem ω.property _
  · have he : ((Eᶜ).domRestrict (E.indicator fun ω => relBdry (Ito.rpath (V · ω)) s (z ω))) =
        fun _ : ↥(Eᶜ) => (0 : ℂ) := by
      funext ω
      exact indicator_of_notMem ω.property _
    rw [he]
    exact measurable_const

end Random

end InteractingSLE.Supp8.GB6.CoordB
