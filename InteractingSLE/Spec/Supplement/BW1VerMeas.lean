/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBAtlas
import InteractingSLE.Spec.Supplement.GB6CoordBMeas

/-!
# GB6's relative-chart measurability at a measurable own time

Packet PROVE-BW1-INPUTS2. GB6's measurable relative-driver atlas (`Supp8.GB6.CoordB`) is stated for a fixed own time
`s` of the retained prefix; Proposition BW1's retained piece stops at a random time. This file proves the measurability
lemmas of `CoordB` with `s` replaced by a measurable `s : Ω → ℝ≥0`, through the Loewner chart at a random time
(`Chart.loewnerChartAtTime`); every deterministic lemma of `CoordB` is used sample by sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Supp8.GB6 Supp8.GB6.CoordB Sec7.PocketTraversal Sec7.Lemma71C

section Random

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {V : ℝ≥0 → Ω → ℝ}
  (hVm : ∀ t, Measurable (V t)) (hVc : ∀ ω, Continuous (V · ω)) (hV0 : ∀ ω, V 0 ω = 0)
  {s : Ω → ℝ≥0} (hs : Measurable s)

include hVm hVc hs in
/-- A continuous measurable driver stopped at a measurable time is measurable at every time. -/
theorem measurable_stoppedDrv (t : ℝ≥0) : Measurable (Chart.stoppedDrv V s t) := by
  have hU : Measurable (Function.uncurry V) := measurable_uncurry_of_continuous_of_measurable hVc hVm
  exact hU.comp ((measurable_const.min hs).prodMk measurable_id)

include hVm hVc hV0 hs in
/-- A fixed-point domain event of the relative chart at a measurable own time is measurable. -/
theorem measurableSet_mem_relDomain_rand (z : ℂ) :
    MeasurableSet {ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)} := by
  by_cases hzH : z ∈ H
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)} =
        {ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom} := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, true_and]
      change _ ↔ -z⁻¹ ∈ (Chart.id.loewner (Ito.rpath (V · ω)) (s ω)).dom
      rw [← SetLike.mem_coe, loewner_dom_eq (Chart.continuous_rpath_of_continuous (hVc ω))
        (Chart.rpath_zero_of (hV0 ω)) (s ω).coe_nonneg]
      exact ⟨fun h => ⟨neg_inv_mem_H hzH, h⟩, fun h => h.2⟩
    rw [he]
    exact Chart.measurableSet_mem_dom_loewnerChartAtTime le_rfl hVc hV0 hs
      (measurable_stoppedDrv hVm hVc hs) _
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, false_and, mem_empty_iff_false]
    rw [he]
    exact MeasurableSet.empty

include hVm hVc hV0 hs in
/-- Fixed-point evaluations of the relative chart at a measurable own time are measurable on its domain. -/
theorem measurable_indicator_relMap_rand (z : ℂ) :
    Measurable ({ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)}.indicator
      fun ω => relMap (Ito.rpath (V · ω)) (s ω) z) := by
  by_cases hzH : z ∈ H
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)} =
        {ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom} := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, true_and]
      change _ ↔ -z⁻¹ ∈ (Chart.id.loewner (Ito.rpath (V · ω)) (s ω)).dom
      rw [← SetLike.mem_coe, loewner_dom_eq (Chart.continuous_rpath_of_continuous (hVc ω))
        (Chart.rpath_zero_of (hV0 ω)) (s ω).coe_nonneg]
      exact ⟨fun h => ⟨neg_inv_mem_H hzH, h⟩, fun h => h.2⟩
    have hm := Chart.measurable_indicator_fwd_loewnerChartAtTime le_rfl hVc hV0 hs
      (measurable_stoppedDrv hVm hVc hs) (-z⁻¹)
    have hEq : ({ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)}.indicator
        fun ω => relMap (Ito.rpath (V · ω)) (s ω) z) =
        fun ω => -(({ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom}.indicator
          fun ω => (Chart.loewnerChartAtTime V s ω).1 (-z⁻¹)) ω)⁻¹ := by
      funext ω
      rw [he]
      by_cases hω : -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom
      · rw [indicator_of_mem (show ω ∈ {ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom} from hω),
          indicator_of_mem (show ω ∈ {ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom} from hω)]
        rfl
      · rw [indicator_of_notMem (show ω ∉ {ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom} from hω),
          indicator_of_notMem (show ω ∉ {ω | -z⁻¹ ∈ (Chart.loewnerChartAtTime V s ω).dom} from hω),
          inv_zero, neg_zero]
    rw [hEq]
    exact hm.inv.neg
  · have he : {ω | z ∈ relDomain (Ito.rpath (V · ω)) (s ω)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_relDomain_iff, hzH, false_and, mem_empty_iff_false]
    rw [he, indicator_empty]
    exact measurable_const

include hVm hVc hV0 hs in
/-- Boundary values of the relative chart at a measurable own time, at measurable random safe points, are
measurable (also at real points). -/
theorem measurable_relBdry_rand {z : Ω → ℂ} (hz : Measurable z)
    (hsafe : ∀ ω, z ω ∈ relSafe (Ito.rpath (V · ω)) (s ω)) :
    Measurable fun ω => relBdry (Ito.rpath (V · ω)) (s ω) (z ω) :=
  Restart.measurable_of_tendsto_nhdsWithin
    (fun ω => isOpen_relDomain (Chart.continuous_rpath_of_continuous (hVc ω)) (s ω).coe_nonneg)
    (measurableSet_mem_relDomain_rand hVm hVc hV0 hs)
    (measurable_indicator_relMap_rand hVm hVc hV0 hs) hz
    (fun ω => relSafe_subset_closure_relDomain _ _ (hsafe ω))
    (fun ω => tendsto_relMap_relBdry (Chart.continuous_rpath_of_continuous (hVc ω))
      (Chart.rpath_zero_of (hV0 ω)) (s ω).coe_nonneg (hsafe ω))

include hVm hVc hV0 hs in
/-- The boundary values restricted to a measurable safe event. -/
theorem measurable_indicator_relBdry_rand {E : Set Ω} (hE : MeasurableSet E)
    {z : Ω → ℂ} (hz : Measurable z) (hsafe : ∀ ω ∈ E, z ω ∈ relSafe (Ito.rpath (V · ω)) (s ω)) :
    Measurable (E.indicator fun ω => relBdry (Ito.rpath (V · ω)) (s ω) (z ω)) := by
  apply measurable_of_restrict_of_restrict_compl hE
  · have hm := measurable_relBdry_rand (V := fun t (ω : E) => V t ω.val) (s := fun ω : E => s ω.val)
      (fun t => (hVm t).comp measurable_subtype_coe) (fun ω => hVc ω.val)
      (fun ω => hV0 ω.val) (hs.comp measurable_subtype_coe) (hz.comp measurable_subtype_coe)
      (fun ω => hsafe ω.val ω.property)
    convert hm using 1
    funext ω
    exact indicator_of_mem ω.property _
  · have he : ((Eᶜ).domRestrict (E.indicator fun ω => relBdry (Ito.rpath (V · ω)) (s ω) (z ω))) =
        fun _ : ↥(Eᶜ) => (0 : ℂ) := by
      funext ω
      exact indicator_of_notMem ω.property _
    rw [he]
    exact measurable_const

end Random

end InteractingSLE.Theorem14.BW1Ver
