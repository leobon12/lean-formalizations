/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInResidualSet
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# The represented old-chart increment is the physical mean difference

PROVE-POCKET-SIDEIN. Subtract the two physical mean distributions on the
current domain, then use the existing transported-test support theorem and
change of variables. Harmonicity follows from holomorphic composition.
No separate increment-representation hypothesis is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- Pulling back the difference of the represented physical means gives
their actual harmonic difference in the old coordinate. -/
theorem pull_mean_difference_representation {old current : Chart}
    (hOld : old.IsConformal) (hInclusion : (current.dom : Set ℂ) ⊆ old.dom)
    {gOld gNow : DistOn upperHalfPlaneOpens} {vOld vNow : ℂ → ℝ}
    (hvOld : InnerProductSpace.HarmonicOnNhd vOld old.dom)
    (hRepOld : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ old.dom →
      gOld φ = ∫ z, vOld z * φ z)
    (hvNow : InnerProductSpace.HarmonicOnNhd vNow current.dom)
    (hRepNow : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ current.dom →
      gNow φ = ∫ z, vNow z * φ z) :
    InnerProductSpace.HarmonicOnNhd
        (fun z => vNow (old.2.1 z) - vOld (old.2.1 z))
        (Restart.MarkovChart.chartPre old current.dom) ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ Restart.MarkovChart.chartPre old current.dom →
        Chart.pullField hOld (gNow - gOld) φ =
          ∫ z, (vNow (old.2.1 z) - vOld (old.2.1 z)) * φ z := by
  have hvOld' : InnerProductSpace.HarmonicOnNhd vOld current.dom :=
    fun z hz => hvOld z (hInclusion hz)
  have hDifference (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ current.dom) :
      (gNow - gOld) φ = ∫ z, (vNow z - vOld z) * φ z := by
    rw [sub_apply, hRepNow φ hφ, hRepOld φ (hφ.trans hInclusion)]
    have hiNow := integrable_mul_test current.dom.isOpen
      (fun z hz => (hvNow z hz).1.continuousAt.continuousWithinAt) φ hφ
    have hiOld := integrable_mul_test current.dom.isOpen
      (fun z hz => (hvOld' z hz).1.continuousAt.continuousWithinAt) φ hφ
    rw [← integral_sub hiNow hiOld]
    congr 1
    funext z
    ring
  refine ⟨fun z hz => ?_, fun φ hφ => ?_⟩
  · have hAnalytic := hOld.1.analyticAt (QuantumZipper.isOpen_H.mem_nhds hz.1)
    exact (QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp hAnalytic (hvNow _ hz.2)).sub
      (QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp hAnalytic (hvOld _ (hInclusion hz.2)))
  · rw [Chart.pullField_apply,
      hDifference _ (Restart.MarkovChart.tsupport_pushTest_subset_of_chartPre hOld hφ),
      Chart.integral_mul_pushTest]

end InteractingSLE.Sec7.PocketStopSide
