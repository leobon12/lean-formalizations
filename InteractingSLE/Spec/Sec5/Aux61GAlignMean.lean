/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignZero
import InteractingSLE.Spec.Sec5.Aux61GRecGlued

/-! # Actual counterflow extension and centered physical pairings -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting LawUnique GlueCond Cond44Ref WangWu
open Sec7.StripSysField
universe u

/-- The counterflow boundary data of the actual source relative angle. -/
def sourceCounterBoundary (S : SourceSetting.{u}) : ℝ → ℝ :=
  fun x => forceBoundaryData S.κ S.ρL S.ρR S.xL S.xR x + -(S.θ * chiC S.κ)

/-- The explicit bounded harmonic extension of the actual dual force word. -/
def sourceCounterExtension (S : SourceSetting.{u}) : ℂ → ℝ :=
  let b := sourceCounterBoundary S
  let J := counterflowJumps (forceJumpFinset S.xL S.xR)
  Impl.forceExt (16 / S.κ)
    (Ito.weightWord
      (flowLineRhoL (16 / S.κ) (counterflowData S.κ b) J 0 0)
      (flowLineRhoR (16 / S.κ) (counterflowData S.κ b) J 0 0))
    (flowLineXL (counterflowData S.κ b) J 0)
    (flowLineXR (counterflowData S.κ b) J 0)

/-- No unspecified harmonic extension is needed for the source dual word. -/
theorem sourceCounterExtension_spec (S : SourceSetting.{u}) :
    IsBoundedHarmonicExtension
      (cfWordData S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR))
      (cfWordJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR))
      (sourceCounterExtension S) := by
  dsimp only [sourceCounterExtension, cfWordData, cfWordJumps]
  rw [coe_forceJumpFinset]
  exact Impl.isBoundedHarmonicExtension_forceExt _ _ _ _

/-- Remove the restored harmonic base from physical mean pairings. Both
integrals are integrable by harmonicity and compact test support. -/
theorem sub_base_pairings {O : Set ℂ} {g : DistOn upperHalfPlaneOpens}
    {m u₀ : ℂ → ℝ} (hm : InnerProductSpace.HarmonicOnNhd m O)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hpair : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      (g + smoothDist upperHalfPlaneOpens u₀) φ = ∫ z, m z * φ z)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) :
    g φ = ∫ z, (m z - u₀ z) * φ z := by
  have hi := WholeField.integrable_mul_testOn hm.continuousOn φ hφ
  have hi₀ := WholeField.integrable_mul_testOn hu₀.continuousOn φ φ.tsupport_subset
  have hp := hpair φ hφ
  rw [add_apply, smoothDist_apply hu₀.continuousOn] at hp
  have he : (∫ z, φ z * u₀ z) = ∫ z, u₀ z * φ z :=
    integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have hs : (∫ z, (m z - u₀ z) * φ z) =
      (∫ z, m z * φ z) - (∫ z, u₀ z * φ z) := by
    simp only [sub_mul]
    exact integral_sub hi hi₀
  rw [he] at hp
  rw [hs]
  exact eq_sub_of_add_eq hp

end InteractingSLE.Sec5.Aux61GAlign
