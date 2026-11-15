/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignMean

/-! # Smaller reference means from the actual source couplings

Instantiate both physical references on the same source measure and with
the same centered field used by MARKS. Counterflow regularity and both
bounded harmonic extensions are derived, rather than supplied as inputs.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting LawUnique GlueCond Cond44Ref WangWu
open CrossCond.Theta LocalSets WholeField
universe u

/-- Actual own and counterflow local means for every rational comparison
time, with harmonicity and precisely the centered pairings of
`ZeroComparisons`. No smaller-set Gaussian mean or pairing is assumed. -/
theorem exists_source_physical_references
    (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i₀ : F.ι) (j : ℚ) :
    ∃ gA gG : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean
        (fun p => hullAt (rationalTime j) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
        (S.marksData F).cfield S.μ gA ∧
      IsLocalSetMean (fun p => cfHullQ (rationalTime S.s) p.2) (S.marksData F).cfield S.μ gG ∧
      (∀ᵐ p ∂S.μ,
        InnerProductSpace.HarmonicOnNhd
          ((S.marksData F).mean j i₀ 0 p)
          (H \ hullAt (rationalTime j) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ hullAt (rationalTime j) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) →
          gA p φ = ∫ z, ((S.marksData F).mean j i₀ 0 p z - (S.marksData F).originalMean z) * φ z) ∧
      (∀ᵐ p ∂S.μ,
        InnerProductSpace.HarmonicOnNhd
          (fun z => cfMeanQ S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
            (sourceCounterExtension S) (rationalTime S.s) p.2 z + (S.marksData F).originalMean z)
          (H \ cfHullQ (rationalTime S.s) p.2) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ (rationalTime S.s) p.2 →
          gG p φ = ∫ z,
            ((cfMeanQ S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
              (sourceCounterExtension S) (rationalTime S.s) p.2 z + (S.marksData F).originalMean z) -
                (S.marksData F).originalMean z) * φ z) := by
  have hu₀ := Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR
  have hreg := ae_cfRegT S.κ_pos S.theta_bounds S.own.coupling S.counterflow S.theta_field_law
  have hr := Aux61GRec.exists_physical_references_gluedT S.own.coupling S.κ_pos S.own_infinite
    S.counterflow hreg S.theta_field_law S.kernel_law hu₀ (rationalTime j) (rationalTime S.s)
    (sourceCounterExtension_spec S)
    (fun ω => Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR)
      (fun i => S.own.VL i (rationalTime j) ω - S.own.W (rationalTime j) ω)
      (fun i => S.own.VR i (rationalTime j) ω - S.own.W (rationalTime j) ω))
  dsimp only at hr
  have he : (fun p : S.Ω × HistorySpace 0 0 =>
      cenTT S.κ S.θ (Impl.forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
        (cfFieldT S.κ S.θ (S.ownField p.1))) =
      (S.marksData F).cfield :=
    funext fun p => cenTT_cfFieldT S.κ S.θ (S.marksData F).originalMean (S.ownField p.1)
  rw [← S.theta_measure, he] at hr
  obtain ⟨gA, gG, hgA, hgG, hA, hG⟩ := hr
  refine ⟨gA, gG, hgA, hgG, ?_, ?_⟩
  · filter_upwards [hA] with p hp
    exact ⟨hp.1, sub_base_pairings hp.1 hu₀.1 hp.2⟩
  · filter_upwards [hG] with p hp
    exact ⟨hp.1, sub_base_pairings hp.1 hu₀.1 hp.2⟩

end InteractingSLE.Sec5.Aux61GAlign
