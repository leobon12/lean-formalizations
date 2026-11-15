/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalChart
import InteractingSLE.Spec.Supplement.SB2LcdStageLoc

/-!
# S3: identify an actual stage mean with its selected conditional word

The chart observations, history-marked locality and clopen complement
conditions are now supplied for the actual staged run. The word is the
caller-supplied stage witness's word, so a witness with physical side labels
keeps those labels throughout the mean identification.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- Every harmonic representative of the actual explored-set mean has the
corrected mean of the same selected stage word in the actual run chart.
No chart-measurability, locality or clopen-geometry input is left open. -/
theorem ae_eqOn_stageMean_of_stageWitness
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hsort : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (β ω).IsSorted)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAeq : ∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E k ω)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
          g ω φ = ∫ z, v z * φ z) →
        EqOn (fun z => v z + u₀ z + chiC κ *
            (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2 z)
          (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z))
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := by
  have hmark₀ := (Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg hu₀ k).2.2
  have hmark := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hAeq.mono fun _ he => he.symm) hmark₀
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hAeq, WalkLaw.ae_isOpen_H_diff_stageSet hR k] with ω he ho
    rw [he]
    exact ⟨WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω, ho⟩
  have hlocal : IsLocalSet A (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hA hAc).out 4 1).2
      hmark.isAvoidanceLocal
  have hver := Lv.ae_verChart_eq_runChart hR hreg k
  have htr : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsChartTransport (WalkInf.verChart κ b jumps spec E k ω) 1 0 (chiC κ) (h ω) (Y ω) := by
    filter_upwards [hver, hW.2.2.1] with ω hv ht hl
    rw [hv]
    exact (ht hl).2.2
  have hAD : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ((WalkInf.verChart κ b jumps spec E k ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (WalkInf.verChart κ b jumps spec E k ω).dom) := by
    filter_upwards [hver, hAeq, ae_clopen_runChart_stageSet_at_launch hR k] with ω hv ha hd hl
    rw [hv, ha]
    exact hd hl
  have hm := ae_eqOn_mean_of_kernelWord (hE.2.1 k) (retainedChartData_verChart hb hE.1 hreg k)
    hh hu₀ hW.2.1 (Lv.measurableSet_launch_pastSigma hb hE.1 hreg k) hsort htr hW.2.2.2
    hA hlocal hmark hAD hg
  filter_upwards [hm, hver] with ω hmω hv hl v hharm hrep
  have he := hmω hl v hharm hrep
  rw [hv] at he
  exact he

end InteractingSLE.Theorem14.SB.S3
