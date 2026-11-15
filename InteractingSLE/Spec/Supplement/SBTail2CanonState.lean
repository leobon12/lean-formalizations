/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2Word
import InteractingSLE.Spec.Supplement.GW1Base

/-!
# Staged histories are independent of a boundary datum's representative

Packet PROVE-T14-SBTAIL2, continuation. Boundary continuations read genuine jumps and
one-sided limits. Consequently equivalent piecewise-constant data give the same runs,
retained sigma-algebras, conditional launch laws and physical lower walks. These adapters
allow the actual-tail construction to use one explicit word for the conditional GFF.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Leaf.Canon

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {κ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ}

/-- Two descriptions of the same GFF have identical one-sided data and genuine jumps. -/
theorem data_eq_of_same_gff {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hh : IsGFFWithBoundaryData Q h b J) (hh' : IsGFFWithBoundaryData Q h b' J') :
    jumpSet b J = jumpSet b' J' ∧ leftLim b = leftLim b' ∧ rightLim b = rightLim b' := by
  have he := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb hb' hh hh'
  have hL : leftLim b = leftLim b' := Restart.leftLim_congr he
  have hR : rightLim b = rightLim b' := Restart.rightLim_congr he
  exact ⟨GW1.jumpSet_eq_of_lims hb hb' hL hR, hL, hR⟩

variable (hS : jumpSet b J = jumpSet b' J') (hL : leftLim b = leftLim b')
  (hR : rightLim b = rightLim b')

include hL hR

theorem heights_eq (s : ExplState) : ExplState.heights κ b s = ExplState.heights κ b' s := by
  simp only [ExplState.heights, hL, hR]

theorem flowStep_eq (gw2 : Bool) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b gw2 s k D θ t = ExplState.flowStep κ b' gw2 s k D θ t := by
  unfold ExplState.flowStep
  split
  rw [heights_eq hL hR]

include hS

theorem contStep_eq (s : ExplState) (v : Option ℝ) (pref : Bool) :
    ExplState.contStep κ b J s v pref = ExplState.contStep κ b' J' s v pref := by
  simp only [ExplState.contStep, hL, hR, hS]

theorem step_eq (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (s : ExplState) (ik : Instr × ℕ) :
    ExplState.step κ b J gw2 D s ik = ExplState.step κ b' J' gw2 D s ik := by
  rcases ik with ⟨i, k⟩
  rcases i with ⟨θ, t⟩ | (pref | ⟨v, pref⟩)
  · exact flowStep_eq hL hR gw2 s k (D k) θ t
  · exact contStep_eq hS hL hR s none pref
  · exact contStep_eq hS hL hR s (some v) pref

theorem run_eq (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    ExplState.run κ b J spec D k = ExplState.run κ b' J' spec D k := by
  have he : ExplState.step κ b J spec.2.1 D = ExplState.step κ b' J' spec.2.1 D :=
    funext fun s => funext fun ik => step_eq hS hL hR spec.2.1 D s ik
  unfold ExplState.run
  rw [he]

theorem pastSigma_eq {Ω : Type*} (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    pastSigma κ b J spec E k = pastSigma κ b' J' spec E k := by
  simp only [pastSigma, run_eq hS hL hR]

theorem isStagedHistory_iff {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Q : Measure Ω} [IsFiniteMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    IsStagedHistory κ b J Q h spec E ↔ IsStagedHistory κ b' J' Q h spec E := by
  unfold IsStagedHistory
  have hK (k : ℕ) (ω₀ : Ω) : condExpKernel Q (pastSigma κ b J spec E k) ω₀ =
      condExpKernel Q (pastSigma κ b' J' spec E k) ω₀ := by
    rw [pastSigma_eq hS hL hR]
  simp_rw [pastSigma_eq hS hL hR, run_eq hS hL hR, hK]

theorem stagedPiecesRegular_iff {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    StagedPiecesRegular κ b J Q spec E ↔ StagedPiecesRegular κ b' J' Q spec E := by
  simp only [StagedPiecesRegular, run_eq hS hL hR]

omit hL hR in
theorem boundaryWalkSpec_eq (θ : ℝ) (right : Bool) :
    boundaryWalkSpec b J θ right = boundaryWalkSpec b' J' θ right := by
  unfold boundaryWalkSpec
  rw [hS]

theorem physSet_eq (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b J spec D = ExplState.physSet κ b' J' spec D := by
  simp only [ExplState.physSet, run_eq hS hL hR]

theorem relWalkSet_eq {Ω : Type*} (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    relWalkSet κ b J EL ω = relWalkSet κ b' J' EL ω := by
  unfold relWalkSet
  rw [boundaryWalkSpec_eq hS, physSet_eq hS hL hR]

end InteractingSLE.Theorem14.SB.Leaf.Canon
