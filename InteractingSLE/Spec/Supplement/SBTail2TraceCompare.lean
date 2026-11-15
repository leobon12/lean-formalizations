/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2TraceFrame

/-!
# Comparing the conditional chosen trace in the actual retained sewing frame

The physical new-piece image condition is discharged by the readout theorem.
The remaining inputs are the regular relative lower history, its exhaustive
surviving word, the calibrated lower-tail frame, and SB3's stage induction.
These are named mathematical inputs; this is not a provider for SB3 or SB4.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Leaf FlowDilate

/-- SB3 applied to the same conditional launch driver, followed by sewing in
the calibrated retained frame. The physical piece may be clipped at its own
time while the comparison uses the driver's complete available lifetime. -/
theorem ae_actualTailSewing_of_frame_word
    (hSB3 : SB3InductionGenStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {bc : ℝ → ℝ} {jc : Finset ℝ} (hbc : IsPiecewiseConstantBoundaryData bc jc)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hl : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ : ℝ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ bc jc θ Q hl W ζ)
    {m : ℝ} (hm : m ≤ 0) {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEL : IsBoundaryContinuedProgram
        (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true).2.2 →
      IsStagedHistory κ (affData 1 m bc) (affJumps 1 m jc) Q
          (fun ω => affField m one_pos (hl ω))
          (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) EL ∧
        StagedPiecesRegular κ (affData 1 m bc) (affJumps 1 m jc) Q
          (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) EL)
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ}
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < Sec4.cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < Sec4.cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hθ : ∃ q ∈ l, θ = q.1)
    (hclass : ∀ y ∈ Ioo m 0, y ∉ affJumps 1 m jc →
      (∃ p ∈ l, affData 1 m bc y = sleLambda κ - p.1 * chiC κ ∨
          affData 1 m bc y = -sleLambda κ - p.1 * chiC κ) ∨
        affData 1 m bc y ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
          affData 1 m bc y ∈ original)
    (hpos : ∀ᵐ ω ∂Q, 0 < ζ ω)
    {f : ℂ → ℂ} {A S : Ω → Set ℂ} {T : ℝ≥0∞}
    (hread : ∀ᵐ ω ∂Q, A ω ⊆ f '' (GW2aSingle.chosenTrace W ζ ω ''
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min T (ζ ω)}))
    (hframe : ∀ᵐ ω ∂Q, RetainedTailFrame f (S ω)
      (relWalkSet κ (affData 1 m bc) (affJumps 1 m jc) EL ω) m) :
    ∀ᵐ ω ∂Q, HasActualTailSewing (A ω) (S ω) := by
  obtain ⟨hbcM, hGM, hflow⟩ := relFlowLine_of_isFlowLineDriver h13 hκ hbc hfl m
  have hword : IsRelSB3WordInstance κ Q (fun ω => affField m one_pos (hl ω))
      (affData 1 m bc) (affJumps 1 m jc) EL m θ
      (fun ω t => aff 1 m (GW2aSingle.chosenTrace W ζ ω t)) ζ l original :=
    ⟨hbcM, hGM, hEL, hm, hθ, hclass, hflow, hpos⟩
  have hS1 := ae_isOneSided_of_relSB3Instance hSB3 h12 h13 hκ hκ4
    (isRelSB3Instance_of_word hκ hκ4 hangles hgaps hbridge hword)
  have hgeo := ae_relTailGeometry_of_frame_readout h13 hκ hfl hread hframe
  filter_upwards [hS1, hgeo] with ω hSω hgω
  exact hgω.hasActualTailSewing hSω

end InteractingSLE.Theorem14.SB.Retain
