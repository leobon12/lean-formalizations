/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.SBS3MarkedStage
import InteractingSLE.Spec.Supplement.OrdGapFixed
import InteractingSLE.Spec.Supplement.SBLuDense
import InteractingSLE.Spec.Supplement.GW2ScheduleIdent
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Sec7.StripWallStage0

/-!
# The tip of a staged piece at a fixed time lies in `ℍ` (D38)

Packet PROVE-T14-SB2LIFT (round 32). **`ae_traceAt_mem_H_stage`**: for a staged history with regular drivers, at a
fixed time `t > 0`, almost surely at a launch of instruction `ℓ` with `t < ζ_ℓ`, the piece's trace at `t` (read by
`LP.traceAt`, measurable) lies in `ℍ`. Under the regular conditional law given the retained past before `ℓ` the piece
is a flow-line driver (`GW1W.ae_isFlowLineDriver_stage`, with the stage witness of
`S3.exists_stageWitness_interiorStageSides`); its chosen trace is a frozen flow line (Theorem 1.3,
`GW2aSingle.ae_chosenTrace`), whose tip at a fixed positive time is interior (`RLC.OrdLate.ae_mem_H_at`). The
transfer to `P` is `GW2Schedule.ae_of_ae_condExpKernel_on` on the launch event, a past event.

This is the clause `η sB ∈ ℍ` of `Om.IsStageS2` for B's stage piece (B's own stage coordinates).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sx

open Exist Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The tip of a launched staged piece at a fixed positive time is interior**, almost surely on `{t < ζ_ℓ}`. -/
theorem ae_traceAt_mem_H_stage (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (ℓ : ℕ) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (t : ℝ≥0∞) < (E ℓ ω).2 → LP.traceAt t (E ℓ ω).1 ∈ H := by
  obtain ⟨β, Y, hW, -⟩ := S3.exists_stageWitness_interiorStageSides hκ hb hh hE hR hreg ℓ
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  have hL := GW1W.measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg ℓ
  have hA : MeasurableSet {ω | (t : ℝ≥0∞) < (E ℓ ω).2 → LP.traceAt t (E ℓ ω).1 ∈ H} := by
    have e : {ω | (t : ℝ≥0∞) < (E ℓ ω).2 → LP.traceAt t (E ℓ ω).1 ∈ H} =
        {ω | (E ℓ ω).2 ≤ (t : ℝ≥0∞)} ∪ (fun ω => LP.traceAt t (E ℓ ω).1) ⁻¹' H := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_preimage, imp_iff_not_or, not_lt]
    rw [e]
    refine (measurableSet_le (measurable_snd.comp (hE.1 ℓ)) measurable_const).union ?_
    exact ((LP.measurable_traceAt t).comp (measurable_fst.comp (hE.1 ℓ))) QuantumZipper.isOpen_H.measurableSet
  refine GW2Schedule.ae_of_ae_condExpKernel_on h𝒢 hL hA ?_
  filter_upwards [GW1W.ae_isFlowLineDriver_stage hκ hb hh hE hreg hW] with ω₀ hfl hω₀
  obtain ⟨⟨h', hd⟩, -⟩ := hfl hω₀
  have htr := GW2aSingle.ae_chosenTrace h13 hκ hd
  have hfl0 := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hd (htr.mono fun ω hω => hω.1)
  filter_upwards [RLC.OrdLate.ae_mem_H_at hκ hκ4.le hfl0 t ht, htr] with ω hω htrω htζ
  rw [LP.traceAt_eq_of_isGeneratingTrace htrω.1 (hreg ℓ ω).1 (hreg ℓ ω).2.1 htζ]
  exact hω htζ

end InteractingSLE.Theorem14.SB.Sx
