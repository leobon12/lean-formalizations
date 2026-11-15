/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedPhysical

/-!
# S3: one physical conditional word for every finite prefix

All properties hold on the full sample space up to null sets. In
particular the prefix need not be followed by a launch, and may contain
arbitrarily many nonlaunch instructions.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- A word for the exact retained past with its actual field, chart and
physical side labels, including at nonlaunch and terminal prefixes. -/
structure RetainedWordWitness {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) : Prop where
  measurable_word : Measurable[pastSigma κ b jumps spec E k] β
  measurable_field : Measurable Y
  sorted : ∀ᵐ ω ∂P, (β ω).IsSorted
  transport : ∀ᵐ ω ∂P, IsChartTransport
    (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (chiC κ) (h ω) (Y ω)
  law : ∀ᵐ ω ∂P, IsGFFWithBoundaryData
    (condExpKernel P (pastSigma κ b jumps spec E k) ω) Y (β ω).fn (β ω).jumps
  sides : ∀ᵐ ω ∂P, HasInteriorStageSides κ b jumps spec (fun j => E j ω) k (β ω)

/-- Restriction to a launch gives the existing stage-witness interface. -/
theorem RetainedWordWitness.isStageWitness {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : RetainedWordWitness κ b jumps P h spec E k β Y)
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    IsStageWitness κ b jumps P h spec E k β Y := by
  refine ⟨hW.measurable_word, hW.measurable_field, ?_, hW.law.mono fun _ hl _ => hl⟩
  filter_upwards [hW.transport, GW1W.regLaunches_of_stagedPiecesRegular hR] with ω ht hr _
  have hc := GW2aCont.isConformal_runChart spec (fun j => E j ω) k (fun j _ c θ hl => hr j c θ hl)
  exact ⟨hc.1, hc.2, ht⟩

/-- A finite instruction advances a full retained-word witness. -/
theorem RetainedWordWitness.next {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {k : ℕ} (htime : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      min (instrTime spec k) (E k ω).2 ≠ ⊤)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : RetainedWordWitness κ b jumps P h spec E k β Y) :
    RetainedWordWitness κ b jumps P h spec E (k + 1)
      (nextRetainedWord κ b jumps spec E k β) (nextRetainedField κ b jumps spec E k Y) := by
  have hStage := hW.isStageWitness hR
  have hPhysical := ae_nextRetained_transport_sides hκ hb hh hE hR hreg htime hStage hW.transport hW.sides
  exact ⟨measurable_nextRetainedWord hb hE.1 hreg hW.measurable_word,
    measurable_nextRetainedField hb hE.1 hreg (hE.2.1 (k + 1)) hW.measurable_field,
    hW.sorted.mono fun _ hs => isSorted_nextRetainedWord hs,
    hPhysical.mono fun _ hp => hp.1,
    ae_kernelWord_nextRetained hκ hb hh hE hreg htime hStage hW.sorted hW.law,
    hPhysical.mono fun _ hp => hp.2⟩

/-- Every finite allotted-time prefix has one conditional word carrying
its physical labels and actual chart transport, regardless of launches. -/
theorem exists_retainedWordWitness {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (k : ℕ) (htime : HasFiniteOrdinaryTimes spec k) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      RetainedWordWitness κ b jumps P h spec E k β Y := by
  induction k with
  | zero =>
    obtain ⟨c₀, hc₀, hc₀J, hcb⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
    have hc : c₀.IsSorted := fun i j hij hj => hc₀.monotoneOn (lt_of_le_of_lt hij hj) hj hij
    have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
      rw [hc₀J]
      exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hcb y hy).2 hh
    refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω),
      ⟨measurable_const, (measurable_flowField _ _).comp hh.1,
        Eventually.of_forall fun _ => BoundaryWord.isSorted_shiftW hc _,
        Eventually.of_forall fun _ => isChartTransport_shiftChart _ _ _, ?_, ?_⟩⟩
    · rw [pastSigma_zero]
      exact ae_isGFFWithBoundaryData_condExpKernel_bot (isGFFWithBoundaryData_shiftW spec.1 hh₀)
    · exact Eventually.of_forall fun ω y _ hyH => by
        change LuM.bdVal (Chart.id.recenter spec.1) (y : ℂ) ∈ H at hyH
        rw [bdVal_init_real] at hyH
        simp [QuantumZipper.H] at hyH
  | succ k ih =>
    obtain ⟨β, Y, hW⟩ := ih (fun j hj => htime j (Nat.lt_succ_of_lt hj))
    refine ⟨_, _, hW.next hκ hb hh hE hR hreg ?_⟩
    intro ω hl
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    exact ne_top_of_le_ne_top
      (htime k (Nat.lt_succ_self k) θ _ (eq_launch_of_launches spec (fun j => E j ω) hcθ).1)
      (min_le_left _ _)

end InteractingSLE.Theorem14.SB.S3
