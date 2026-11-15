/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KcStage
import InteractingSLE.Spec.Restart.FCDetTransfer

/-!
# The measurable force-type partition for K2 at a launch

Use the existing `WordType` at an arbitrary angle, adjusting only the two seed
weights. A countable profile cover supplies a countable type cover even after a
random recentering. The cells are measurable in the retained past and disjoint;
their union covers the launch event almost surely. The positions on a cell are
the existing `FCDet.typeXL` and `FCDet.typeXR`, including their global order API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist.Staged Exist.StagedLaw Supp8.Q3Stop

/-- Changing the angle changes only the two seed weights of a force type. -/
def angleType (κ θ : ℝ) (w : WordType) : WordType :=
  (w.1, w.2.1,
    (fun i => w.2.2.1 i - if i = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0),
    fun j => w.2.2.2 j + if j = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0)

/-- The padded force type of a word at angle `θ`. -/
def angleWordType (κ θ : ℝ) (c : BoundaryWord) : WordType :=
  (flowLineNL c.fn c.jumps 0, flowLineNR c.fn c.jumps 0,
    (padFL κ θ c.fn c.jumps).2.1, (padFL κ θ c.fn c.jumps).2.2)

theorem angleWordType_eq (κ θ : ℝ) (c : BoundaryWord) :
    angleWordType κ θ c = angleType κ θ (wordType κ c) := by
  have he := padFL_weights κ θ c.fn c.jumps
  change (_, _, (padFL κ θ c.fn c.jumps).2.1, (padFL κ θ c.fn c.jumps).2.2) = _
  rw [congrArg Prod.fst he, congrArg Prod.snd he]
  rfl

theorem measurable_angleWordType (κ θ : ℝ) : Measurable (angleWordType κ θ) :=
  wordMeasStatement.1.prodMk (wordMeasStatement.2.1.prodMk
    (((measurable_fst.comp measurable_snd).comp (wordMeasStatement.2.2 κ θ)).prodMk
      ((measurable_snd.comp measurable_snd).comp (wordMeasStatement.2.2 κ θ))))

/-- Recentered words with profiles in `S` have types in this countable image. -/
theorem angleWordType_shift_mem (κ θ a : ℝ) {S : Set WordProfile}
    {c : BoundaryWord} (hc : wordProfile c ∈ S) :
    angleWordType κ θ (BoundaryWord.shiftW a c) ∈ angleType κ θ '' profileTypes κ S := by
  rw [angleWordType_eq]
  exact ⟨_, wordType_mem_profileTypes κ (c := BoundaryWord.shiftW a c) hc, rfl⟩

/-- A stage witness with a countable cover of the force types after any
past-measurable recentering, at any fixed angle. -/
theorem exists_stageWitness_countable_types {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) (θ : ℝ) {m : Ω → ℝ}
    (hm : Measurable[pastSigma κ b jumps spec E k] m) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens)
      (T : Set WordType),
      IsStageWitness κ b jumps P h spec E k β Y ∧ T.Countable ∧
        Measurable[pastSigma κ b jumps spec E k]
          (fun ω => BoundaryWord.shiftW (m ω) (β ω)) ∧
        ∀ᵐ ω ∂P,
          (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
            angleWordType κ θ (BoundaryWord.shiftW (m ω) (β ω)) ∈ T := by
  obtain ⟨β, Y, S, hW, hS, hp⟩ :=
    exists_stageWitness_countable_profiles hκ hb hh hE hreg k
  refine ⟨β, Y, angleType κ θ '' profileTypes κ S, hW,
    (countable_profileTypes κ hS).image _,
    BoundaryWord.measurable_shiftW.comp (hm.prodMk hW.1), ?_⟩
  exact hp.mono fun ω hω hl => angleWordType_shift_mem κ θ (m ω) (hω hl)

section Cells

variable {Ω : Type*} [MeasurableSpace Ω] {κ θ : ℝ}
  {cw : Ω → BoundaryWord} {F : Set Ω}

/-- The launch event restricted to one padded force type. -/
def wordTypeCell (κ θ : ℝ) (cw : Ω → BoundaryWord) (F : Set Ω)
    (w : WordType) : Set Ω := F ∩ {ω | angleWordType κ θ (cw ω) = w}

theorem measurableSet_wordTypeCell (hcw : Measurable cw) (hF : MeasurableSet F)
    (w : WordType) : MeasurableSet (wordTypeCell κ θ cw F w) :=
  hF.inter (((measurable_angleWordType κ θ).comp hcw) (measurableSet_singleton w))

omit [MeasurableSpace Ω] in
theorem disjoint_wordTypeCell {w v : WordType} (hwv : w ≠ v) :
    Disjoint (wordTypeCell κ θ cw F w) (wordTypeCell κ θ cw F v) := by
  exact disjoint_left.2 fun _ h1 h2 => hwv (h1.2.symm.trans h2.2)

omit [MeasurableSpace Ω] in
/-- Membership in a cell supplies the fixed force type used by K2. -/
theorem mem_typeSet_of_mem_wordTypeCell {w : WordType} {ω : Ω}
    (hω : ω ∈ wordTypeCell κ θ cw F w) :
    cw ω ∈ FCDet.typeSet κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w) := by
  have he := hω.2
  refine ⟨congrArg Prod.fst he, congrArg (fun p : WordType => p.2.1) he, ?_, ?_⟩
  · intro i
    exact congrFun (congrArg (fun p : WordType => p.2.2.1) he) i
  · intro j
    exact congrFun (congrArg (fun p : WordType => p.2.2.2) he) j

omit [MeasurableSpace Ω] in
/-- The exact word equality in K2's `hword` on one cell, using the existing
typed positions and fixed weights. -/
theorem k2_word_of_mem_wordTypeCell {w : WordType} {ω : Ω}
    (hω : ω ∈ wordTypeCell κ θ cw F w) :
    flowLineNL (cw ω).fn (cw ω).jumps 0 = w.1 ∧
    flowLineNR (cw ω).fn (cw ω).jumps 0 = w.2.1 ∧
    truncWord w.1 w.2.1 (padFL κ θ (cw ω).fn (cw ω).jumps) =
      ((FCDet.typeXL κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w) (cw ω),
        FCDet.typeXR κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w) (cw ω)),
        (typedRhoL w, typedRhoR w)) := by
  have hc := mem_typeSet_of_mem_wordTypeCell hω
  refine ⟨congrArg Prod.fst hω.2, congrArg (fun p : WordType => p.2.1) hω.2, ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · unfold FCDet.typeXL
      rw [ite_eq_left hc]
      rfl
    · unfold FCDet.typeXR
      rw [ite_eq_left hc]
      rfl
  · apply Prod.ext
    · exact funext fun i => congrFun (congrArg (fun p : WordType => p.2.2.1) hω.2) i
    · exact funext fun j => congrFun (congrArg (fun p : WordType => p.2.2.2) hω.2) j

/-- A countable force-type cover gives a countable measurable partition up to
null sets; no restriction is imposed on a null modification of the word. -/
theorem ae_mem_iUnion_wordTypeCell {P : Measure Ω} {T : Set WordType}
    (hT : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ θ (cw ω) ∈ T) :
    ∀ᵐ ω ∂P, ω ∈ F → ω ∈ ⋃ w : T, wordTypeCell κ θ cw F w := by
  filter_upwards [hT] with ω hω hF
  exact mem_iUnion.2 ⟨⟨angleWordType κ θ (cw ω), hω hF⟩, hF, rfl⟩

end Cells

end InteractingSLE.Theorem14.SB.Lv
