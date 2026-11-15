/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SwitchComparison
import InteractingSLE.Spec.Exist.StagedLaw2Run
import InteractingSLE.Spec.Supplement.StagedRegularize

/-!
# R51 regularity at an SB4 switch

Launch events are null-measurable for the original family, by its measurable
regularization. Every actually launched finite schedule piece is the range of a
continuous frozen path, using the good launch chart and the regular generating
trace. No simplicity of an arbitrary angle schedule is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB

open Exist.StagedLaw GW1P GW2Schedule CounterflowRange

/-- Exact measurability of the raw launch event is unnecessary under R51:
regularization gives its null-measurability with no extra premise. -/
theorem nullMeasurableSet_launch_of_stagedPiecesRegular
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    NullMeasurableSet {ω | (ExplState.run κ b jumps spec
      (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} P := by
  have hm := (Exist.StagedLaw.runMeasStatement κ b jumps hb spec
    (StagedReg.regHist spec E) (StagedReg.measurable_regHist hEm)
    (StagedReg.isRegularDriver_regHist) k).1
  refine hm.nullMeasurableSet.congr ?_
  filter_upwards [StagedReg.ae_run_regHist hR] with ω hω
  rw [hω (k + 1)]

/-- Good inverse-chart boundary limits transport a finite regular generating
trace to a continuous physical path frozen at its available endpoint. -/
theorem finite_piece_exists_continuous_param {c : Chart} {W : ℝ≥0 → ℝ}
    {T : ℝ≥0∞} (hc : HasProperBdryExt c) (hW : PieceRegular W T) (hT : T ≠ ⊤) :
    ∃ a : ℝ≥0 → ℂ, Continuous a ∧
      range a = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) T).toNNReal) T := by
  obtain ⟨f, _, hf, _⟩ := hc
  obtain ⟨hW0, hWc, α, hα, _⟩ := hW
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα
      (hWc.mono fun s (hs : (s : ℝ≥0∞) < T) =>
        show (s : ℝ≥0∞) ≤ T from hs.le) hW0 ht
  have hfc := continuousOn_of_tendsto hf
  have hmem : ∀ t : ℝ≥0, ((min t T.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T := fun t =>
    (ENNReal.coe_le_coe.2 (min_le_right t T.toNNReal)).trans
      (le_of_eq (ENNReal.coe_toNNReal hT))
  have hαc : Continuous fun t : ℝ≥0 => α (min t T.toNNReal) :=
    hα.2.1.comp_continuous (continuous_id.min continuous_const) hmem
  refine ⟨fun t => f (α (min t T.toNNReal)),
    hfc.comp_continuous hαc (fun t => hαH _ (hmem t)), ?_⟩
  rw [tipSet_stopped_eq_of_tendsto hα hWc hW0 (fun t ht => hf _ (hαH t ht))]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨α _, ⟨_, hmem t, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have ht' : t ≤ T.toNNReal := by
      apply ENNReal.coe_le_coe.1
      rw [ENNReal.coe_toNNReal hT]
      exact ht
    exact ⟨t, congrArg (fun s => f (α s)) (min_eq_left ht')⟩

/-- For an R51 schedule at any real root, every actual launched piece has the
continuous physical parametrization needed for the countable avoidance event. -/
theorem ae_schedulePiece_exists_continuous_param
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E) :
    ∀ᵐ ω ∂P, ∀ k < (scheduleProgram 0 l).length,
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∃ a : ℝ≥0 → ℂ, Continuous a ∧
        range a = schedulePiece κ b jumps x l (fun j => E j ω) k := by
  filter_upwards [hR.ae_pieceRegular] with ω hω k hk hlaunch
  obtain ⟨cθ, hcθ⟩ := Option.ne_none_iff_exists'.1 hlaunch
  have hc := (isClosed_pieces_run ⟨x, true, scheduleProgram 0 l⟩
    (fun j => E j ω) hω k).1
  have hr := hω k cθ.1 cθ.2 hcθ
  have ht : instrTime (x, true, scheduleProgram 0 l) k = schedDelta 0 l k := by
    unfold instrTime
    rw [isFlowProg_scheduleProgram 0 l k hk]
  rw [ht] at hr
  have hfin : min (schedDelta 0 l k) (E k ω).2 ≠ ⊤ :=
    ne_top_of_le_ne_top (schedDelta_ne_top 0 l k) (min_le_left _ _)
  obtain ⟨a, hac, har⟩ := finite_piece_exists_continuous_param hc hr hfin
  exact ⟨a, hac, har⟩

end InteractingSLE.Theorem14.SB
