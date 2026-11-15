/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2ReadoutBoundary

/-!
# Measurable physical paths for finite launched pieces

Packet PROVE-T14-SBTAIL2. Measurable interior inverse-chart evaluations from
`WalkStageLocalMeas` approximate the boundary readout of `LP.drivingTrace`.
Their limits give measurable coordinates and, on the regularity event, a
continuous parametrization of the entire finite physical piece.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Readout

open Exist.Staged Exist.StagedLaw GW2aMulti

/-- On a measurable event of regular pieces, a finite launched piece has one
physical parametrization with every coordinate measurable. The statement does
not require a field law or a measurable selection of charts' boundary values. -/
theorem exists_measurable_piece_param {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {Ω : Type u} [MeasurableSpace Ω] {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2))
    (k : ℕ) (hfin : instrTime spec k ≠ ⊤) :
    ∃ a : Ω → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => a ω t) ∧
      ∀ ω ∈ M,
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        Continuous (a ω) ∧ range (a ω) =
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.tipSet
            (stoppedDriver spec (fun j => E j ω) k) (pieceStop spec (fun j => E j ω) k) := by
  let T : Ω → ℝ≥0∞ := fun ω => min (instrTime spec k) (E k ω).2
  let tr : Ω → ℝ≥0 → ℂ := fun ω => (LP.drivingTrace (T ω, (E k ω).1)).2
  have hT : Measurable T := measurable_const.min (measurable_snd.comp (hEm k))
  have htr : ∀ t, Measurable fun ω => tr ω t := fun t =>
    (measurable_pi_apply t).comp (measurable_snd.comp (LP.measurable_drivingTrace.comp
      (hT.prodMk (measurable_fst.comp (hEm k)))))
  have hY : ∀ (t : ℝ≥0) (n : ℕ), ∃ Y : Ω → ℂ, Measurable Y ∧ ∀ ω ∈ M,
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1
        (raiseH n (tr ω t)) = Y ω := by
    intro t n
    exact WalkLaw.exists_measurable_runChart_inv hb spec hEm hreg hM hMreg k
      ((continuous_raiseH n).measurable.comp (htr t)) (fun ω => raiseH_mem n (tr ω t))
  choose Y hYm hYeq using hY
  let a : Ω → ℝ≥0 → ℂ := fun ω t => limUnder atTop (fun n => Y t n ω)
  refine ⟨a, fun t =>
    (StronglyMeasurable.limUnder fun n => (hYm t n).stronglyMeasurable).measurable, ?_⟩
  intro ω hω hlaunch
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlaunch
  have hr := hMreg ω hω k c θ hcθ
  obtain ⟨f, _, hf, _⟩ := (GW1P.isClosed_pieces_run spec (fun j => E j ω) (hMreg ω hω) k).1
  have ht : T ω ≠ ⊤ := ne_top_of_le_ne_top hfin (min_le_left _ _)
  have htraceH : ∀ t, tr ω t ∈ Hbar := by
    obtain ⟨hW0, hWc, α, hα, _⟩ := hr
    have he := LP.drivingTrace_eq hα
      (hWc.mono fun s hs => show (s : ℝ≥0∞) ≤ T ω from hs.le) hW0 (fun _ _ => rfl)
    intro t
    change (LP.drivingTrace (T ω, (E k ω).1)).2 t ∈ Hbar
    rw [he]
    apply Sec7.IsGeneratingTrace.mem_Hbar hα
      (hWc.mono fun s hs => show (s : ℝ≥0∞) ≤ T ω from hs.le) hW0
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  have ha : ∀ t, a ω t = f (tr ω t) := by
    intro t
    have he : (fun n => Y t n ω) = fun n =>
        (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1
          (raiseH n (tr ω t)) := funext fun n => (hYeq t n ω hω).symm
    change limUnder atTop (fun n => Y t n ω) = f (tr ω t)
    rw [he]
    exact ((hf _ (htraceH t)).comp (tendsto_raiseH (htraceH t))).limUnder_eq
  exact continuous_range_of_stopped_readout hf hr ht ha

end InteractingSLE.Theorem14.SB.Readout
