/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2PointSchedule

/-!
# The actual conditional trace read through its retained launch chart

R51 supplies one continuous boundary extension of the launch chart before the
new piece is sampled. Under the actual retained conditional measure, the
stopped physical piece is exactly the image of the conditional driver's chosen
trace through that same extension. Finite lifetime endpoints are included.
The actual relative lower tail is not constructed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Exist.Staged Exist.StagedLaw GW2Schedule

/-- The boundary readout is chosen from the retained realization, then works
conditionally for the actual next driver and every witness of its flow law.
Neither an additional field nor an independent trace is substituted. -/
theorem ae_launch_chosenTrace_readout (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∃ (f : ℂ → ℂ) (C : ℝ),
        (∀ z ∈ Hbar, Tendsto c.2.1 (𝓝[H] z) (𝓝 (f z))) ∧
        ContinuousOn f Hbar ∧ (∀ z ∈ Hbar, ‖f z - z‖ ≤ C) ∧
        ∀ (bc : ℝ → ℝ) (jc : Finset ℝ) (hl : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
          IsFlowLineDriver κ bc jc θ (condExpKernel P
            (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀) hl
            (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) →
          ∀ᵐ ω ∂(condExpKernel P
            (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
            (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
              (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) ∧
            schedulePiece κ b jumps x l (fun j => E j ω) k =
              f '' (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t)
                (fun ω => (E k ω).2) ω ''
                  {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (schedDelta 0 l k) (E k ω).2}) ∧
            ContinuousOn (fun t => f (GW2aSingle.chosenTrace
              (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) ω t))
                {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (schedDelta 0 l k) (E k ω).2} := by
  let spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩
  have ht : instrTime spec k = schedDelta 0 l k := by
    unfold instrTime
    rw [isFlowProg_scheduleProgram 0 l k hk]
  filter_upwards [hR.ae_pieceRegular,
    ae_ae_run_eq spec hR (hE.2.1 k) le_rfl,
    KernelTower.ae_ae_condExpKernel_of_ae (hE.2.1 k) hR.ae_pieceRegular]
    with ω₀ hreg₀ hrun hreg c θ hlaunch
  have hc := (eq_launch_of_launches spec (fun j => E j ω₀) hlaunch).2.2
  obtain ⟨f, C, hf, hC⟩ := (GW1P.isClosed_pieces_run spec (fun j => E j ω₀) hreg₀ k).1
  rw [← hc] at hf
  have hfc := GW1P.continuousOn_of_tendsto hf
  refine ⟨f, C, hf, hfc, hC, ?_⟩
  intro bc jc hl hfl
  filter_upwards [hrun, hreg, GW2aSingle.ae_chosenTrace h13 hκ hfl]
    with ω hrunω hregω htr
  have hlω : (ExplState.run κ b jumps spec (fun j => E j ω)
      (k + 1)).2.2.2.1 k = some (c, θ) := by
    rw [launches_run_succ_of_run_eq spec hrunω, hlaunch]
  have hr := hregω k c θ hlω
  rw [ht] at hr
  have hgen := htr.1.mono_horizon (min_le_right (schedDelta 0 l k) (E k ω).2)
  have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (schedDelta 0 l k) (E k ω).2 →
      GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) ω t ∈ Hbar :=
    fun t ht => Sec7.IsGeneratingTrace.mem_Hbar hgen
      (hr.2.1.mono fun s (hs : (s : ℝ≥0∞) < min (schedDelta 0 l k) (E k ω).2) =>
        show (s : ℝ≥0∞) ≤ min (schedDelta 0 l k) (E k ω).2 from hs.le) hr.1 ht
  refine ⟨hlω, ?_, hfc.comp hgen.2.1 hH⟩
  unfold schedulePiece
  change (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.tipSet _ _ = _
  rw [hrunω, ← hc]
  exact CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hr.2.1 hr.1
    (fun t ht => hf _ (hH t ht))

end InteractingSLE.Theorem14.SB.Retain
