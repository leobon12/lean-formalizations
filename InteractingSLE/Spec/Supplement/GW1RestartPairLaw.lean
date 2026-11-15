/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairClock

/-!
# The exact terminal-restart and finite-retargeting inputs still needed

These are named conditional inputs, not providers of BW1 or BR4a. The terminal
input concerns the complete piece with all older records retained. The retargeting
input uses its full conditional pair, and conditions on precisely the same past:
the connector has no random retained record. Their deterministic assembly is proved
below. No theorem here asserts either input without hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1RestartPair

open Exist.Staged Exist.StagedLaw

section Pair

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
  (right : Bool) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)

/-- The needed BW1 consequence at a completed piece. The target is its post-piece
chart; the clock is in the previous launch pair. A zero piece permits the identity
pair, as in BW2's initial-singleton case. -/
structure IsTerminalRestart (V Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞)
    (β : Ω → ℝ≥0 → ℝ≥0) : Prop where
  measurable_driver : ∀ t, Measurable (Q t)
  conditional : ∀ᵐ ω₀ ∂P,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
    ∀ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport
        (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E j ω₀) (2 * n + 1))) 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      IsCenteredCounterflowDriver κ
        (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀)
        h' Q ζQ ∧
      ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀), ζQ ω = ⊤
  pathwise : ∀ᵐ ω ∂P,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
    ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0 ∧
    (∃ γ, IsGeneratingTrace (fun t => Q t ω) ⊤ γ ∧
      Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    IsRetainedClock
      ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω) (2 * n))).trans infinitySourceChart)
      ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω) (2 * n + 1))).trans infinitySourceChart)
      (fun t => V t ω) (fun t => Q t ω)
      (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω) (2 * n + 1)) (β ω)

/-- The needed BW2–BR4a consequence inside the post-piece conditional pair.
The kernel is still conditioned on the completed ordinary piece's retained past.
Its finite first contact is with the whole next union, not just the new endpoint. -/
structure IsForcedRetarget (Q U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (a : Ω → ℝ≥0 → ℝ≥0) : Prop where
  measurable_driver : ∀ t, Measurable (U t)
  conditional : ∀ᵐ ω₀ ∂P, ∀ c θ,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) = some (c, θ) →
    ∀ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      IsCenteredCounterflowDriver κ
        (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀)
        h' U ζ ∧
      ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀), ζ ω = ⊤
  pathwise : ∀ᵐ ω ∂P, ∀ c θ,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) = some (c, θ) →
    ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0 ∧
    (∃ γ, IsGeneratingTrace (fun t => U t ω) ⊤ γ ∧
      Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    let d := stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E j ω) (2 * n + 1))
    let B := SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E j ω) (2 * (n + 1))
    ∃ T : ℝ≥0, firstTipTime (d.trans infinitySourceChart) (fun t => Q t ω) B = T ∧
      (∃ z ∈ B, (d.trans infinitySourceChart).tipAt (fun t => Q t ω) T z) ∧
      Continuous (a ω) ∧ StrictMono (a ω) ∧ range (a ω) = Iio T ∧
      ∀ r z, (c.trans infinitySourceChart).tipAt (fun t => U t ω) r z ↔
        (d.trans infinitySourceChart).tipAt (fun t => Q t ω) (a ω r) z

end Pair

/-- The terminal and connector source inputs assemble to the requested finite
pair. Equality of the retained sigma algebras handles the longer-past kernel. -/
theorem isFiniteRestartPair_of_terminal_and_forcedRetarget
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {right : Bool} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    {V Q U : ℝ≥0 → Ω → ℝ} {ζQ ζ : Ω → ℝ≥0∞} {β a : Ω → ℝ≥0 → ℝ≥0}
    (hQ : IsTerminalRestart κ b jumps P h right E n V Q ζQ β)
    (hU : IsForcedRetarget κ b jumps P h right E n Q U ζ a) :
    GW1LaunchClock.IsFiniteRestartPair κ b jumps P h (GW1Z.walkSpec b jumps right)
      E n V U ζ (fun ω => β ω ∘ a ω) := by
  refine ⟨hU.measurable_driver, ?_, ?_⟩
  · filter_upwards [hU.conditional] with ω hu c θ hl h' htr
    have he : condExpKernel P
        (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1))) ω =
        condExpKernel P
          (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω :=
      condExpKernel_walk_connector P E n ω
    rw [he]
    exact hu c θ hl h' htr
  · filter_upwards [hQ.pathwise, hU.pathwise] with ω hq hu c θ hl
    have hn : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none := by
      rw [hl]
      exact Option.some_ne_none _
    obtain ⟨-, -, -, -, hb⟩ := hq hn
    obtain ⟨hζ, hUc, hU0, hγ, T, hT, hhit, hac, ham, har, hai⟩ := hu c θ hl
    have hclock := hb.compose_cut hT hhit hac ham har hai
    have hcut := firstTipTime_eq_of_retainedClock hb hT hhit
    refine ⟨hζ, hUc, hU0, hγ, β ω T, hcut, ?_, hclock.1, hclock.2.1, ?_, hclock.2.2.2⟩
    · obtain ⟨z, hz, ht⟩ := hhit
      exact ⟨z, hz, (hb.2.2.2 T z).1 ht⟩
    · rw [hclock.2.2.1, hcut]
      ext t
      simp only [mem_ofPred_eq, mem_Iio, ENNReal.coe_lt_coe]

end InteractingSLE.Theorem14.GW1RestartPair
