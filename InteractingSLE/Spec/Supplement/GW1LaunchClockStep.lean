/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClockCompose

/-!
# GW1: the finite BW1–BW2–BR4a transition and its clock assembly

`IsFiniteRestartPair` records the local terminal-prefix and retargeting conclusion
in the previous counterflow clock. Its conditional-kernel field is substantive
mathematics: the existing BW1 and BR4a statements have no landed providers.
This file proves the deterministic clock assembly from that explicitly named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1LaunchClock

open Exist.Staged Exist.StagedLaw GW1WalkFinish

/-- The local finite terminal-prefix/connector pair in the previous launch clock.
The clock `a` is relative to `V`; its finite cut is an attained first visit to the
whole next raw union. No original-clock identification is assumed here. -/
structure IsFiniteRestartPair (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)
    (V U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (a : Ω → ℝ≥0 → ℝ≥0) : Prop where
  measurable_driver : ∀ t, Measurable (U t)
  conditional : ∀ᵐ ω₀ ∂P, ∀ c θ,
    (ExplState.run κ b jumps spec (fun j => E j ω₀) (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) = some (c, θ) →
    ∀ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      IsCenteredCounterflowDriver κ
        (condExpKernel P (pastSigma κ b jumps spec E (2 * (n + 1))) ω₀) h' U ζ ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E (2 * (n + 1))) ω₀), ζ ω = ⊤
  pathwise : ∀ᵐ ω ∂P, ∀ c θ,
    (ExplState.run κ b jumps spec (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) = some (c, θ) →
    ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0 ∧
    (∃ γ, IsGeneratingTrace (fun t => U t ω) ⊤ γ ∧
      Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    let d := stChart (ExplState.run κ b jumps spec (fun j => E j ω) (2 * n))
    let B := SB.prefixPhysSet κ b jumps spec (fun j => E j ω) (2 * (n + 1))
    ∃ T : ℝ≥0, firstTipTime (d.trans infinitySourceChart) (fun t => V t ω) B = T ∧
      (∃ z ∈ B, (d.trans infinitySourceChart).tipAt (fun t => V t ω) T z) ∧
      Continuous (a ω) ∧ StrictMono (a ω) ∧ range (a ω) = Iio T ∧
      ∀ r z, (c.trans infinitySourceChart).tipAt (fun t => U t ω) r z ↔
        (d.trans infinitySourceChart).tipAt (fun t => V t ω) (a ω r) z

/-- All global-clock conclusions follow by composing a finite local pair with
the previous launch clock. The old retained union remains in the new one. -/
theorem isLaunchClock_succ_of_finiteRestartPair
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W V U : ℝ≥0 → Ω → ℝ} {ζV ζ : Ω → ℝ≥0∞} {ℓ a : Ω → ℝ≥0 → ℝ≥0}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hV : GW1Z.IsLaunchClock κ b jumps P h W spec E (2 * n) V ζV ℓ)
    (hR : IsFiniteRestartPair κ b jumps P h spec E n V U ζ a)
    (hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1
        (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none) :
    GW1Z.IsLaunchClock κ b jumps P h W spec E (2 * (n + 1)) U ζ
      (fun ω => ℓ ω ∘ a ω) := by
  refine ⟨hR.measurable_driver, hR.conditional, ?_⟩
  filter_upwards [hV.2.2, hR.pathwise, hprev] with ω hv hr hp c θ hl
  have hln : (ExplState.run κ b jumps spec (fun j => E j ω)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  obtain ⟨⟨d, θ₀⟩, hd⟩ := Option.ne_none_iff_exists'.1 (hp hln)
  obtain ⟨-, -, -, -, hℓc, hℓm, hℓr, hid⟩ := hv d θ₀ hd
  obtain ⟨hζ, hUc, hU0, hγ, T, hT, hhit, hac, ham, har, hai⟩ := hr c θ hl
  have he : d = stChart (ExplState.run κ b jumps spec (fun j => E j ω) (2 * n)) :=
    (eq_launch_of_launches spec _ hd).2.2
  rw [← he] at hT hhit hai
  have hclock := IsPrefixClock.compose_cut ⟨hℓc, hℓm, hℓr, hid⟩ hT hhit hac ham har hai
  have hsub := GW1Z.prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps)
    spec (fun j => E j ω) (2 * n)
  have hsub' := GW1Z.prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps)
    spec (fun j => E j ω) (2 * n + 1)
  have heq : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  rw [heq] at hsub'
  rw [union_eq_right.2 (hsub.trans hsub')] at hclock
  exact ⟨hζ, hUc, hU0, hγ, hclock⟩

end InteractingSLE.Theorem14.GW1LaunchClock
