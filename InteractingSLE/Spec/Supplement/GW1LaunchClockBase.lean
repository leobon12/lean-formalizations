/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClock

/-! # GW1: the launch clock at the original seed -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1LaunchClock

open Exist.Staged Exist.StagedLaw

/-- The base datum uses a measurable version of the original counterflow, with the
identity clock. No conditional counterflow restart law is required at the root. -/
theorem exists_isLaunchClock_zero (hT13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (spec : ExplSpec) (hx : spec.1 = 0) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∃ V : ℝ≥0 → Ω → ℝ, GW1Z.IsLaunchClock κ b jumps P h W' spec E 0 V ζ' (fun _ => id) := by
  obtain ⟨V, hVm, hVc, he⟩ := exists_measurable_counterflow_version hcf hζ
  have hreg := ae_counterflow_regular hT13 hκ hcf hζ
  have hchart (ω : Ω) (c : Chart) (θ : ℝ)
      (hl : (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.1 0 =
        some (c, θ)) : c = Chart.id.recenter 0 := by
    have hc := (eq_launch_of_launches spec _ hl).2.2
    change c = Chart.id.recenter spec.1 at hc
    rwa [hx] at hc
  refine ⟨V, hVm, Eventually.of_forall fun ω₀ c θ hl h' ht => ?_, ?_⟩
  · have hc := hchart ω₀ c θ hl
    subst c
    have hh' : h' = h := funext fun ω => by
      rw [GW2aPiece.eq_flowField_of_isChartTransport (ht ω), Sec7.Prop74B.flowField_zero_zero]
    subst h'
    rw [GW1.pastSigma_zero_eq_bot, GW1.condExpKernel_bot_apply]
    exact ⟨hVc, hζ⟩
  · filter_upwards [hζ, he, hreg] with ω hζω heω ⟨hW, hW0, γ, hγ, htr⟩ c θ hl
    have hc := hchart ω c θ hl
    have hA : SB.prefixPhysSet κ b jumps spec (fun j => E j ω) 0 = {(0 : ℂ)} := by
      simp [SB.prefixPhysSet, ExplState.run, ExplState.init, hx]
    refine ⟨hζω, ?_, ?_, ?_, continuous_id, strictMono_id, ?_, ?_⟩
    · simpa only [heω] using hW
    · exact congrFun heω 0 |>.trans hW0
    · exact ⟨γ, heω.symm ▸ hγ, htr⟩
    · rw [hA, firstTipTime_root_eq_top hγ hW hW0]
      ext s
      simp only [range_id, mem_univ, mem_ofPred_eq, ENNReal.coe_lt_top]
    · intro r z
      rw [hc, heω]
      exact GW2Later.tipAt_recenter_zero_trans

end InteractingSLE.Theorem14.GW1LaunchClock
