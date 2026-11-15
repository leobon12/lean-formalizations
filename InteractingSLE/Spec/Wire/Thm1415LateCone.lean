/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415LateReg
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Wire
open Theorem14 Theorem14.GW2Tip Theorem14.GW2Cone Theorem14.GW2Schedule
  Theorem14.GW2Later Theorem14.GW2Sched Theorem14.GW2aMulti

/-- The full light cone using only R51 containment. -/
theorem lightCone14Statement_of_inputs_late (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hEx : GW2TipExhaustionAllQStatement.{u})
    (hA : GW2aCont.GW2aContainmentRegStatement.{u}) : LightCone14Statement.{u} := by
  have hQ := gw2InteriorScheduleQStatement'_of_param h13 h12p
  have hGW2 := gw2LightConeR51Statement_current h13 h13₀ hBR4a hGB6 hG hQ hEx
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQ'⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ⟨hQ' E hE hreg, fun 𝒞 h𝒞 h𝒞p => ?_⟩⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg p (h𝒞p p hp)
  filter_upwards [hQ' E hE hreg, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

/-- All frontier clauses, including the R51 nowhere-filling consequence. -/
theorem frontiers14Statement_of_reg_late (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) : Frontiers14Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  have hR := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
      (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  have hL := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
      (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)
  filter_upwards [hR, hL, hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    LateReg.gw6Statement_of_gw2a_lateReg hA GW1.gw1FirstThresholdStatement κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg]
    with ω hRω hLω hFω h6ω
  exact ⟨⟨hRω, hFω.1⟩, ⟨hLω, hFω.2⟩, h6ω⟩

end InteractingSLE.Wire
