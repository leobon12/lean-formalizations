/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.LightConeAllQ.Core
import InteractingSLE.Spec.Wire.Thm1415CurrentCone
import InteractingSLE.Spec.Seal.PrepT1415
import InteractingSLE.Spec.Wire.T14FnTop

/-!
# Theorem 1.4's light cone for every prescribed schedule set (ruling R126)

Packet PROVE-T14-ALLQ.

* `lightConeAllSchedule_of_inputs` (conditional assembly): `Wire.gw2LightConeR51Statement_current` and
  `Wire.lightCone14Statement_of_inputs_late` with the schedule set `Q` given instead of chosen. The containment of
  each schedule's path uses the core `GW2InteriorScheduleAllQStatement` at the given `Q`; the tip exhaustion already
  holds for every `Q`.
* **`lightConeAllSchedule_holds`**: `LightConeAllScheduleStatement` proved. The inputs are discharged inline exactly as
  in `Seal.Prep.lightCone14Statement_of_thm12_thm13_tests` (Theorems 1.2–1.3 from `Wire.T14Asm7`, GW2's root tests
  from `Wire.T14Fn.gw2RootTestStatement_closed`), and the core by `gw2InteriorScheduleAllQ_holds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.LightConeAllQ

open Theorem14 Theorem14.GW2Tip Theorem14.GW2Cone Theorem14.GW2Schedule Theorem14.GW2Later Theorem14.GW2Sched
  Theorem14.GW2aMulti

/-- **Theorem 1.4's light cone for a given schedule set, from its inputs** (conditional assembly; the successor of
`Wire.gw2LightConeR51Statement_current` and `Wire.lightCone14Statement_of_inputs_late` with `Q` given): Theorem 1.3
(at `u` and `0`), BR4a, GB6's restart law, GB6 conditioned on the prefix, the core (interior switching tips at every
deterministic schedule), the tip exhaustion for every `Q` and Lemma GW2a's containment. -/
theorem lightConeAllSchedule_of_inputs (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (hint : GW2InteriorScheduleAllQStatement.{u}) (hEx : GW2TipExhaustionAllQStatement.{u})
    (hA : GW2aCont.GW2aContainmentRegStatement.{u}) : LightConeAllScheduleStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos E hE hreg
  have hStep := gb6PastStepStatement_of_prefix hG hT13
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  have hsched : ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l ∈ {l | IsSchedule Θ Q l},
      ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    fun x hx l hl => GW2Tip.ae_physSet_subset_of_step_launched hStep hBR4a hGB6 hT13 hT13₀
      hκ hκ4 hb hh hcf hζ' hE hreg hx (mem_Icc_of_isSchedule hΘ hl) hl.2
      (hint κ hκ hκ4 b jumps hb P h hh Θ hΘ hΘc Q hQc hQd hQpos E hE hreg x hx l hl)
  have h0 : ∀ᵐ ω ∂P, ∀ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
      (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hSc).2 fun l hl => hsched 0 (Or.inl rfl) l hl
  have harc : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps,
      ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => GW2Cone.gw2ForcedArcStatement_of_theorem13 hT13 hT13₀
      κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv
  have hv : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => (ae_ball_iff hSc).2 fun l hl => hsched v (Or.inr hv) l hl
  have hEQ := hEx κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos E hE hreg
  have hcone : ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
      counterflowCompletedRange (fun t => W' t ω) := by
    obtain ⟨b', J', h', -, -, hfl⟩ := hcf
    have hκ' : 0 < 16 / κ := by positivity
    have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hfl
    have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
    have hγtop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (GW2aSingle.chosenTrace W' ζ' ω) := by
      filter_upwards [hγ, hζ'] with ω hω hζ
      rw [hζ] at hω
      exact hω.1
    have hex : ∀ᵐ ω ∂P, ∀ q : ℚ, GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal ∈ H →
        -(GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal)⁻¹ ∈
          closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω)) :=
      ae_all_iff.2 fun q => hEQ (GW2aSingle.chosenTrace W' ζ') hγtop (q : ℝ).toNNReal
    filter_upwards [hγ, hζ', hdrv, h0, harc, hv, hex] with ω hγω hζω hdω h0ω harcω hvω hexω
    rw [hζω] at hγω hdω
    have hWc : Continuous fun t => W' t ω := by
      have hc := hdω.2
      simp only [ENNReal.coe_lt_top, ofPred_true] at hc
      exact continuousOn_univ.1 hc
    exact closure_union_zero_eq hγω.1 hWc hdω.1 (hγω.2 rfl)
      (boundaryLightConeFamily_subset h0ω harcω hvω) hexω
  refine ⟨hcone, fun 𝒞 h𝒞 h𝒞p => ?_⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg p (h𝒞p p hp)
  filter_upwards [hcone, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

section Closed

open Wire

/-- **Theorem 1.4, light cone, for every prescribed schedule set** (ruling R126): for every deterministic countable
dense `Q ⊂ (0, ∞)` (for instance the positive rationals, as in the paper, p. 22), almost surely the closure of the
boundary light-cone family with switching times in `Q` (together with `0`, and with any countable family of
boundary-continued programs from `0`) is the completed counterflow range. Theorems 1.2–1.3 and GW2's root tests enter
inline, as in `Seal.Prep.lightCone14Statement_of_thm12_thm13_tests` (rulings R48, R123). -/
theorem lightConeAllSchedule_holds : LightConeAllScheduleStatement.{u} := by
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 T14Asm7.h12.{u} T14Asm7.h13.{u} T14Asm7.h12₀ T14Asm7.h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 T14Asm7.h12.{u} T14Asm7.h13.{u}
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12.{u} T14Asm7.h13.{u}
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p T14Asm7.h12.{u} T14Asm7.h13.{u} T14Asm7.h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ T14Asm7.h13₀)
  have hFix := GW2aForce.flowFixedTimeInteriorStatement_of_thm13 T14Asm7.h13.{u}
  have hForce := GW2aConn.gw2aConnectorForcingStatement_of_theorem13 T14Asm7.h13.{u} T14Asm7.h13₀
  have hA := GW2aStep.gw2aContainmentRegStatement_of_bw1 hD T14Asm7.h12.{u} T14Asm7.h13.{u} T14Asm7.h12₀
    T14Asm7.h13₀ hBW1 hFix hForce hBR4a
  have hGB6 := gb6RestartStatement_of_hullDet_now T14Asm7.h12₀ T14Asm7.h13₀ hD
  have hG := BRLeaf.gb6PrefixPairStatement_of_hullDet hD T14Asm7.h12.{u} T14Asm7.h13.{u} T14Asm7.h12₀ T14Asm7.h13₀
  have hU := GW2TipSystem.gw2TipJointUnboundedStatement_of_candR
    (GW2TipSystem.gw2RootCandRStatement_of_test T14Fn.gw2RootTestStatement_closed.{u})
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ T14Asm7.h12.{u} T14Asm7.h13.{u}
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightConeAllScheduleStatement.{u} :=
    lightConeAllSchedule_of_inputs T14Asm7.h13.{u} T14Asm7.h13₀ hBR4a hGB6 hG gw2InteriorScheduleAllQ_holds hEx hA
  exact @hCone

end Closed

end InteractingSLE.LightConeAllQ
