/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415CurrentStatements
import InteractingSLE.Spec.Supplement.GW2ConeQFixed
import InteractingSLE.Spec.Supplement.BR6ProofArc

/-!
# The corrected interior schedule route without the obsolete BR6 hypothesis

The sole use of BR6 in `GW2ConeQFixed` is the forced original-boundary arc.
`BR6ProofArc` already proves exactly that arc from Theorem 1.3. This adapter
specializes the same containment and closure argument to the landed arc theorem.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
universe u
namespace InteractingSLE.Wire
open Theorem14 Theorem14.GW2Tip Theorem14.GW2Cone Theorem14.GW2Schedule
  Theorem14.GW2Later Theorem14.GW2Sched Theorem14.GW2aMulti

/-- R51 GW2 with interior tips only at actual launches and the forced arcs discharged. -/
theorem gw2LightConeR51Statement_current (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (hQ : GW2InteriorScheduleQStatement'.{u}) (hEx : GW2TipExhaustionAllQStatement.{u}) :
    GW2LightConeR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQint⟩ := hQ κ hκ hκ4 b jumps hb P h hh Θ hΘ hΘc
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ?_⟩
  have hStep := gb6PastStepStatement_of_prefix hG hT13
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  have hsched : ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l ∈ {l | IsSchedule Θ Q l},
      ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    fun x hx l hl => GW2Tip.ae_physSet_subset_of_step_launched hStep hBR4a hGB6 hT13 hT13₀
      hκ hκ4 hb hh hcf hζ' hE hreg hx
      (mem_Icc_of_isSchedule hΘ hl) hl.2 (hQint E hE hreg x hx l hl)
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

/-- The full version-2 light-cone conclusion from the corrected schedule and the landed forced arcs. -/
theorem lightCone14Statement_of_inputs_current (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hEx : GW2TipExhaustionAllQStatement.{u})
    (hA : GW2aContainmentStatement.{u}) : LightCone14Statement.{u} := by
  have hQ := gw2InteriorScheduleQStatement'_of_param h13 h12p
  have hGW2 := gw2LightConeR51Statement_current h13 h13₀ hBR4a hGB6 hG hQ hEx
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQ'⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ⟨hQ' E hE hreg, fun 𝒞 h𝒞 h𝒞p => ?_⟩⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE p (h𝒞p p hp)
  filter_upwards [hQ' E hE hreg, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

end InteractingSLE.Wire
