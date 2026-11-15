/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Current14
import InteractingSLE.Spec.Sec5.CfLineRegQ
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourRegime

/-!
# Theorem 1.3 supplies the counterflow regularity used only by Theorem 1.5

This adapter is downstream of Theorem 1.3. It must never be fed back into the
Section 5 inputs of Theorems 1.2 or 1.3 (R48). It removes Part A from this
packet's Theorem 1.5 leaf list by specializing the complete trace theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Wire

/-- Aux. 6 supplies infinite lifetime; Theorem 1.3 supplies the complete transient trace. -/
theorem aux7Statement_of_theorem13_current (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) : Sec4.Aux7Statement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P 𝓕 W VL VR B ζ hF hadm hE
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hζ := (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun _ hω => hω.1
  filter_upwards [hζ, h13 hκ hF hE, hE.2.2.2.2] with ω hζω h13ω hp
  obtain ⟨η, hη, htrans⟩ := h13ω.2
  rw [hζω] at hη
  rw [hζω] at hp
  refine ⟨hζω, ⟨η, hη⟩, fun γ hγ => ?_⟩
  have heq : η = γ := funext fun t =>
    IsGeneratingTrace.eq_of_le hη hγ hp.2.2.2.1 hp.1 le_top
  rw [← heq]
  exact htrans hζω

open Sec5 Sec5.Cond44Ref Sec5.CfLineRegQ Sec5.CfRegQ Sec5.Prop411Q WangWu

/-- The existing history certificate and glue transfer, with its trace input supplied by Theorem 1.3. -/
theorem cfLineRegularQStatement_of_theorem13_current (h13 : Exist.Theorem13Statement.{u}) :
    Prop51Q.CfLineRegularQStatement.{u} := by
  intro κ hκ _hκ4 a b θ₁ hb ha Ω mΩ P _ h hh Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * QuantumZipper.chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  obtain ⟨mL, mR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hadm, hE⟩ :=
    exists_seed_of_isCenteredCounterflowDriver hκ hb ha hh hcf hlaw
  have hk' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hF : IsOrderedForceWord (fun _ : Fin mL => (0 : ℝ)) (fun _ : Fin mR => (0 : ℝ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have h7 := aux7Statement_of_theorem13_current h13 hk' _ _ σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hF hadm hE
  have hne := ae_trace_ne_zero_of_seed hk' hadm hE (h7.mono fun _ hω => hω.2.2)
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodRegSet := by
    filter_upwards [h7, hne, hE.2.2.2.2] with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hneω hp
    have hw : Continuous fun t => W₂ t ω := by
      have hc := hp.2.2.2.1
      rw [hζ] at hc
      exact continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodRegSet hζ hw hp.1 hη (hneω η hη) (htr η hη)
  have hg := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory hX₂) hlaw k hk measurableSet_goodRegSet hΩ₂
  exact hg.mono fun _ hp => reg_of_mem_goodRegSet hp

/-- The forward route needs only the finite planar bypass and east-side comparison after Theorem 1.3. -/
theorem prop51QStatement_of_theorem13_current (h13 : Exist.Theorem13Statement.{u})
    (hfinite : Prop51HTopo.FiniteWesternCrosscutBypassStatement)
    (hside : Prop51I.FwdPostContactEastSideQOn.{u}
      fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) : Cond44Ref.Prop51QStatement.{u} := by
  have hreg := cfLineRegularQStatement_of_theorem13_current h13
  apply Prop51G.prop51QStatement_of_on Prop51G.IsLargeGap (Prop51H.prop51QOn_largeGap_of_reg hreg)
  apply Prop51HTopo.prop51QOn_smallGap_of_finiteCrosscutBypass hreg hfinite
  exact Prop51G.fwdFirstContactNotEastQOn_of_split (Prop51G.fwdFirstExitQOn_smallGap hreg)
    (Prop51H.fwdPostContactQOn_of_residual hreg (Prop51I.fwdPostContactEastQOn_of_side hreg hside))

end InteractingSLE.Wire
