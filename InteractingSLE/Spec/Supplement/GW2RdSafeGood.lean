/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdExt
import InteractingSLE.Spec.Supplement.RelSafeGB6Read
import InteractingSLE.Spec.Supplement.SBTail2RetainWord
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# GW2's relative safe law (K2's (S), (L)), part 1: the good event with the curves exchanged

Packet PROVE-GW2-RELDET (K2's (S)/(L) clauses of `GW2RdSafeStatement`). GB6's lines step reads the explored curve in
physical time through a clock `physClock s W Wα ζα GT` built on a good event `GT` (`Supp8.RelSafe.PhysGood`): the
explored driver `W` continuous from `0` with a complete generating trace, the retained driver `Wα` with its trace, the
record of the retained prefix good, and the retained tip the inverse boundary limit of the record driver. All of
`RelSafeGB6Drv`/`RelSafeGB6Read`'s clock layer is stated for arbitrary `(W, Wα, ζα, γ, α)`.

GW2 exchanges the curves: the explored curve is the **extended flow line** `regW s Wα ζα` with its trace
`extTr s Wα ζα α` (`GW2RdExt`), the retained curve is the **counterflow** `(W, ζ, γ)`. This file provides the good event
in that instance (`exists_goodSet_gw2`): its only inputs beyond GB6's are the positive lifetime of the flow at an
admissible seed (`SB.Retain.ae_lifetime_pos_of_seed_admissible`), the extension `GW2Rd.ae_extTr_spec`, and the tip of
the counterflow record (`ae_tendsto_record_tip_top`, from the complete counterflow trace; no `κ < 4`, no no-return).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8.GB6 GW2TipSystem Exist.StagedLaw

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The tip of the record of a complete flow-line driver**: the inverse map of the record driver at `s` tends at `0`
to the trace at `s`. -/
theorem ae_tendsto_record_tip_top {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hfl : IsFlowLineDriver κ b J θ P h W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fwdMapInv (rdrv (gb6Rec s W ζ ω)) s) (𝓝[H] 0) (𝓝 (γ ω s)) := by
  filter_upwards [ae_driver_zero_continuousOn hfl, hγ, hζ] with ω hreg htr hz
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip htr hreg.2 hreg.1 hs
  have hWc : Continuous fun r : ℝ => W r.toNNReal ω := by
    have h1 : ContinuousOn (fun t => W t ω) univ := by
      have e : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = univ := by
        ext t; simp only [hz, mem_ofPred_eq, ENNReal.coe_lt_top, mem_univ]
      rw [← e]; exact hreg.2
    exact (continuousOn_univ.1 h1).comp continuous_real_toNNReal
  refine htip.congr' (eventually_nhdsWithin_of_forall fun z hz' => ?_)
  refine LP.fwdMapInv_eq_of_eqOn_Icc hWc (continuous_rdrv _) (by simp [hreg.1]) (rdrv_zero _) s.coe_nonneg
    (fun x hx => ?_) hz'
  exact (rdrv_recOf_cfE s hreg.1 hreg.2 hs hx.2).symm

/-- **GW2's good event**: GB6's `PhysGood` with the explored curve the extended flow line and the retained curve the
counterflow; measurable, and almost surely the record event of the counterflow prefix. -/
theorem exists_goodSet_gw2 [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ) {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    {h h' : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hadm : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
      (flowLineXR b J 0))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0) :
    ∃ GT : Set Ω, (∀ ω ∈ GT, Supp8.RelSafe.PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s W ζ ω ∈ gb6TS s) := by
  have hall : ∀ᵐ ω ∂P,
      (Continuous (fun t => regW s Wα ζα t ω) ∧ regW s Wα ζα 0 ω = 0 ∧
        IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ (extTr s Wα ζα α ω)) ∧
      (W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
        IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) ∧
      ((s : ℝ≥0∞) < ζ ω → GB6RecGood s W ζ γ ω) ∧
      ((s : ℝ≥0∞) < ζ ω → γ ω s ∈ H →
        Tendsto (fwdMapInv (rdrv (gb6Rec s W ζ ω)) s) (𝓝[H] 0) (𝓝 (γ ω s))) := by
    filter_upwards [ae_extTr_spec hκ hfl hα s, SB.Retain.ae_lifetime_pos_of_seed_admissible hfl hadm,
      ae_driver_zero_continuousOn hcf, hγ, ae_gb6RecGood hcf hγ s, ae_tendsto_record_tip_top hcf hγ hζ s]
      with ω he hpos hd hγω hg htip
    obtain ⟨h1, h2, -, h4, -⟩ := he hpos
    exact ⟨⟨h1, h2, h4⟩, ⟨hd.1, hd.2, hγω⟩, hg, fun _ _ => htip⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hall
  have hrec : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  refine ⟨G ∩ gb6Rec s W ζ ⁻¹' gb6TS s, fun ω hω => ?_, hGm.inter (hrec (measurableSet_gb6TS s)), ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hG ω hω.1
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff h3).2 hω.2
    exact ⟨h1, h2, hs, hsH, h3 hs, h4 hs hsH⟩
  · filter_upwards [hGae] with ω hω
    exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

end Good

end InteractingSLE.Theorem14.GW2Rd
