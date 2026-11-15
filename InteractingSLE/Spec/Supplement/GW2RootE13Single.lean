/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE13Carrier

/-!
# The literal carrier of a canonical first schedule piece

Packet PROVE-T14-GW2ROOT2. The already proved single-instruction physical
set and stopped-tip trace formulas identify the actual canonical prefix.
This result permits a finite generating lifetime and uses no relative law.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE13

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric CounterflowRange

/-- A single ordinary instruction from zero has precisely its generating
trace prefix as physical set. The recorded root is already the trace seed. -/
theorem physSet_single_eq_prefix (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (gw : Bool) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    {γ : ℝ≥0 → ℂ} (hgen : IsGeneratingTrace (D 0).1 (D 0).2 γ)
    (hw : ContinuousOn (D 0).1 {t | (t : ℝ≥0∞) ≤ (D 0).2})
    (hw0 : (D 0).1 0 = 0) {v : ℝ≥0} (hv : (v : ℝ≥0∞) ≤ (D 0).2) :
    ExplState.physSet κ b jumps (0, gw, [Sum.inl (θ, (v : ℝ≥0∞))]) D = γ '' Icc 0 v := by
  rw [physSet_single, min_eq_left hv]
  have hS := hgen.mono_horizon hv
  have hwS : ContinuousOn (D 0).1 {t | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} :=
    hw.mono (fun r hr => hr.trans hv)
  rw [tipSet_stopped_eq (continuous_recenter_id_inv 0) hS hwS hw0, recenter_id_inv]
  have hI : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  simp only [hI, Complex.ofReal_zero, add_zero, image_id']
  apply union_eq_right.mpr
  rintro z rfl
  exact ⟨0, ⟨le_rfl, zero_le⟩, hgen.1⟩

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- The actual one-entry canonical schedule has the literal trace carrier
needed by the joint-chart geometry, whenever the cutoff precedes its lifetime. -/
theorem prefixSet_single_eq_prefix (θ : ℝ) (v : ℝ≥0) (ω : Ω) {γ : ℝ≥0 → ℂ}
    (hgen : IsGeneratingTrace
      (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1
      (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2 γ)
    (hw : ContinuousOn (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1
      {t | (t : ℝ≥0∞) ≤ (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2})
    (hw0 : (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1 0 = 0)
    (hv : (v : ℝ≥0∞) ≤ (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2) :
    prefixSet hκ h12p βA b jumps c₀ h 0 [(θ, v)] ω = γ '' Icc 0 v := by
  have hs : schedSpec 0 [(θ, v)] = (0, true, [Sum.inl (θ, (v : ℝ≥0∞))]) := by
    simp only [schedSpec, scheduleProgram, tsub_zero]
  have hres := physSet_single_eq_prefix κ b jumps true θ
    (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) j ω)
    hgen hw hw0 hv
  simpa only [prefixSet, hs] using hres

end InteractingSLE.Theorem14.GW2TipSystem.RootE13
