/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Observe

/-!
# Continuity of the observable tip in the actual relative capacity time

Packet PROVE-T14-GW2ROOT2. Original trace geometry proves the existing
clock predicate. Its inverse is continuous, so the boundary tip reader is
continuous through every protected attained endpoint and starts at zero.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
  (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
  {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ QuantumZipper.H)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)

include hα hW hW0 hs hsH he hγ hv

/-- The existing clock predicate is a conclusion of the two original
generating traces, without a new clock hypothesis. -/
theorem isClockOn_forwardCapacity_before_contact :
    IsClockOn (fun t => RootZ21.forwardCapacity s t
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) (v : ℝ≥0∞) := by
  obtain ⟨h0, hm, hc⟩ := RootZ21.forwardCapacity_regular_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  exact ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩

/-- The observable relative tip is continuous on the full attained
capacity interval, including its initial and final endpoints. -/
theorem continuousOn_relativeTipRead_before_contact :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    ContinuousOn (fun u => relativeTipRead s v u p)
      {u : ℝ≥0 | (u : ℝ) ≤ RootZ21.forwardCapacity s v p} := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let a := fun t => RootZ21.forwardCapacity s t p
  have ha := isClockOn_forwardCapacity_before_contact W ζ ω hα hW hW0 hs hsH he hγ hv
  have hsub : {u : ℝ≥0 | (u : ℝ) ≤ a v} ⊆
      {u | (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞)} := by
    intro u hu
    change (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞)
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe,
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hu
  have hc := (continuousOn_record_relBdry_before_contact W ζ ω hα hW hW0 hs he hγ hv).comp
    (ha.continuousOn_invClock.mono hsub) (fun u hu =>
      ⟨zero_le, ENNReal.coe_le_coe.mp (ha.invClock_spec (hsub hu)).1⟩)
  exact hc.congr fun u hu =>
    relativeTipRead_eq_before_contact W ζ ω hα hW hW0 hs hsH he hγ hv u hu

theorem relativeTipRead_zero_before_contact :
    relativeTipRead s v 0 (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) = 0 := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  have ha := isClockOn_forwardCapacity_before_contact W ζ ω hα hW hW0 hs hsH he hγ hv
  have hu := RootZ21.forwardCapacity_nonneg s v p
  have hh := RootZ21.forwardClockInverse_spec_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv 0 hu
  have hz : RootZ21.forwardClockInverse s v 0 p = 0 :=
    ha.strictMonoOn.injOn (ENNReal.coe_le_coe.mpr hh.1) (bot_le : (0 : ℝ≥0∞) ≤ v)
      (hh.2.trans ha.zero.symm)
  rw [relativeTipRead_eq_before_contact W ζ ω hα hW hW0 hs hsH he hγ hv 0 hu,
    hz, hγ.1, relBdry_zero (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg]

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
