/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Actual

/-!
# Relative observations do not depend on the later recording horizon

Packet PROVE-T14-GW2ROOT2. Reading an already attained capacity level
from a longer protected physical record gives the same inverse time and
the same actual relative tip. No clock or trace identity is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open Exist Staged StagedLaw Restart Supp8.GB6

/-- An observation through a protected cutoff is unchanged if the
physical record is extended to any later protected cutoff. -/
theorem relativeTipRead_prefix_eq_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v V : ℝ≥0} (hvV : v ≤ V)
    (hV : (V : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    (u : ℝ≥0)
    (hu : (u : ℝ) ≤ RootZ21.forwardCapacity s v
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    relativeTipRead s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) =
      relativeTipRead s V u (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let P := (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e)
  have hv := (ENNReal.coe_le_coe.mpr hvV).trans_lt hV
  have ha := isClockOn_forwardCapacity_before_contact W ζ ω hα hW hW0 hs hsH he hγ hV
  have hab : ∀ t ≤ v, RootZ21.forwardCapacity s t P = RootZ21.forwardCapacity s t p := by
    intro t htv
    exact (RootZ21.forwardCapacity_prefix_eq s _ he (lt_min_iff.mp hV).2
      (htv.trans hvV)).trans
        (RootZ21.forwardCapacity_prefix_eq s _ he (lt_min_iff.mp hv).2 htv).symm
  have huV : (u : ℝ) ≤ RootZ21.forwardCapacity s V P :=
    (hu.trans (hab v le_rfl).ge).trans (ha.strictMonoOn.monotoneOn
      (ENNReal.coe_le_coe.mpr hvV) (show (V : ℝ≥0∞) ≤ (V : ℝ≥0∞) from le_rfl) hvV)
  have hq := RootZ21.forwardClockInverse_spec_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv u hu
  have hQ := RootZ21.forwardClockInverse_spec_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hV u huV
  have hqQ : RootZ21.forwardClockInverse s v u p = RootZ21.forwardClockInverse s V u P :=
    ha.strictMonoOn.injOn (ENNReal.coe_le_coe.mpr (hq.1.trans hvV))
      (ENNReal.coe_le_coe.mpr hQ.1) (((hab _ hq.1).trans hq.2).trans hQ.2.symm)
  rw [relativeTipRead_eq_before_contact W ζ ω hα hW hW0 hs hsH he hγ hv u hu,
    relativeTipRead_eq_before_contact W ζ ω hα hW hW0 hs hsH he hγ hV u huV]
  exact congrArg (fun t => Supp8.GB6.CoordB.relBdry (rdrv p.1) s (γ t)) hqQ

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
