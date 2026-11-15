/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Model
import InteractingSLE.Spec.Restart.FlowCodeMain

/-!
# The observable relative tip is a generating trace with zero boundary time

Packet PROVE-T14-GW2ROOT2. The original traces construct the relative
driven curve. Its actual inverse-capacity reader is that curve's canonical
trace, so the landed deterministic boundary-occupation theorem applies.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB
open Sec7.PocketTraversal Sec7.Lemma71C

/-- The observable relative tip has a continuous normalized driver,
generates its hulls through the protected endpoint, and spends zero
relative capacity time outside `H`. All relative regularity is proved. -/
theorem exists_relativeTipRead_generatingTrace_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    let C := (RootZ21.forwardCapacity s v p).toNNReal
    ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧
      ContinuousOn V {t | (t : ℝ≥0∞) ≤ (C : ℝ≥0∞)} ∧
      IsGeneratingTrace V (C : ℝ≥0∞) (fun u => relativeTipRead s v u p) ∧
      volume {t : ℝ | 0 ≤ t ∧ (t.toNNReal : ℝ≥0∞) < (C : ℝ≥0∞) ∧
        relativeTipRead s v t.toNNReal p ∉ H} = 0 := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let a := fun t => RootZ21.forwardCapacity s t p
  let C := (a v).toNNReal
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨ξ, hξ, hL, htip⟩ :=
    exists_driven_relative_tip_model W ζ ω hα hW hW0 hζ hsH he hγ hv
  have hC : (C : ℝ) = a v := Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg s v p)
  have hgen := hξ.isGeneratingTrace hL
  have heq : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ (C : ℝ≥0∞) →
      relativeTipRead s v u p = capTrace ξ u := by
    intro u hu
    have hu' : (u : ℝ) ≤ a v := by
      rw [← hC]
      exact NNReal.coe_le_coe.mpr (ENNReal.coe_le_coe.mp hu)
    have hq := RootZ21.forwardClockInverse_spec_before_contact
      W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv u hu'
    rw [relativeTipRead_eq_before_contact W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv u hu',
      ← htip _ ⟨zero_le, hq.1⟩]
    change capTrace ξ (a (RootZ21.forwardClockInverse s v u p)).toNNReal = capTrace ξ u
    have hqu : a (RootZ21.forwardClockInverse s v u p) = u := hq.2
    rw [hqu, Real.toNNReal_coe]
  have hg := isGeneratingTrace_congr_le hgen heq
  have hc : ContinuousOn (segDriver ξ) {t | (t : ℝ≥0∞) ≤ (C : ℝ≥0∞)} :=
    hξ.segDriver_spec.2.1.mono fun _ ht => ht.trans_lt hL
  exact ⟨segDriver ξ, hξ.segDriver_spec.1, hc, hg,
    hg.volume_setOf_notMem_H
      (hc.mono fun t (ht : (t : ℝ≥0∞) < (C : ℝ≥0∞)) => ht.le) hξ.segDriver_spec.1⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
