/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KqWord
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# SB2(1)'s late (S) line mean, part 6: the chain record's physical driver is the coupling driver

Packet PROVE-T14-SB2DRV (round 9). FIN's configuration is built (`FinRel.isRelConfigJK_of_s2_liftOn`) with the physical
driver `w` of the chain record (a global Loewner trace), while FIN's hull and its mean come from the flow-line coupling
with driver `W` (`GW2Fb.ae_eqOn_explMean_stop` needs a global continuous driver agreeing with `W` past the stop).
**`eqOn_driver_of_trace`**: a continuous driver from `0` whose Loewner trace agrees with the coupling's generating trace
on `[0, t₂]`, below the lifetime, equals the coupling driver on `[0, t₂]` (hulls agree: `fwdHull_eq_fillH_of_isFilling`;
drivers from hulls: `Sec6.eqOn_of_fwdHull_eq`).

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.SB.Lv

/-- **A continuous driver whose Loewner trace is the coupling's generating trace on `[0, t₂]` is the coupling driver
there**, below the lifetime. -/
theorem eqOn_driver_of_trace {w : ℝ → ℝ} {ηw : ℝ → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w ηw) {W : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < ζ'}) (hW0 : W 0 = 0) (htr : IsGeneratingTrace W ζ' γ)
    {t₂ t₂' : ℝ≥0} (h12 : t₂ < t₂') (ht₂' : (t₂' : ℝ≥0∞) < ζ')
    (hagree : ∀ r : ℝ, 0 ≤ r → r ≤ t₂ → ηw r = γ r.toNNReal) :
    EqOn w (fun r : ℝ => W r.toNNReal) (Icc 0 t₂) := by
  -- a globally continuous version of the coupling driver up to `t₂'`
  set Wf : ℝ → ℝ := fun r => W (min r t₂').toNNReal with hWf
  have hWfc : Continuous Wf := by
    have hm : Continuous fun r : ℝ => (min r t₂').toNNReal :=
      continuous_real_toNNReal.comp (continuous_id.min continuous_const)
    refine hWc.comp_continuous hm fun r => ?_
    show (((min r t₂').toNNReal : ℝ≥0) : ℝ≥0∞) < ζ'
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht₂'
    rw [← NNReal.coe_le_coe]
    by_cases hr : 0 ≤ min r (t₂' : ℝ)
    · rw [Real.coe_toNNReal _ hr]
      exact min_le_right _ _
    · rw [Real.toNNReal_of_nonpos (le_of_not_ge hr)]
      exact t₂'.coe_nonneg
  have hWf0 : Wf 0 = 0 := by
    simp only [hWf, min_eq_left t₂'.coe_nonneg, Real.toNNReal_zero, hW0]
  have hagreeW : EqOn (fun r : ℝ => W r.toNNReal) Wf (Icc 0 t₂') := fun r hr => by
    simp only [hWf, min_eq_left hr.2]
  -- the hulls agree on `[0, t₂]`
  have hhull : ∀ s ∈ Icc (0 : ℝ) t₂, fwdHull w s = fwdHull Wf s := by
    intro s hs
    have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ' := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) (lt_trans (ENNReal.coe_lt_coe.2 h12) ht₂')
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have hc : ContinuousOn γ (Icc 0 s.toNNReal) :=
      htr.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hsζ.le
    have hcpt : IsCompact (γ '' Icc 0 s.toNNReal) := isCompact_Icc.image_of_continuousOn hc
    have h1 : fwdHull (fun r : ℝ => W r.toNNReal) (s.toNNReal : ℝ) = fillH (γ '' Icc 0 s.toNNReal) :=
      Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hcpt (htr.2.2 _ hsζ)
    rw [Real.coe_toNNReal _ hs.1] at h1
    have h2 : ηw '' Icc 0 s = γ '' Icc 0 s.toNNReal := by
      rw [← Restart.realPath_image_Icc γ hs.1]
      exact Set.image_congr fun r hr => hagree r hr.1 (hr.2.trans hs.2)
    rw [hη.2.2 s hs.1, h2, ← h1]
    exact LocalExt.fwdHull_congr_of_eqOn_of_lt hs.1 (lt_of_le_of_lt hs.2 (NNReal.coe_lt_coe.2 h12)) hagreeW
  have heq := Sec6.eqOn_of_fwdHull_eq hw hWfc hw0 hWf0 t₂.coe_nonneg hhull
  intro r hr
  rw [heq hr]
  exact (hagreeW ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 h12.le)⟩).symm

end InteractingSLE.Theorem14.SB.Lv
