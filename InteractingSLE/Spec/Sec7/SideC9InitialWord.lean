/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8Transport
import InteractingSLE.Spec.Sec7.SideVisLate

/-!
# Initial native coordinates and their raw-mark extension

PROVE-SIDE-COLLAR2. Resolve the zero-time coordinate adapter in the initial
mean formula using local driver causality, without global continuity of
the canonical driver. The signed-mark hypotheses are explicit in these
pathwise helpers; no initial mean formula or source theorem is asserted.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open InteractingSLE.MartChar.RealFlow
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- The literal dual parameter in the native side target is the original one. -/
theorem target_kappa_eq (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) :
    (j.target i d).kappa = i.kappa := by
  have hκ : i.kappa ≠ 0 := (lt_trans (by norm_num) i.kappa_gt_four).ne'
  rw [Late.target_kappa]
  field_simp

/-- Both side-target shapes retain the supplied physical harmonic function. -/
theorem target_harmonic_eq (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) :
    (j.target i d).harmonic = d.harmonic := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

/-- Signed raw marks are the exact centered geometric coordinates at zero. -/
theorem initial_positions_eq_marks_of_signed_marks {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event)
    (hL : ∀ a, (j.target i d).marksL ω a ≤ 0)
    (hR : ∀ a, 0 ≤ (j.target i d).marksR ω a) :
    (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
      (j.target i d).marksL a 0 ω - segDriver ((j.target i d).curve ω) 0) =
        (j.target i d).marksL ω ∧
      (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t)
        (j.target i d).marksR a 0 ω - segDriver ((j.target i d).curve ω) 0) =
        (j.target i d).marksR ω := by
  have hDriven := isDrivenCurve_target hj ω hω
  obtain ⟨W, hW, hW0, q', hq', hEq, -⟩ :=
    exists_relChart_eq_loewner (c := (j.target i d).baseChart) hDriven
      (PocketPhaseMeans.capLife_pos hDriven)
  have hEq0 : EqOn (fun r : ℝ => segDriver ((j.target i d).curve ω) r.toNNReal) W
      (Icc 0 ((0 : ℝ≥0) : ℝ)) := fun r hr => hEq r ⟨hr.1, hr.2.trans hq'.le⟩
  have hCoords := geom_positions_eq_of_driver_eqOn
    (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hW hEq0
  constructor
  · funext a
    rw [congrFun hCoords.1 a, NNReal.coe_zero,
      rightImg_zero (w := fun r => -W r) hW.neg (by rw [hW0, neg_zero])
        (neg_nonneg.2 (hL a)),
      hW0, sub_zero, neg_neg]
  · funext a
    rw [congrFun hCoords.2 a, NNReal.coe_zero, rightImg_zero hW hW0 (hR a), hW0, sub_zero]

/-- The initial extension in the remaining formula is the raw-mark mean
extension once the initial marks have their stated signs. -/
theorem initialWordExtension_eq_raw_of_signed_marks {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event)
    (hL : ∀ a, (j.target i d).marksL ω a ≤ 0)
    (hR : ∀ a, 0 ≤ (j.target i d).marksR ω a) :
    j.initialWordExtension i d ω = MartChar.meanExt (j.target i d).kappa
      (j.target i d).rhoL (j.target i d).rhoR 0
      ((j.target i d).marksL ω) ((j.target i d).marksR ω) := by
  obtain ⟨hL0, hR0⟩ := initial_positions_eq_marks_of_signed_marks hj hω hL hR
  unfold initialWordExtension
  rw [hL0, hR0]

end InteractingSLE.Wire.Current.SideTest
