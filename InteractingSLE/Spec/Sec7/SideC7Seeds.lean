/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC6Collar
import InteractingSLE.Spec.Sec7.PocketStopSideLimInitial

/-!
# The actual initial seed interval is empty

PROVE-SIDE-COLLAR2. Both actual word shapes have their seed marks at zero.
Causality of the real Loewner flow makes their zero-time coordinates zero,
even though the canonical driver is only locally continuous. Consequently
the initial boundary word is independent of the supplied phase.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoupling Sec7.PocketStopSide Sec7.PocketTraversal Sec7.Lemma71C
  Sec7.PocketAdapt

variable {Ω : Type} [MeasurableSpace Ω]

/-- The two actual target shapes both have literal zero seed marks. -/
theorem target_seed_marks (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (ω : Ω) :
    (j.target i d).marksL ω (Late.leftZero i d j) = 0 ∧
      (j.target i d).marksR ω (Late.rightZero i d j) = 0 := by
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft <;> exact ⟨rfl, rfl⟩

/-- The two centered geometric seed coordinates coincide at relative zero. -/
theorem initial_seed_coordinates {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
        (j.target i d).marksL (Late.leftZero i d j) 0 ω -
        segDriver ((j.target i d).curve ω) 0 = 0 ∧
      geomRW (fun t ω => segDriver ((j.target i d).curve ω) t)
        (j.target i d).marksR (Late.rightZero i d j) 0 ω -
        segDriver ((j.target i d).curve ω) 0 = 0 := by
  have h0 := (isDrivenCurve_target hj ω hω).segDriver_spec.1
  obtain ⟨hL, hR⟩ := target_seed_marks j i d ω
  constructor
  · rw [h0, sub_zero]
    change -MartChar.RealFlow.rightImg
      (Bessel.realPath (fun t ω => -segDriver ((j.target i d).curve ω) t) ω)
      (-((j.target i d).marksL ω (Late.leftZero i d j))) 0 = 0
    rw [hL, neg_zero, rightImg_seed_zero_time (by
      simp only [Bessel.realPath, Real.toNNReal_zero, h0, neg_zero]), neg_zero]
  · rw [h0, sub_zero]
    change MartChar.RealFlow.rightImg
      (Bessel.realPath (fun t ω => segDriver ((j.target i d).curve ω) t) ω)
      ((j.target i d).marksR ω (Late.rightZero i d j)) 0 = 0
    rw [hR]
    exact rightImg_seed_zero_time (by simp only [Bessel.realPath, Real.toNNReal_zero, h0])

/-- At zero capacity the phase-window term vanishes for every phase value. -/
theorem initial_phase_window_eq_zero {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) (δ ξ : ℝ) :
    δ * (Ioo
      (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
        (j.target i d).marksL (Late.leftZero i d j) 0 ω -
        segDriver ((j.target i d).curve ω) 0)
      (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t)
        (j.target i d).marksR (Late.rightZero i d j) 0 ω -
        segDriver ((j.target i d).curve ω) 0)).indicator 1 ξ = 0 := by
  obtain ⟨hL, hR⟩ := initial_seed_coordinates hj hω
  simp only [hL, hR, Ioo_self, indicator_empty, mul_zero]

end InteractingSLE.Wire.Current.SideTest
