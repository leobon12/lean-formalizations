/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Initial
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# The original zero-time reference has the initial pocket lift

PROVE-SIDE-COLLAR2 continuation. Before the first attachment the erasure
clock vanishes. At original time zero, both actual pocket shapes therefore
have relative capacity zero. This reference needs no interior visit.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec6

/-- An erasure clock supported strictly after its starting time is zero
at any earlier time. -/
theorem erasureClock_eq_zero_of_le {I : Set ℝ} {τ t : ℝ}
    (hI : I ⊆ Ioi τ) (ht : t ≤ τ) : erasureClock I τ t = 0 := by
  unfold erasureClock
  calc
    (∫ s in τ..t, I.indicator (fun s => Real.exp (-s)) s) = ∫ _ in τ..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact indicator_of_notMem (fun h => (hI h).not_ge hs.2) _
    _ = 0 := intervalIntegral.integral_zero

end InteractingSLE.Sec6

namespace InteractingSLE.Wire.Current.SideTest

open Sec6 Sec7 Sec7.PocketStopMarked Sec7.PocketStop Sec7.PocketTraversal
  Sec7.PocketCoupling Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- At original time zero the actual relative capacity is zero, for either
pocket shape. The first-hit times are nonnegative by construction. -/
theorem visitCapacity_zero {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    j.visitCapacity d ω 0 = 0 := by
  have hc := (isDrivenCurve_target (i := i) hj ω hω).capClock_zero
  rw [target_curve] at hc
  unfold visitCapacity
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [relCap, relTime, pocketClock, erasureClock_eq_zero_of_le
      (fun _ h => h.1.1) (Sec7.PocketTraversalMeasRand.firstHit_nonneg _ _), zero_div]
    exact hc
  · simp only [hI, ↓reduceIte] at hc ⊢
    rw [relCapInf, relTimeInf, pocketClockInf, erasureClock_eq_zero_of_le
      (fun _ h => h.1) (Sec7.PocketTraversalMeasRand.firstHit_nonneg _ _), zero_div]
    exact hc

/-- The literal reference-visit lift at original zero is the base lift. -/
theorem referenceVisitChart_zero_lift {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    (j.referenceVisitChart i d ω 0).2.2 = ((j.target i d).baseChart ω).2.2 := by
  rw [referenceVisitChart, visitCapacity_zero hj hω, Real.toNNReal_zero]
  exact Theorem14.GW2aCont.loewner_zero_lift

end InteractingSLE.Wire.Current.SideTest
