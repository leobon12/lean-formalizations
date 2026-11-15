/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17SeedSource
import InteractingSLE.Spec.Sec5.Aux61SlitWAABufferMeas

/-! # Initial-record restrictions for uniformly finite canonical windows -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61FibData Aux61GInst Aux61GWord LawUnique
universe u

/-- A window together with a seed piece whose fixed collar contains its gap. -/
abbrev AllowedWindow := {p : SeedWindowIndex × (ℕ × ℕ) //
  ((p.1 : WindowIndex).2.2 : ℝ) ≤ collarRadius p.2.1}

/-- All tests are predicates of the initial record. No continuation or
future capture appears in this selection. -/
def windowRecords (S : SourceSetting.{u}) (t : GoodTime S) (J : AllowedWindow) :
    Set (SourceRecord S.nL S.nR) :=
  {y | y ∈ certifiedRecords S t ∧
    (∀ z ∈ closure (outerBuffer J.1.1) ∩ Hbar, boundedInverse (recordChart S t y) z ≠ 1) ∧
    y ∈ seedPiece S t J.1.2}

theorem measurableSet_windowRecords (S : SourceSetting.{u}) (t : GoodTime S) (J : AllowedWindow) :
    MeasurableSet (windowRecords S t J) := by
  have hm := Aux61SlitWAA.measurableSet_finite_buffer (measurableSet_certifiedRecords S t)
    (recordChart_spec S t).measurable (fun y _ => (recordChart_spec S t).conformal y)
    (fun _ hy => recordChart_extension S t hy) J.1.1.2.2.2.2
  convert hm.inter (measurableSet_seedPiece S t J.1.2) using 1
  ext y
  exact and_assoc.symm

/-- Every admitted record has the fixed free seed collar. -/
theorem seed_on_windowRecords (S : SourceSetting.{u}) (t : GoodTime S) (J : AllowedWindow)
    {y : SourceRecord S.nL S.nR} (hy : y ∈ windowRecords S t J) {a : ℝ}
    (ha : |a| < ((J.1.1 : WindowIndex).2.2 : ℝ)) :
    boundedInverse (recordChart S t y) (a : ℂ) ∉
      Aux61SlitWAB.recordBoundary (rationalTime S.s) y.1 :=
  seedPiece_free S t J.1.2 hy.2.2 (ha.le.trans J.2)

/-- Every admitted record has a bounded physical inverse-window image. -/
theorem isBounded_inverse_on_windowRecords (S : SourceSetting.{u}) (t : GoodTime S) (J : AllowedWindow)
    {y : SourceRecord S.nL S.nR} (hy : y ∈ windowRecords S t J) :
    Bornology.IsBounded ((recordChart S t y).2.1 '' (bufferedWindow J.1.1 ∩ H)) :=
  Aux61GR1F.isBounded_inverse_window ((recordChart_spec S t).conformal y)
    (windowGeometry J.1.1).window_sub J.1.1.2.2.2.2 (recordChart_extension S t hy.1).2 hy.2.1

end InteractingSLE.Sec5.Aux61GWindow17
