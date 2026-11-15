/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice16Setup

/-! # The exact comparison field from retained physical boundary germs

`PastGermCover` isolates the remaining physical access, local containment,
and height/lift limit. All marked unions and smaller local-set means are
constructed from the actual coupling, for the exact current cut family.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice16
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst Aux61GR1F Aux61GAlign
open LawUnique GlueCond
universe u

/-- The remaining full-ball physical boundary comparison, with every own
reference time clamped to the retained time. This proposition includes no
marked-union or local-mean existence assertion. -/
def PastGermCover (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
    (i : F.ι) (q : ℚ) : Prop :=
  ∀ᵐ x ∂S.μ, (S.marksData F).Z i x ∈ (S.marksData F).B i →
    ∀ b ∈ ((S.marksData F).data i).O₀,
    ∃ (j : SourceReferenceIndex) (z₀ : ℂ),
      z₀ ∈ sourceReferenceSet S (pastReferenceIndex q j) x ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, (S.marksData F).baseSets i 0 x ∩ ball z₀ r ⊆
        sourceReferenceSet S (pastReferenceIndex q j) x) ∧
      Tendsto ((S.marksData F).chart i x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
      Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q j) x
        (((S.marksData F).chart i x).2.1 z) + (S.marksData F).scale +
        (S.marksData F).constant * ((S.marksData F).chart i x).2.2
          (((S.marksData F).chart i x).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
        (𝓝[H] (b : ℂ)) (𝓝 0)

/-- The existing `ChoiceInputs.comparisons` type, without a supplied
`ReferenceUnions`, restart-facts, marked-measurability or mean-family input.
Only the physical germ cover remains beyond the restart/window inputs. -/
theorem choice_comparisons_of_past_germs {S : SourceSetting.{u}} (C : RestartChoices S)
    (hsel : ∀ i, MeasurableSet (C.selected i)) (w : WindowFields C.toR1Restart)
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (V : Aux61SlitWZ.SeedWindows C)
    (hfinite : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      ∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
        boundedInverse (sourceChart C.fam (rationalTime S.s)
          S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1)
    (hgerms : ∀ i, PastGermCover S (cutSource S (withRecordPath S C.fam)) i (C.q i.1)) :
    ∀ i, Nonempty (Aux61GAlign.ZeroComparisons
      (S.marksData (cutSource S (withRecordPath S C.fam))) i) := by
  intro i
  apply source_comparisons_of_past_germs S (cutSource S (withRecordPath S C.fam))
    (choice_cut_restart C hsel w hg V hfinite) i (C.q i.1) rfl
    (choice_cut_sets_recorded C hsel w hg V hfinite i) _ (hgerms i)
  filter_upwards [Aux61SlitWZ.ae_chart_topology C i] with p hp he
  exact (hp he.1).2.1

end InteractingSLE.Sec5.Aux61GChoice16
