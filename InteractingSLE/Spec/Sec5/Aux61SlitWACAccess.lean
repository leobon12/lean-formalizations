/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWACStable

/-! # Fixed normalized accesses across window and index refinements

Equal retained times give equal complete chart witnesses and physical
contact rules. On samples selected by both indices the entire normalized
access is therefore identical, independently of either candidate window.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAC
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Asm2 Aux61FibData Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (C D : RestartChoices S)

/-- The physical contact rule depends only on the retained time, with
no chart normalization or future selection argument. -/
theorem contact_eq_of_time_eq (i : C.Idx) (j : D.Idx) (hq : C.q i.1 = D.q j.1) :
    C.fam.contact i = D.fam.contact j := by
  change C.toR1Restart.contact i = D.toR1Restart.contact j
  unfold R1Restart.contact
  dsimp only [RestartChoices.toR1Restart]
  rw [hq]

/-- Equal retained times give the same actual normalized chart at every
sample, even for different index types and selected-record predicates. -/
theorem normalized_sourceChart_eq_of_time_eq (i : C.Idx) (j : D.Idx)
    (hq : C.q i.1 = D.q j.1) :
    sourceChart (source C.toR1Restart C.hasChart) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i =
      sourceChart (source D.toR1Restart D.hasChart) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life j := by
  funext p
  have hr : sourceRecord (source C.toR1Restart C.hasChart) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p =
    sourceRecord (source D.toR1Restart D.hasChart) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life j p := by
    change (_, stopRec (rationalTime (C.q i.1)) _) = (_, stopRec (rationalTime (D.q j.1)) _)
    rw [hq]
  change Aux61SlitWX.chart C.toR1Restart C.hasChart i _ =
    Aux61SlitWX.chart D.toR1Restart D.hasChart j _
  rw [normalized_chart_eq_of_time_eq C D i j hq, hr]

/-- The normalized selected path is fixed on samples admitted by both
indices. This is equality of total functions, not only pre-contact germs. -/
theorem normalized_inPath_eq_of_time_eq (i : C.Idx) (j : D.Idx) (hq : C.q i.1 = D.q j.1)
    {p : S.Ω × HistorySpace 0 0} (hi : p ∈ C.fam.event i) (hj : p ∈ D.fam.event j) :
    inPath ((source C.toR1Restart C.hasChart).event i)
      (sourceChart (source C.toR1Restart C.hasChart) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i)
      ((source C.toR1Restart C.hasChart).path i) ((source C.toR1Restart C.hasChart).contact i) p =
    inPath ((source D.toR1Restart D.hasChart).event j)
      (sourceChart (source D.toR1Restart D.hasChart) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life j)
      ((source D.toR1Restart D.hasChart).path j) ((source D.toR1Restart D.hasChart).contact j) p := by
  have hc := normalized_sourceChart_eq_of_time_eq C D i j hq
  have ht := contact_eq_of_time_eq C D i j hq
  have hp : (source C.toR1Restart C.hasChart).path i =
      (source D.toR1Restart D.hasChart).path j := by
    change recordPath S (rationalTime (C.q i.1)) = recordPath S (rationalTime (D.q j.1))
    rw [hq]
  funext v
  change inPath (C.fam.event i) _ _ (C.fam.contact i) p v =
    inPath (D.fam.event j) _ _ (D.fam.contact j) p v
  simp only [inPath, hi, hj, true_and]
  rw [hc, ht, hp]

end InteractingSLE.Sec5.Aux61SlitWAC
