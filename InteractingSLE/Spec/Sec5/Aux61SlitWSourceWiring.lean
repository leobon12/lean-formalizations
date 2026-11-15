/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceGlued
import InteractingSLE.Spec.Sec5.Aux61SlitWOn

/-! # The concrete source assembly and its physical slit wiring -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open QuantumZipper (chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW.SourceSetting
open Aux61Marks Aux61Asm Aux61ChLoc Aux61GInst Cond44Ref
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- The source marked sets already use the current live version. -/
theorem liveSets_eq_baseSets (i : F.ι) (q : ℝ≥0) :
    (S.marksData F).liveSets i q = (S.marksData F).baseSets i q := by
  change liveSet (liveEv (sourceHistory F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      (sourceHistoryEvent F i) (sourceCode F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField i) q)
    (liveSet _ _) = liveSet _ _
  exact Aux61Nest.liveSet_idem _ _

/-- The source assembly has physical comparison wiring built from its
null-completed capacity rules, including all live comparison unions. -/
theorem exists_wiring (I : S.Inputs F) :
    ∃ W : SlitWiringData ((S.marksData F).toAsmData (S.marksFacts F I)),
      SlitWiring S.μ ((S.marksData F).toAsmData (S.marksFacts F I)) W := by
  apply exists_slitWiring_of_null_capacityRules S.own.coupling S.κ_pos S.own_infinite S.theta_bounds
    S.counterflow S.theta_field_law S.kernel_law
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
    S.theta_measure (S.marksData F) (S.marksFacts F I)
    F.chart I.restart.chart_measurable F.start (rationalTime S.s) rationalTime
    (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR)
    (fun _ _ => Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) _ _)
    rfl rfl rfl rfl I.restart.kappa (fun _ _ => rfl) _
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  intro i q
  rw [S.liveSets_eq_baseSets F i q]
  exact S.regular_contains F I i q

/-- The physical comparison data, with no abstract wiring supplied. -/
def wiring (I : S.Inputs F) : SlitWiringData ((S.marksData F).toAsmData (S.marksFacts F I)) :=
  Classical.choose (S.exists_wiring F I)

/-- All clauses of `SlitWiring` for the concrete physical source. -/
theorem wiring_facts (I : S.Inputs F) :
    SlitWiring S.μ ((S.marksData F).toAsmData (S.marksFacts F I)) (S.wiring F I) :=
  Classical.choose_spec (S.exists_wiring F I)

end InteractingSLE.Sec5.Aux61SlitW.SourceSetting
