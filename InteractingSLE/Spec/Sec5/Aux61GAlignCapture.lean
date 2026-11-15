/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceWiring
import InteractingSLE.Spec.Sec5.Aux61GRecCapture

/-! # Source wiring and exclusion using only pointwise future capture

These theorems do not take `SourceSetting.Inputs`, its history cover, or its
completed-window field. The countable future capture is an explicit named
geometric input. The physical wiring is constructed from the actual source
capacity rules rather than supplied separately.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61Asm Aux61FibData
open Aux61ULoc LawUnique GlueCond Cond44Ref
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- Build physical source wiring independently of all future-capture
properties. The MARKS facts and union containment are the required physical
inputs; the selected-event cover is not needed to construct wiring. -/
theorem exists_source_wiring_of_marks
    (hF : MarksFacts S.μ (S.marksData F))
    (hchart : ∀ i, IsMeasChart (F.chart i))
    (hκ : ∀ i, (F.data i).κ = S.κ)
    (hcontains : ∀ i q, ∀ᵐ p ∂S.μ,
      unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
        (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
        (fun p => capacityRule (F.chart i) (F.start i) q
          (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
          (S.marksData F).baseSets i q p) :
    ∃ W : SlitWiringData ((S.marksData F).toAsmData hF),
      SlitWiring S.μ ((S.marksData F).toAsmData hF) W := by
  apply exists_slitWiring_of_null_capacityRules S.own.coupling S.κ_pos S.own_infinite S.theta_bounds
    S.counterflow S.theta_field_law S.kernel_law
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
    S.theta_measure (S.marksData F) hF F.chart hchart F.start (rationalTime S.s) rationalTime
    (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR)
    (fun _ _ => Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) _ _)
    rfl rfl rfl rfl hκ (fun _ _ => rfl) _
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  intro i q
  rw [S.liveSets_eq_baseSets F i q]
  exact hcontains i q

/-- The concrete source window event is null from pointwise countable
completed capture. This route assumes no future-capture assertion for every
selected past event, and no independent slit-wiring or local-cover input. -/
theorem ae_not_source_of_completed_capture
    (hF : MarksFacts S.μ (S.marksData F))
    (hchart : ∀ i, IsMeasChart (F.chart i))
    (hκ : ∀ i, (F.data i).κ = S.κ)
    (hcontains : ∀ i q, ∀ᵐ p ∂S.μ,
      unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
        (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
        (fun p => capacityRule (F.chart i) (F.start i) q
          (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
          (S.marksData F).baseSets i q p)
    (hneg : Aux61Cov.R5NegStatement.{u})
    (hcaptured_cover : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture (S.marksData F) i p) :
    ∀ᵐ p ∂S.μ, ¬ S.windowEvent p := by
  obtain ⟨W, hW⟩ := exists_source_wiring_of_marks S F hF hchart hκ hcontains
  exact Aux61GRec.ae_not_of_marks_capture_cover hF W hW hneg hcaptured_cover

end InteractingSLE.Sec5.Aux61GAlign
