/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow18Capture
import InteractingSLE.Spec.Sec5.Aux61GWindow17CompareLink
import InteractingSLE.Spec.Sec5.Aux61CmpCfGerm

/-! # The current fibre-cover interface with GLUEINST's inputs discharged

WindowData and existential capture are unconditional for this exact
finite-restricted normalized source, and O₀ is bounded. Component
comparisons remain COMPARE's explicit input. Its landed collar theorem
applies with the seed heights and every other prerequisite discharged.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow18
open Aux61SlitW Aux61R1C Aux61Asm2 LawUnique
universe u

/-- Both canonical seed heights for the actual installed reference word. -/
theorem family_seed_heights (S : SourceSetting.{u}) (i : (choices S).Idx) :
    PiecewiseConstantBoundaryData.leftLim ((family S).data i).bR 0 =
        -sleLambda ((family S).data i).κ ∧
      PiecewiseConstantBoundaryData.rightLim ((family S).data i).bR 0 =
        sleLambda ((family S).data i).κ :=
  Aux61GWindow17.intervalWord_seed_heights S i.1.2.1

/-- COMPARE's component constructor specialized to the corrected bounded
window family. The physical collar-access cover remains its explicit
geometric input; no access or height matching is asserted here. -/
def componentComparisons_of_collars (S : SourceSetting.{u})
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (cutSource S (family S))).Z i p ∈
        (S.marksData (cutSource S (family S))).B i →
      ∀ b ∈ ((S.marksData (cutSource S (family S))).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (cutSource S (family S)) i p b ∨
          Aux61Cmp.CfAccess S (cutSource S (family S)) i p b) :
    ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (family S))) i :=
  Aux61Cmp.normalizedComparisons (finiteChoices S).toR1Restart (finiteChoices S).hasChart
    (Aux61SlitWZ.readers (finiteChoices S) (finiteChoices_selected_measurable S))
    (Aux61SlitWY.ownTipForwardLimit S) (windows S)
    (Aux61WndCap.physicalExit_finiteRestrict (choices S) (choices_selected_measurable S))
    (fun i => (family_seed_heights S i).1) (fun i => (family_seed_heights S i).2) haccess

/-- The exact current fibre leaf through WINDOW's finite-restriction
route. Only COMPARE's component comparisons remain as an input. -/
theorem dyCover_of_component_comparisons
    (C : ∀ S : SourceSetting.{u}, ∀ i, Aux61GPrime.ZeroComparisons
      (S.marksData (cutSource S (family S))) i) :
    Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  Aux61WndCap.dyCover_of_finiteRestrict_capture choices choices_selected_measurable
    windows C family_completed_cover_cut

/-- The two universes used by the theorem tops, with the same remaining
component-comparison input at each universe. -/
theorem dyCover_of_component_comparisons_both
    (C : ∀ S : SourceSetting.{u}, ∀ i, Aux61GPrime.ZeroComparisons
      (S.marksData (cutSource S (family S))) i)
    (C₀ : ∀ S : SourceSetting.{0}, ∀ i, Aux61GPrime.ZeroComparisons
      (S.marksData (cutSource S (family S))) i) :
    Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
    Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  ⟨dyCover_of_component_comparisons C, dyCover_of_component_comparisons C₀⟩

end InteractingSLE.Sec5.Aux61GWindow18
