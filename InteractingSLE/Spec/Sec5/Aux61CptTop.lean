/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptGerm
import InteractingSLE.Spec.Sec5.Aux61WndCapNorm

/-!
# The fibre cover on the finite-buffer route from component accesses

Packet PROVE-AUX61-CAPTURE (ruling R103). `Aux61WndCap.dyCover_of_finiteRestrict_capture` leaves the window data, the
component comparisons and the existential capture of the finite-buffer restriction of arbitrary restart choices. Here
the comparisons are discharged by `Aux61Cpt.normalizedComparisonsC` from

* the seed heights `∓λ` of the installed words (`hleft`, `hright`), and
* the per-outcome access hypothesis in **component** form (`haccess`): almost surely on each selected record every
  window point is an own collar point or a component counterflow access (`CfAccessC`, no prime-end preimage clause).

`dyCover_of_componentAccess` is the fibre leaf at a universe `u`; it is universe-polymorphic, so the Theorem 1.2–1.3
tops instantiate it at `u` and at `0`.
Conditional helpers with distinct names: the access hypothesis is the per-outcome selection of ruling R103 (it is a
property of the chosen restart family, not a source premise), and nothing here replaces a source theorem.
R48: no Theorem 1.2/1.3 input; R77: no post-contact kernel.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61SlitWX Aux61WndCap Aux61Cmp LawUnique
universe u

/-- The restricted choices of the finite-buffer route. -/
abbrev finiteChoicesOf {S : SourceSetting.{u}} (C : RestartChoices S) : RestartChoices S :=
  Aux61SlitWAC.restrictChoices C (finiteRestrict C)

/-- **The fibre leaf from component accesses** on the finite-buffer restrictions of arbitrary restart choices: the
remaining inputs are the window data, the installed seed heights, the component access on the selected records, and
the existential capture. -/
theorem dyCover_of_componentAccess (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)
    (hleft : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
        -sleLambda ((finiteRestart (C S)).data i).κ)
    (hright : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
        sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).Z i p ∈
        (S.marksData (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).data i).O₀,
        OwnCollarPoint S (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b ∨
          CfAccessC S (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b)
    (hcaptured_cover : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (cutSource S (source (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart))) i p) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_finiteRestrict_capture C hsel V
    (fun S => normalizedComparisonsC (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart
      (Aux61SlitWZ.readers _ (selected_measurable_finiteRestrict (C S) (hsel S)))
      (Aux61SlitWY.ownTipForwardLimit S) (V S) (physicalExit_finiteRestrict (C S) (hsel S))
      (hleft S) (hright S) (haccess S))
    hcaptured_cover

/-- **The same fibre leaf in the binder shape of `Wire.T12Asm5.theorem12Statement_assembled5`** (seed heights as one
conjunction), with the component access `CfAccessC` of ruling R103a in place of `CfAccess`. -/
theorem dyCover_of_finiteRestrict_accessC (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)
    (hSeed : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
          sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).Z i p ∈
        (S.marksData (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).data i).O₀,
        OwnCollarPoint S (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b ∨
          CfAccessC S (normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b)
    (hcap : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (cutSource S (source (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart))) i p) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_componentAccess C hsel V (fun S i => (hSeed S i).1) (fun S i => (hSeed S i).2) haccess hcap

end InteractingSLE.Sec5.Aux61Cpt
