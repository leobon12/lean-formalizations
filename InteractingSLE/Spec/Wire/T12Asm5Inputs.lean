/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm4Inputs
import InteractingSLE.Spec.Sec7.R5InitProved
import InteractingSLE.Spec.Sec7.R6TrTwo
import InteractingSLE.Spec.Sec7.R6TrTwoInf
import InteractingSLE.Spec.Sec7.R6TrTwoInfInf
import InteractingSLE.Spec.Sec7.R6CorFinal
import InteractingSLE.Spec.Sec5.Aux61WndCapNorm
import InteractingSLE.Spec.Sec5.Aux61CmpCfGerm

/-! # The leaves of Theorems 1.2–1.3 on the evening's results

PROVE-T12-ASSEMBLE5. The R.5, R.6 and fibre-cover binders of `T12Asm5.theorem12Statement_assembled5_core`, from the
latest committed reductions:

* **Lemma R.5: PROVED on every pocket** (PROVE-R5-INIT, `Spec/Sec7/R5InitProved`): extremal pockets
  (`R5Init.wordPhase_proved`, `R5Init.phaseWordM_proved`, closing ASSEMBLE4's `hWordInit`) and outer pockets
  (`R5Init.hOuterCover_proved`, `R5Init.outerCont_proved`, closing ASSEMBLE4's `hOuterCover`); here only the margin
  form `phaseWordM_margin` of ASSEMBLE4's generic layer;
* **R.6, mixed faces: PROVED.** PROVE-R6-CORNER's deterministic route (seed corner included):
  `R6Cor.r6FaceSMixed{,Inf,InfInf}Remaining` close ASSEMBLE4's inner-hit binder `hR6Hit` (`mixedFaces_proved`);
* **R.6, two-outer faces**: PROVE-R6-TWO's common-time incident-face geometry `R6Tr.R6SameTimeTwo{,Inf,InfInf}Remaining`
  (seed corners permitted), which replaces the retired landing-patch route (`twoFaces_of_sameTime`);
* **the fibre cover** (ruling R102): PROVE-AUX61-WINDOW's `Aux61WndCap.dyCover_of_finiteRestrict_capture` (restart
  data, readers, `OwnTipForwardLimit` and `PhysicalExit` discharged on the finite-buffer restriction) with the
  component comparisons from PROVE-AUX61-COMPARE's `Aux61Cmp.normalizedComparisons` (the seed heights of the installed
  words and the R101 collar-access hypothesis remain): `dyCover_of_finiteRestrict_access`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`
(Cond44 is R74's `T12Asm2.cond44Holds`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Wire.T12Asm5

open Sec7 Sec7.R6Safe

universe u

/-! ### Lemma R.5 -/

/-- **R.5 up to phase on the extremal pockets at margins `πχ ≤ c`, `0 ≤ c'`** (PROVE-R5-INIT's
`R5Init.phaseWordM_proved` in the form of ASSEMBLE4's generic layer, `T12Asm4.r6Cert_ofW`'s `hWordM`). -/
theorem phaseWordM_margin :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c' :=
  fun _ hk4 _ _ _ _ _ _ _ hc hc' => R5Init.phaseWordM_proved hk4 ((T12Asm2.margin_nonneg hk4).trans hc) hc'

/-! ### R.6 -/

/-- **R.6's three mixed faces, PROVED** (PROVE-R6-CORNER, `R6Cor.r6FaceSMixed{,Inf,InfInf}Remaining`), in the form of
ASSEMBLE4's generic layer (`T12Asm4.r6Cert_ofW`'s `hR6Mixed`). -/
theorem mixedFaces_proved :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6FaceSMixedInfInfRemaining.{0} k rL rR c 0 :=
  fun _ _ _ _ _ _ _ _ => ⟨R6Cor.r6FaceSMixedRemaining, R6Cor.r6FaceSMixedInfRemaining,
    R6Cor.r6FaceSMixedInfInfRemaining⟩

/-- **R.6's three two-outer faces from PROVE-R6-TWO's common-time incident-face geometry**
(`R6Tr.r6FaceQTwo*Remaining_of_sameTime`; seed corners permitted). -/
theorem twoFaces_of_sameTime
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := by
  intro k hk4 rL rR hL hR hbad
  obtain ⟨h1, h2, h3⟩ := hR6Same k hk4 rL rR hL hR hbad
  exact ⟨R6Tr.r6FaceQTwoRemaining_of_sameTime h1, R6Tr.r6FaceQTwoInfRemaining_of_sameTime h2,
    R6Tr.r6FaceQTwoInfInfRemaining_of_sameTime h3⟩

/-- **Theorem 1.2's binder `hR6Cert` from the leaves**: Lemma R.5 and the mixed faces (proved) and the common-time
two-outer geometry. -/
theorem r6Cert_of_leaves5
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → R6Rel.R6NestCertRemaining.{0} k rL rR :=
  T12Asm4.r6Cert_ofW phaseWordM_margin (T12Asm4.outerContM_of_cover R5Init.hOuterCover_proved) hDy0
    mixedFaces_proved (twoFaces_of_sameTime hR6Same)

/-! ### The fibre cover (ruling R102) -/

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap in
/-- **The fibre cover at one universe on R102's route, with `PhysicalExit` and the component comparisons
discharged.** Restart choices `C` with Borel selection, restricted to their finite-buffer record pieces
(`Aux61WndCap.finiteRestrict`): PROVE-AUX61-WINDOW's `dyCover_of_finiteRestrict_capture` discharges the restart data,
readers, `OwnTipForwardLimit` and `PhysicalExit`; its component comparisons are PROVE-AUX61-COMPARE's
`Aux61Cmp.normalizedComparisons`, from the seed heights `hSeed` of the installed words and the R101 collar-access
hypothesis `haccess`. Remaining: GLUEINST's `WindowData` and existential capture, COMPARE's access, the seed heights
and the Borel selection. -/
theorem dyCover_of_finiteRestrict_access (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S))
      (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)
    (hSeed : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
          sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C S))
            (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart) i p b ∨
          Aux61Cmp.CfAccess S (Aux61Cmp.normSource (finiteRestart (C S))
            (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart) i p b)
    (hcap : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart))) i p) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_finiteRestrict_capture C hsel V
    (fun S => Aux61Cmp.normalizedComparisons (finiteRestart (C S))
      (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart
      (Aux61SlitWZ.readers _ (selected_measurable_finiteRestrict (C S) (hsel S)))
      (Aux61SlitWY.ownTipForwardLimit S) (V S) (physicalExit_finiteRestrict (C S) (hsel S))
      (fun i => (hSeed S i).1) (fun i => (hSeed S i).2) (haccess S)) hcap

end InteractingSLE.Wire.T12Asm5
