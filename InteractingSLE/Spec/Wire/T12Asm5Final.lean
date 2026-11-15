/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm5Core
import InteractingSLE.Spec.Wire.T12Asm5Inputs
import InteractingSLE.Spec.Sec7.SideC19Top

/-! # Theorems 1.2 and 1.3 re-assembled on the evening's results: the final binder list

PROVE-T12-ASSEMBLE5. The tops `T12Asm5.theorem12Statement_assembled5_core` / `theorem13Statement_assembled5_core` with

* the physical word context from `T12Ctx.exists_physical_context` (`T12Asm3.exists_physCtx`);
* **the late-side collar: PROVED** — PROVE-SIDE-COLLAR2's `SideC19.physCtx_exists_reliftedCollar` (ruling R100: current
  and reference charts jointly relifted by a walls-measurable integer, offset `0`), restated capacity-first by
  `SideC19.lateSideCollarExcWithChart_shift_iff`; the tops consume the relifted chart (`T12Asm5Side`, `T12Asm5Exc`,
  `T12Asm5ExcSide`, `T12Asm5Core`);
* **Lemma R.5 on every pocket: PROVED** (PROVE-R5-INIT's `R5Init.wordPhase_proved`, `R5Init.outerCont_proved`,
  `R5Init.hOuterCover_proved`);
* **R.6's mixed faces: PROVED** (`T12Asm5.mixedFaces_proved`, PROVE-R6-CORNER);
* R.6's two-outer faces from PROVE-R6-TWO's common-time geometry: binder `hR6Same`
  (`R6Tr.R6SameTimeTwo{,Inf,InfInf}Remaining`);
* the fibre covers `hDy`/`hDy0` on ruling R102's route (`T12Asm5.dyCover_of_finiteRestrict_access`): restart choices
  `C` with Borel selection `hsel`, restricted to their finite-buffer pieces, `WindowData` `V`, the installed words' seed
  heights `hSeed`, the R101/R103 collar access `haccess` and the existential capture `hcap`, at universes `u` and `0`.

No full Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or `*_of_param` is used (R48); Cond44 is R74's
`T12Asm2.cond44Holds`.
-/
set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Wire.T12Asm5

open Sec7

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap in
/-- **Theorem 1.2 re-assembled on the evening's results** (PROVE-T12-ASSEMBLE5). The collar, Lemma R.5 on every
pocket and R.6's mixed faces are proved. Binders: the fibre cover's inputs at universes `u` (`C … hcap`) and `0`
(`C₀ … hcap₀`) on R102's route (restart choices and their Borel selection, `WindowData` of the finite-buffer
restriction, the installed words' seed heights, the collar access, the existential capture); R.6's common-time
two-outer geometry `hR6Same`. -/
theorem theorem12Statement_assembled5
    (C : ∀ S : SourceSetting.{u}, RestartChoices S)
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
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart))) i p)
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S))
      (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b ∨
          Aux61Cmp.CfAccess S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart))) i p)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    Exist.Theorem12Statement.{u} := by
  have hDy := dyCover_of_finiteRestrict_access C hsel V hSeed haccess hcap
  have hDy0 := dyCover_of_finiteRestrict_access C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hCx⟩ := T12Asm3.exists_physCtx
  obtain ⟨pre, idx, m, X, hXfin, _, hm, hcol⟩ := SideC19.physCtx_exists_reliftedCollar hCx
  exact @theorem12Statement_assembled5_core.{u} hDy hDy0 R5Init.wordPhase_proved R5Init.outerCont_proved
    (r6Cert_of_leaves5 hDy0 hR6Same)
    Ωw mWord hB baseWord hP pre idx hWordb hCx.hWordGFF hCx.hWordCF hCx.hWordLife hCx.hWordleft
    hCx.hWordright hCx.hWordθ₁ hCx.hWordθ₂ hCx.hWordu₀ hCx.hWordvα hCx.hWordvL hCx.hWordβc hCx.hWordβ0
    hCx.hWordβm hCx.hWordβtr hCx.hWordηc hCx.hWordηH hCx.hWordη0 hCx.hWordηm hCx.hWordηtr hCx.hWordu
    hCx.hWordub hCx.hWord𝔥 X hXfin m hm
    (fun i => (SideC19.lateSideCollarExcWithChart_shift_iff i _ _ (m i) (X i)).1 (hcol i)) hCx.hRefWord

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap in
/-- **Theorem 1.3 re-assembled on the evening's results** (PROVE-T12-ASSEMBLE5): as
`theorem12Statement_assembled5`, with the fibre cover's inputs only at universe `0`. -/
theorem theorem13Statement_assembled5
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S))
      (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b ∨
          Aux61Cmp.CfAccess S (Aux61Cmp.normSource (finiteRestart (C₀ S))
            (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S))
          (Aux61SlitWAC.restrictChoices (C₀ S) (finiteRestrict (C₀ S))).hasChart))) i p)
    (hR6Same : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tr.R6SameTimeTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tr.R6SameTimeTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    Exist.Theorem13Statement.{u} := by
  have hDy0 := dyCover_of_finiteRestrict_access C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hCx⟩ := T12Asm3.exists_physCtx
  obtain ⟨pre, idx, m, X, hXfin, _, hm, hcol⟩ := SideC19.physCtx_exists_reliftedCollar hCx
  exact @theorem13Statement_assembled5_core.{u} hDy0 R5Init.wordPhase_proved R5Init.outerCont_proved
    (r6Cert_of_leaves5 hDy0 hR6Same)
    Ωw mWord hB baseWord hP pre idx hWordb hCx.hWordGFF hCx.hWordCF hCx.hWordLife hCx.hWordleft
    hCx.hWordright hCx.hWordθ₁ hCx.hWordθ₂ hCx.hWordu₀ hCx.hWordvα hCx.hWordvL hCx.hWordβc hCx.hWordβ0
    hCx.hWordβm hCx.hWordβtr hCx.hWordηc hCx.hWordηH hCx.hWordη0 hCx.hWordηm hCx.hWordηtr hCx.hWordu
    hCx.hWordub hCx.hWord𝔥 X hXfin m hm
    (fun i => (SideC19.lateSideCollarExcWithChart_shift_iff i _ _ (m i) (X i)).1 (hcol i))

end InteractingSLE.Wire.T12Asm5
