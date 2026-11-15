/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm5Final
import InteractingSLE.Spec.Sec7.R6CorTwoFinal
import InteractingSLE.Spec.Sec5.Aux61CptTop

/-! # Theorems 1.2 and 1.3 with Lemma R.6 complete: only the fibre cover remains

PROVE-T12-ASSEMBLE5, round 2 (orchestrator's order). PROVE-R6-CORNER proved R.6's three two-outer-arm faces with no
input (`R6Cor.twoFaces_proved`); its drop-in `R6Cor.r6Cert_of_leaves_corner hDy0` is `T12Asm5.r6Cert_of_leaves5` without
`hR6Same`. So the collar, Lemma R.5, Lemma R.6 and every other leaf of the T12Asm5 tops are proved, and the only inputs
left are the Prop. 5.1 fibre covers at universes `u` and `0`:

* `theorem12Statement_of_covers hDy hDy0`, `theorem13Statement_of_covers hDy0`: the tops with the covers themselves as
  the only binders;
* `theorem12Statement_assembled6` (12 binders), `theorem13Statement_assembled6` (6 binders): the covers built on ruling
  R102's route by PROVE-AUX61-CAPTURE's `Aux61Cpt.dyCover_of_finiteRestrict_accessC` (finite-buffer restriction of
  restart choices; component access `CfAccessC` on the landing part, ruling R103a), whose inputs are the binders: the
  restart choices `C`, their Borel selection `hsel`, the window data `V`, the installed words' seed heights `hSeed`, the
  per-outcome access `haccess`, and the existential capture `hcap`.

No full Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or `*_of_param` is used (R48); Cond44 is R74's
`T12Asm2.cond44Holds`.
-/
set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Wire.T12Asm6

open Sec7

/-- **Theorem 1.2 from the two fibre covers alone** (universes `u` and `0`):
`T12Asm5.theorem12Statement_assembled5_core` with the proved collar (`SideC19`), Lemma R.5 (`R5Init`) and Lemma R.6
(`R6Cor.r6Cert_of_leaves_corner`). -/
theorem theorem12Statement_of_covers
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin) :
    Exist.Theorem12Statement.{u} := by
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hCx⟩ := T12Asm3.exists_physCtx
  obtain ⟨pre, idx, m, X, hXfin, _, hm, hcol⟩ := SideC19.physCtx_exists_reliftedCollar hCx
  exact @T12Asm5.theorem12Statement_assembled5_core.{u} hDy hDy0 R5Init.wordPhase_proved R5Init.outerCont_proved
    (R6Cor.r6Cert_of_leaves_corner hDy0)
    Ωw mWord hB baseWord hP pre idx hWordb hCx.hWordGFF hCx.hWordCF hCx.hWordLife hCx.hWordleft
    hCx.hWordright hCx.hWordθ₁ hCx.hWordθ₂ hCx.hWordu₀ hCx.hWordvα hCx.hWordvL hCx.hWordβc hCx.hWordβ0
    hCx.hWordβm hCx.hWordβtr hCx.hWordηc hCx.hWordηH hCx.hWordη0 hCx.hWordηm hCx.hWordηtr hCx.hWordu
    hCx.hWordub hCx.hWord𝔥 X hXfin m hm
    (fun i => (SideC19.lateSideCollarExcWithChart_shift_iff i _ _ (m i) (X i)).1 (hcol i)) hCx.hRefWord

/-- **Theorem 1.3 from the universe-`0` fibre cover alone** (as `theorem12Statement_of_covers`). -/
theorem theorem13Statement_of_covers
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin) :
    Exist.Theorem13Statement.{u} := by
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hCx⟩ := T12Asm3.exists_physCtx
  obtain ⟨pre, idx, m, X, hXfin, _, hm, hcol⟩ := SideC19.physCtx_exists_reliftedCollar hCx
  exact @T12Asm5.theorem13Statement_assembled5_core.{u} hDy0 R5Init.wordPhase_proved R5Init.outerCont_proved
    (R6Cor.r6Cert_of_leaves_corner hDy0)
    Ωw mWord hB baseWord hP pre idx hWordb hCx.hWordGFF hCx.hWordCF hCx.hWordLife hCx.hWordleft
    hCx.hWordright hCx.hWordθ₁ hCx.hWordθ₂ hCx.hWordu₀ hCx.hWordvα hCx.hWordvL hCx.hWordβc hCx.hWordβ0
    hCx.hWordβm hCx.hWordβtr hCx.hWordηc hCx.hWordηH hCx.hWordη0 hCx.hWordηm hCx.hWordηtr hCx.hWordu
    hCx.hWordub hCx.hWord𝔥 X hXfin m hm
    (fun i => (SideC19.lateSideCollarExcWithChart_shift_iff i _ _ (m i) (X i)).1 (hcol i))

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap Sec5.Aux61Cpt in
/-- **Theorem 1.2 with Lemma R.6 complete** (PROVE-T12-ASSEMBLE5, round 2). Every leaf except the fibre cover is proved.
Binders: the fibre cover's inputs on R102's route (CAPTURE's `Aux61Cpt.dyCover_of_finiteRestrict_accessC`) at universe
`u` (`C … hcap`) and `0` (`C₀ … hcap₀`): restart choices and their Borel selection, `WindowData` of the finite-buffer
restriction, the installed words' seed heights, the per-outcome own-collar / component counterflow access, and the
existential capture. -/
theorem theorem12Statement_assembled6
    (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)
    (hSeed : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
          sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b ∨
          CfAccessC S (Aux61Cmp.normSource (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart) i p b)
    (hcap : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C S)) (finiteChoicesOf (C S)).hasChart))) i p)
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
            i p b ∨
          CfAccessC S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart))) i p) :
    Exist.Theorem12Statement.{u} :=
  theorem12Statement_of_covers (dyCover_of_finiteRestrict_accessC C hsel V hSeed haccess hcap)
    (dyCover_of_finiteRestrict_accessC C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀)

open Sec5 Sec5.Aux61SlitW Sec5.Aux61R1C Sec5.Aux61SlitWX Sec5.Aux61WndCap Sec5.Aux61Cpt in
/-- **Theorem 1.3 with Lemma R.6 complete** (PROVE-T12-ASSEMBLE5, round 2): as `theorem12Statement_assembled6`, with
the fibre cover's inputs only at universe `0`. -/
theorem theorem13Statement_assembled6
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S)
    (hsel₀ : ∀ S, ∀ i, MeasurableSet ((C₀ S).selected i))
    (V₀ : ∀ S : SourceSetting.{0}, WindowData (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
    (hSeed₀ : ∀ S : SourceSetting.{0}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C₀ S)).data i).bR 0 =
          -sleLambda ((finiteRestart (C₀ S)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C₀ S)).data i).bR 0 =
          sleLambda ((finiteRestart (C₀ S)).data i).κ)
    (haccess₀ : ∀ S : SourceSetting.{0}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).Z i p ∈
        (S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).B i →
      ∀ b ∈ ((S.marksData (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart)
            i p b ∨
          CfAccessC S (Aux61Cmp.normSource (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart) i p b)
    (hcap₀ : ∀ S : SourceSetting.{0}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (Aux61Asm2.cutSource S (source (finiteRestart (C₀ S)) (finiteChoicesOf (C₀ S)).hasChart))) i p) :
    Exist.Theorem13Statement.{u} :=
  theorem13Statement_of_covers (dyCover_of_finiteRestrict_accessC C₀ hsel₀ V₀ hSeed₀ haccess₀ hcap₀)

end InteractingSLE.Wire.T12Asm6
