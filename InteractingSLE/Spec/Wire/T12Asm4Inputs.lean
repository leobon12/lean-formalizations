/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm3Inputs
import InteractingSLE.Spec.Sec7.R5FreshInit
import InteractingSLE.Spec.Sec7.R6FdHit
import InteractingSLE.Spec.Sec7.R6FdWireInf
import InteractingSLE.Spec.Sec7.R6FdInfInf
import InteractingSLE.Spec.Sec7.R6FcWire
import InteractingSLE.Spec.Sec7.R6FcWireInf
import InteractingSLE.Spec.Sec7.R6FcWireInfInf
import InteractingSLE.Spec.Sec7.R6TnTwo
import InteractingSLE.Spec.Sec7.R6TnTwoInf
import InteractingSLE.Spec.Sec7.R6TnTwoInfInf

/-! # The R.5 and R.6 leaves of Theorems 1.2–1.3 on the afternoon's reductions

PROVE-T12-ASSEMBLE4. The three R.5/R.6 binders of `T12Asm.theorem12Statement_assembled` (`hWordPhase`, `hOuterCont`,
`hR6Cert`), in two layers.

**Generic layer** (`*W`): `hR6Cert` from R.5 on the extremal pockets up to phase at every margin (`hWordM`), the
outer continuity at every margin (`hOuterM`), and T12Asm3's mixed and two-outer face forms. This is
`T12Asm3.r6Cert_of_faces` with its split-cover binder replaced by the phase words it produces.

**Leaves** (the open inputs):

* extremal R.5: PROVE-R5-FRESHTIP's initial-heights input `R5Fresh.R7SplitRemainingInit` (only `R7InitialHeights`
  per test; owner PROVE-R5-INIT), through `R5Fresh.r7PhaseWordRemaining_of_splitInit` with Aux. lemma 7 at `k` from
  the proved clearance Part A (`T12Asm3.aux7`) — the non-circular no-return; never `r7R5RemainingOn_of_splitNR`;
* outer R.5: PROVE-R5-OUTER's incident-component form `R5Out.R7OuterRelativeCoverMRemaining` (ruling R88; R5-OUTER
  has no committed reduction of it yet);
* R.6 mixed faces: PROVE-R6-FACE3's inner-hit inputs `R6Fd.R6InnerSharedHitMixed{,InfInf}Remaining`
  (`R6Fd.r6NonCornerMixed*Remaining_of_innerHit`, then PROVE-R6-FACE2's `R6Fc.r6FaceSMixed*Remaining_of_nonCorner`);
* R.6 two-outer faces: PROVE-R6-TWO's landing patches `R6Tn.R6LandingPatchTwo{,Inf,InfInf}Remaining`
  (`R6Tn.r6FaceQTwo*Remaining_of_landingPatch`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`
(Cond44 is R74's `T12Asm2.cond44Holds`).
-/

set_option autoImplicit false
noncomputable section

open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Wire.T12Asm4

open Sec7 Sec7.R6Safe Sec7.R6Nest Sec7.R6Fin Sec7.R7Leaves Sec7.R7Outer

/-! ### The generic layer -/

/-- **R.6's certificate on a mixed configuration** (`R6Safe.r6NestCertRemaining_of_core_safe`) from the inner
pocket's R.5 word at its margins and the three mixed faces (`T12Asm3.r6Cert_mixed` with the phase words given). -/
theorem r6Cert_mixedW
    (hWordM : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c')
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hR6Mixed : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6FaceSMixedInfInfRemaining.{0} k rL rR c 0)
    {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    R6Rel.R6NestCertRemaining.{0} k rL rR := by
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement T12Asm3.partA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 T12Asm3.partA
  have h51 := Beacon.prop51 T12Asm3.partA hDy0
  have hout : k / 2 - 4 < max rL rR := by
    rcases hmix with h | h
    · exact lt_max_of_lt_left h.1
    · exact lt_max_of_lt_right h.2
  have hword : PhaseCont.R7PhaseWordRemaining.{0} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) :=
    hWordM k hk4 _ _ (neg_two_lt_innerRight_weight hk4 hL) (neg_two_lt_innerLeft_weight hk4 hR)
      (T12Asm3.max_inner_eq hout) _ _ (le_add_of_nonneg_right (sub_nonneg.2 (r7A_innerLeft_le hk4 rR)))
      (by rw [zero_add]; exact sub_nonneg.2 (r7B_innerRight_le hk4 rL))
  obtain ⟨hS, hSI, hSII⟩ := hR6Mixed k hk4 rL rR hL hR _ le_rfl
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement T12Asm3.partA h1 h2
  have hc1 : R6FaceQMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6FaceQMixedRemaining_of_faceS hS
  have hc2 : R6FacePMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6FacePMixedRemaining_of_faceQ hc1
  have hc3 : R6FaceMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6FaceMixedRemaining_of_faceP hc2
  have hc4 : R6GeomCoreMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6GeomCoreMixedRemaining_of_face hc3
  exact @r6NestCertRemaining_of_core_safe.{0} k rL rR h411 h51 h47 h47T
    (T12Asm3.aux7 k hk4) T12Asm2.cond44Holds hword hc4
    (r6GeomCoreMixedInfRemaining_of_face (r6FaceMixedInfRemaining_of_faceP
      (r6FacePMixedInfRemaining_of_faceQ (r6FaceQMixedInfRemaining_of_faceS hSI))))
    (r6GeomCoreMixedInfInfRemaining_of_face (r6FaceMixedInfInfRemaining_of_faceP
      (r6FacePMixedInfInfRemaining_of_faceQ (r6FaceQMixedInfInfRemaining_of_faceS hSII))))
    hk4 hL hR hmix

/-- **R.6's two-outer-arm inputs** `TwoOuterFaceSInputs` from the phase words and outer continuity at `V`'s margins,
`V`'s mixed faces and the three two-outer faces (`T12Asm3.twoOuterFaceSInputs_of_inputs` with the R.5 outputs
given). -/
theorem twoOuterFaceSInputsW
    (hWordM : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c')
    (hOuterM : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R6Rel.R7OuterPhaseContMRemaining.{0} k rL rR c c')
    (hR6Mixed : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6FaceSMixedInfInfRemaining.{0} k rL rR c 0)
    (hR6Two : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR) (hbad : ¬ (rL < k - 6 ∧ rR < k - 6)) :
    TwoOuterFaceSInputs.{0} k rL rR := by
  have hd : -2 < k / 2 - 4 := by linarith
  have hcV := pi_chi_le_leftExt_margin hk4 le_rfl hdR
  obtain ⟨hS, hSI, hSII⟩ := hR6Mixed k hk4 rL (k / 2 - 4) hL hd _ hcV
  obtain ⟨hT, hTI, hTII⟩ := hR6Two k hk4 rL rR hL hR hbad
  refine ⟨?_, hS, hSI, hSII, ?_, hT, hTI, hTII⟩
  · exact hWordM k hk4 _ _ (neg_two_lt_innerRight_weight hk4 hL) (neg_two_lt_innerLeft_weight hk4 hd)
      (T12Asm3.max_innerV_eq hdL) _ _ (le_add_of_le_of_nonneg hcV (sub_nonneg.2 (r7A_innerLeft_le hk4 _)))
      (by rw [zero_add]; exact sub_nonneg.2 (r7B_innerRight_le hk4 rL))
  · exact hOuterM k hk4 rL (k / 2 - 4) hL hd (lt_max_of_lt_left hdL) _ 0 hcV le_rfl

/-- **Theorem 1.2's binder `hR6Cert`** from the generic R.5 outputs and R.6's face descriptions (mixed configurations
by `r6Cert_mixedW`, two outer arms by `R6Safe.r6NestCertRemaining_two` on `twoOuterFaceSInputsW`). -/
theorem r6Cert_ofW
    (hWordM : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c')
    (hOuterM : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R6Rel.R7OuterPhaseContMRemaining.{0} k rL rR c c')
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hR6Mixed : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6FaceSMixedInfInfRemaining.{0} k rL rR c 0)
    (hR6Two : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → R6Rel.R6NestCertRemaining.{0} k rL rR := by
  intro k hk4 rL rR hL hR _ hbad
  rcases mixed_or_twoOuter hk4 hbad with hmix | ⟨hdL, hdR⟩
  · exact r6Cert_mixedW hWordM hDy0 hR6Mixed hk4 hL hR hmix
  · have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement T12Asm3.partA
    have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 T12Asm3.partA
    have h51 : Sec5.Cond44Ref.Prop51QStatement.{0} := Beacon.prop51 T12Asm3.partA hDy0
    have hin : TwoOuterFaceSInputs.{0} k rL rR :=
      twoOuterFaceSInputsW hWordM hOuterM hR6Mixed hR6Two hk4 hL hR hdL hdR hbad
    exact @r6NestCertRemaining_two.{0} k rL rR h411 h51 h47
      (fun θ h1 h2 => late_lemma47QHitTStatement T12Asm3.partA h1 h2) (T12Asm3.aux7 k hk4) T12Asm2.cond44Holds
      T12Asm3.partA hk4 hL hdL hdR (twoOuterInputs_of_face.{0} (twoOuterFaceInputs_of_faceP.{0}
        (twoOuterFacePInputs_of_faceQFull.{0} (twoOuterFaceQFullInputs_of_faceS.{0} hin))))

/-! ### The leaves -/

/-- **R.5 up to phase on the extremal pockets at margins `πχ ≤ c`, `0 ≤ c'` from the initial heights**
(`R5Fresh.r7PhaseWordRemaining_of_splitInit`; Aux. lemma 7 at `k` from the proved clearance Part A). -/
theorem phaseWordM_of_init
    (hWordInit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Fresh.R7SplitRemainingInit.{0} k rL rR c c') :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c' :=
  fun k hk4 rL rR hL hR hmax c c' hc hc' => R5Fresh.r7PhaseWordRemaining_of_splitInit hk4
    ((T12Asm2.margin_nonneg hk4).trans hc) hc' (T12Asm3.aux7 k hk4) (hWordInit k hk4 rL rR hL hR hmax c c' hc hc')

/-- **Lemma R.5 on the extremal pockets (conditioned clauses) at margins `πχ ≤ c`, `0 ≤ c'` from the initial
heights** (`R5Fresh.r7R5RemainingOn_of_splitInit`; recorded for consumers of `R5Enl.R7R5RemainingOn`). -/
theorem r5RemainingOn_of_init
    (hWordInit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Fresh.R7SplitRemainingInit.{0} k rL rR c c') :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Enl.R7R5RemainingOn.{0} k rL rR c c' :=
  fun k hk4 rL rR hL hR hmax c c' hc hc' => R5Fresh.r7R5RemainingOn_of_splitInit hk4
    ((T12Asm2.margin_nonneg hk4).trans hc) hc' (T12Asm3.aux7 k hk4) (hWordInit k hk4 rL rR hL hR hmax c c' hc hc')

/-- **Theorem 1.2's binder `hWordPhase`** from the initial heights. -/
theorem wordPhase_of_init
    (hWordInit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Fresh.R7SplitRemainingInit.{0} k rL rR c c') :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
  fun k hk4 rL rR hL hR hmax => phaseWordM_of_init hWordInit k hk4 rL rR hL hR hmax _ _ le_rfl le_rfl

/-- **The outer continuity at margins `πχ ≤ c`, `0 ≤ c'`** from R5-OUTER's incident-component clauses
(`R5Out.r7OuterPhaseContMRemaining_of_relativeCover`). -/
theorem outerContM_of_cover
    (hOuterCover : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Out.R7OuterRelativeCoverMRemaining.{0} k rL rR c c') :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R6Rel.R7OuterPhaseContMRemaining.{0} k rL rR c c' :=
  fun k hk4 rL rR hL hR hmax c c' hc hc' => R5Out.r7OuterPhaseContMRemaining_of_relativeCover hk4
    ((T12Asm2.margin_nonneg hk4).trans hc) hc' (hOuterCover k hk4 rL rR hL hR hmax c c' hc hc')

/-- **R.6's three mixed faces from PROVE-R6-FACE3's inner-hit inputs** (inner hit ⇒ non-corner landing ⇒ face). -/
theorem mixedFaces_of_innerHit
    (hR6Hit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6Fd.R6InnerSharedHitMixedRemaining.{0} k rL rR c 0 ∧
        R6Fd.R6InnerSharedHitMixedInfInfRemaining.{0} k rL rR c 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6FaceSMixedInfInfRemaining.{0} k rL rR c 0 := by
  intro k hk4 rL rR hL hR c hc
  obtain ⟨hI, hII⟩ := hR6Hit k hk4 rL rR hL hR c hc
  exact ⟨R6Fc.r6FaceSMixedRemaining_of_nonCorner (R6Fd.r6NonCornerMixedRemaining_of_innerHit hI),
    R6Fc.r6FaceSMixedInfRemaining_of_nonCorner (R6Fd.r6NonCornerMixedInfRemaining_of_innerHit hI),
    R6Fc.r6FaceSMixedInfInfRemaining_of_nonCorner (R6Fd.r6NonCornerMixedInfInfRemaining_of_innerHit hII)⟩

/-- **R.6's three two-outer faces from PROVE-R6-TWO's landing patches.** -/
theorem twoFaces_of_landingPatch
    (hR6Patch : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tn.R6LandingPatchTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tn.R6LandingPatchTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tn.R6LandingPatchTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := by
  intro k hk4 rL rR hL hR hbad
  obtain ⟨hP, hPI, hPII⟩ := hR6Patch k hk4 rL rR hL hR hbad
  exact ⟨R6Tn.r6FaceQTwoRemaining_of_landingPatch hP, R6Tn.r6FaceQTwoInfRemaining_of_landingPatch hPI,
    R6Tn.r6FaceQTwoInfInfRemaining_of_landingPatch hPII⟩

/-- **Theorem 1.2's binder `hR6Cert` from the leaves**: the initial heights, the outer incident cover, the inner-hit
inputs and the landing patches. -/
theorem r6Cert_of_leaves
    (hWordInit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Fresh.R7SplitRemainingInit.{0} k rL rR c c')
    (hOuterCover : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Out.R7OuterRelativeCoverMRemaining.{0} k rL rR c c')
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hR6Hit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6Fd.R6InnerSharedHitMixedRemaining.{0} k rL rR c 0 ∧
        R6Fd.R6InnerSharedHitMixedInfInfRemaining.{0} k rL rR c 0)
    (hR6Patch : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Tn.R6LandingPatchTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tn.R6LandingPatchTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Tn.R6LandingPatchTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → R6Rel.R6NestCertRemaining.{0} k rL rR :=
  r6Cert_ofW (phaseWordM_of_init hWordInit) (outerContM_of_cover hOuterCover) hDy0
    (mixedFaces_of_innerHit hR6Hit) (twoFaces_of_landingPatch hR6Patch)

end InteractingSLE.Wire.T12Asm4
