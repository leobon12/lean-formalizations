/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm2Inputs
import InteractingSLE.Spec.Sec7.R5WallAssemblyWord
import InteractingSLE.Spec.Sec7.R5OutCapacityWire
import InteractingSLE.Spec.Sec7.R6SafeMeetInf

/-! # The R.5 and R.6 leaves of Theorems 1.2–1.3 on the latest landed reductions

PROVE-T12-ASSEMBLE3. The three R.5/R.6 binders of `T12Asm.theorem12Statement_assembled`
(`hWordPhase`, `hOuterCont`, `hR6Cert`) from the latest named inputs:

* R.5 on the extremal pockets: PROVE-R5-WALL's split-cover word inputs `R5Wall.R7SplitWordRemaining`
  (LIFT2's two lift words at one integer field, and `hInit`), at every margin `πχ(16/k) ≤ c`, `0 ≤ c'`;
* R.5 on the outer pockets: PROVE-R5-OUTER's incident-component form `R5Out.R7OuterRelativeCoverMRemaining`
  (ruling R88), at the same margins;
* R.6: PROVE-R6-SAFE's face descriptions — the mixed faces `R6Safe.R6FaceSMixed{,Inf,InfInf}Remaining` at every
  margin `πχ(16/k) ≤ c` and the two-outer-arm faces `R6Safe.R6FaceQTwo{,Inf,InfInf}Remaining` at `(πχ(16/k), 0)`.

The margins above Theorem 1.2's `(πχ(16/k), 0)` are needed because R.6 runs R.5 on the inner pocket of a mixed
configuration (`hword`) and, for two outer arms, on the intermediate pocket `V` (`TwoOuterFaceSInputs`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`
(Cond44 is R74's `T12Asm2.cond44Holds`).
-/

set_option autoImplicit false
noncomputable section

open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Wire.T12Asm3

open Sec7 Sec7.R6Safe Sec7.R6Nest Sec7.R6Fin Sec7.R7Leaves Sec7.R7Outer

/-- Clearance Part A from the proved A.1 C laws (as in `T12Asm.theorem12Statement_assembled`). -/
theorem partA : Sec5.PartAInputsSixteenDivOfClearance :=
  late_partAInputs (fun κ => Beacon.coreG3_of_lawC (T12Asm.g3Law T12Asm2.g3S T12Asm2.g3F κ))
    (fun κ => Beacon.coreEight_of_lawC (T12Asm.eightLaw T12Asm2.eightS κ))

/-- Aux. 7 at every dual parameter `k > 4`, from clearance Part A. -/
theorem aux7 (k : ℝ) (hk4 : 4 < k) : Sec4.Aux7Statement.{0} k :=
  aux7_of_sixteen_div (fun _ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance partA hκ hκ4) k hk4

/-- The max of the inner pocket's weights is `k/2 − 4` on an outer configuration. -/
theorem max_inner_eq {k rL rR : ℝ} (hout : k / 2 - 4 < max rL rR) :
    max (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4)) = k / 2 - 4 := by
  apply le_antisymm (max_le (innerRight_weight_le k rL) (innerLeft_weight_le k rR))
  rcases lt_max_iff.1 hout with h | h
  · exact le_max_of_le_left (le_of_eq (by simp only [innerRight, h, ↓reduceIte]))
  · exact le_max_of_le_right (le_of_eq (by simp only [innerLeft, h, ↓reduceIte]))

/-- The max of the intermediate pocket's weights is `k/2 − 4` when the right arm is outer. -/
theorem max_innerV_eq {k rL : ℝ} (hdL : k / 2 - 4 < rL) :
    max (innerRight k rL rL (k / 2 - 4)) (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4)) = k / 2 - 4 := by
  have h1 : innerRight k rL rL (k / 2 - 4) = k / 2 - 4 := by simp only [innerRight, hdL, ↓reduceIte]
  have h2 : innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4) = k / 2 - 4 := by
    simp only [innerLeft, lt_irrefl, ↓reduceIte]
  rw [h1, h2, max_self]

section

variable
    (hWordSplit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Wall.R7SplitWordRemaining.{0} k rL rR c c')
    (hOuterCover : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Out.R7OuterRelativeCoverMRemaining.{0} k rL rR c c')

include hWordSplit in
/-- **R.5 up to phase on the extremal pockets at margins `πχ ≤ c`, `0 ≤ c'`** (PROVE-R5-WALL's
`r7PhaseWordRemaining_of_splitWord`). -/
theorem phaseWordM_of_split {k rL rR c c' : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmax : max rL rR = k / 2 - 4) (hc : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c') :
    PhaseCont.R7PhaseWordRemaining.{0} k rL rR c c' :=
  R5Wall.r7PhaseWordRemaining_of_splitWord hk4 ((T12Asm2.margin_nonneg hk4).trans hc) hc'
    (hWordSplit k hk4 rL rR hL hR hmax c c' hc hc')

include hWordSplit in
/-- **Theorem 1.2's binder `hWordPhase`** from the split-cover word inputs. -/
theorem wordPhase_of_split : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
    PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
  fun _ hk4 _ _ hL hR hmax => phaseWordM_of_split hWordSplit hk4 hL hR hmax le_rfl le_rfl

include hOuterCover in
/-- **Theorem 1.2's binder `hOuterCont`** from R5-OUTER's incident-component clauses (ruling R88;
`R5Out.r7OuterPhaseContRemaining_of_relativeCover`). -/
theorem outerCont_of_cover : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
    OuterPhNext.R7OuterPhaseContRemaining.{0} k rL rR :=
  fun k hk4 rL rR hL hR hmax => R5Out.r7OuterPhaseContRemaining_of_relativeCover hk4
    (hOuterCover k hk4 rL rR hL hR hmax _ _ le_rfl le_rfl)

variable
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hR6Mixed : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6FaceSMixedInfInfRemaining.{0} k rL rR c 0)
    (hR6Two : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)

include hDy0 hWordSplit hR6Mixed in
/-- **R.6's certificate on a mixed configuration** (`R6Safe.r6NestCertRemaining_of_core_safe`): the inner R.5
word from the split-cover inputs at the inner margins, the three cores from the mixed faces. -/
theorem r6Cert_mixed {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    R6Rel.R6NestCertRemaining.{0} k rL rR := by
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement partA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 partA
  have h51 := Beacon.prop51 partA hDy0
  have hout : k / 2 - 4 < max rL rR := by
    rcases hmix with h | h
    · exact lt_max_of_lt_left h.1
    · exact lt_max_of_lt_right h.2
  have hword : PhaseCont.R7PhaseWordRemaining.{0} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) :=
    phaseWordM_of_split hWordSplit hk4 (neg_two_lt_innerRight_weight hk4 hL)
    (neg_two_lt_innerLeft_weight hk4 hR) (max_inner_eq hout)
    (le_add_of_nonneg_right (sub_nonneg.2 (r7A_innerLeft_le hk4 rR)))
    (by rw [zero_add]; exact sub_nonneg.2 (r7B_innerRight_le hk4 rL))
  obtain ⟨hS, hSI, hSII⟩ := hR6Mixed k hk4 rL rR hL hR _ le_rfl
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement partA h1 h2
  have hc1 : R6FaceQMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6FaceQMixedRemaining_of_faceS hS
  have hc2 : R6FacePMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6FacePMixedRemaining_of_faceQ hc1
  have hc3 : R6FaceMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6FaceMixedRemaining_of_faceP hc2
  have hc4 : R6GeomCoreMixedRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := r6GeomCoreMixedRemaining_of_face hc3
  exact @r6NestCertRemaining_of_core_safe.{0} k rL rR h411 h51 h47 h47T
    (aux7 k hk4) T12Asm2.cond44Holds hword hc4
    (r6GeomCoreMixedInfRemaining_of_face (r6FaceMixedInfRemaining_of_faceP
      (r6FacePMixedInfRemaining_of_faceQ (r6FaceQMixedInfRemaining_of_faceS hSI))))
    (r6GeomCoreMixedInfInfRemaining_of_face (r6FaceMixedInfInfRemaining_of_faceP
      (r6FacePMixedInfInfRemaining_of_faceQ (r6FaceQMixedInfInfRemaining_of_faceS hSII))))
    hk4 hL hR hmix

include hWordSplit hOuterCover hR6Mixed hR6Two in
/-- **R.6's two-outer-arm inputs** `TwoOuterFaceSInputs` (PROVE-R6-SAFE): the extremal R.5 word and the outer R.5
continuity of the intermediate pocket `V = (α_R, β_L)` from the R.5 inputs at `V`'s margins, `V`'s mixed faces,
and the three two-outer faces. -/
theorem twoOuterFaceSInputs_of_inputs {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR) (hbad : ¬ (rL < k - 6 ∧ rR < k - 6)) :
    TwoOuterFaceSInputs.{0} k rL rR := by
  have hd : -2 < k / 2 - 4 := by linarith
  have hcV := pi_chi_le_leftExt_margin hk4 le_rfl hdR
  obtain ⟨hS, hSI, hSII⟩ := hR6Mixed k hk4 rL (k / 2 - 4) hL hd _ hcV
  obtain ⟨hT, hTI, hTII⟩ := hR6Two k hk4 rL rR hL hR hbad
  refine ⟨?_, hS, hSI, hSII, ?_, hT, hTI, hTII⟩
  · exact phaseWordM_of_split hWordSplit hk4 (neg_two_lt_innerRight_weight hk4 hL)
      (neg_two_lt_innerLeft_weight hk4 hd) (max_innerV_eq hdL)
      (le_add_of_le_of_nonneg hcV (sub_nonneg.2 (r7A_innerLeft_le hk4 _)))
      (by rw [zero_add]; exact sub_nonneg.2 (r7B_innerRight_le hk4 rL))
  · exact R5Out.r7OuterPhaseContMRemaining_of_relativeCover hk4 ((T12Asm2.margin_nonneg hk4).trans hcV) le_rfl
      (hOuterCover k hk4 rL (k / 2 - 4) hL hd (lt_max_of_lt_left hdL) _ 0 hcV le_rfl)

include hDy0 hWordSplit hOuterCover hR6Mixed hR6Two in
/-- **Theorem 1.2's binder `hR6Cert`** from R.5's split-cover and incident-component inputs and R.6's face
descriptions: mixed configurations by `r6Cert_mixed`, two outer arms by `R6Safe.r6NestCertRemaining_two` on
`TwoOuterFaceSInputs` (reduced to `TwoOuterInputs` by PROVE-R6-SAFE's face → core chain). -/
theorem r6Cert_of_faces : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
    ¬ (rL < k - 6 ∧ rR < k - 6) → R6Rel.R6NestCertRemaining.{0} k rL rR := by
  intro k hk4 rL rR hL hR _ hbad
  rcases mixed_or_twoOuter hk4 hbad with hmix | ⟨hdL, hdR⟩
  · exact r6Cert_mixed hWordSplit hDy0 hR6Mixed hk4 hL hR hmix
  · have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement partA
    have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 partA
    have h51 : Sec5.Cond44Ref.Prop51QStatement.{0} := Beacon.prop51 partA hDy0
    have hin : TwoOuterFaceSInputs.{0} k rL rR :=
      twoOuterFaceSInputs_of_inputs hWordSplit hOuterCover hR6Mixed hR6Two hk4 hL hR hdL hdR hbad
    exact @r6NestCertRemaining_two.{0} k rL rR h411 h51 h47
      (fun θ h1 h2 => late_lemma47QHitTStatement partA h1 h2) (aux7 k hk4) T12Asm2.cond44Holds partA hk4 hL hdL
      hdR (twoOuterInputs_of_face.{0} (twoOuterFaceInputs_of_faceP.{0} (twoOuterFacePInputs_of_faceQFull.{0}
        (twoOuterFaceQFullInputs_of_faceS.{0} hin))))

end

end InteractingSLE.Wire.T12Asm3
