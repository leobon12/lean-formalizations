/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorTwoFace
import InteractingSLE.Spec.Wire.T12Asm5Inputs

/-!
# Drop-in: R.6's three two-outer faces with no input, and Theorem 1.2's `hR6Cert` without `hR6Same`

Packet PROVE-R6-CORNER, second round. No Aux. lemma 136, no singleton-tip or landing-patch input.

* `r6FaceQTwo{,Inf,InfInf}Remaining_of_walls`: the three faces in `R6FaceQ` form from Prop. 4.11 and Lemma 4.7
  (`R6Two.r6FaceQTwo*Remaining_of_faceS` after `R6Cor.r6FaceSTwo*Remaining_of_walls`);
* **`twoFaces_proved`**: the three faces at Theorem 1.2's margins `(π χ(16/k), 0)`, universe `0`, with Prop. 4.11 and
  Lemma 4.7 from the committed clearance Part A (`Wire.T12Asm3.partA`): exactly the output of
  `Wire.T12Asm5.twoFaces_of_sameTime`, without its binder `hR6Same`;
* **`r6Cert_of_leaves_corner`**: `Wire.T12Asm5.r6Cert_of_leaves5` without `hR6Same` (only the fibre cover `hDy0`).

R43/R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`
(Cond44 is R74's `T12Asm2.cond44Holds`, inside `Wire.T12Asm4.r6Cert_ofW`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Sec7.R6Cor

open R6Safe

universe u

variable {k rL rR c c' : ℝ}

/-- **R.6's two-outer face `Two` in `R6FaceQ` form**, from the reverse visits of `M_L`. -/
theorem r6FaceQTwoRemaining_of_walls (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R6FaceQTwoRemaining.{u} k rL rR c c' :=
  R6Two.r6FaceQTwoRemaining_of_faceS (r6FaceSTwoRemaining_of_walls h411 h47 h47T hk4 hc hc')

/-- **R.6's two-outer face `TwoInf` in `R6FaceQ` form**, from the reverse visits of `M_L`. -/
theorem r6FaceQTwoInfRemaining_of_walls (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R6FaceQTwoInfRemaining.{u} k rL rR c c' :=
  R6Two.r6FaceQTwoInfRemaining_of_faceS (r6FaceSTwoInfRemaining_of_walls h411 h47 h47T hk4 hc hc')

/-- **R.6's two-outer face `TwoInfInf` in `R6FaceQ` form**, from the reverse visits of `M_L`. -/
theorem r6FaceQTwoInfInfRemaining_of_walls (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R6FaceQTwoInfInfRemaining.{u} k rL rR c c' :=
  R6Two.r6FaceQTwoInfInfRemaining_of_faceS (r6FaceSTwoInfInfRemaining_of_walls h411 h47 h47T hk4 hc hc')

/-- **R.6's three two-outer faces at Theorem 1.2's margins, PROVED with no input** (universe `0`; Prop. 4.11 and
Lemma 4.7 from the committed clearance Part A, `Wire.T12Asm3.partA`). This is exactly the output of
`Wire.T12Asm5.twoFaces_of_sameTime`, without its binder `hR6Same`. -/
theorem twoFaces_proved :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 := by
  intro k hk4 rL rR _ _ _
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := Wire.late_lemma47QHitStatement Wire.T12Asm3.partA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 Wire.T12Asm3.partA
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => Wire.late_lemma47QHitTStatement Wire.T12Asm3.partA h1 h2
  have hc := Wire.T12Asm2.margin_nonneg hk4
  exact ⟨r6FaceQTwoRemaining_of_walls h411 h47 h47T hk4 hc le_rfl,
    r6FaceQTwoInfRemaining_of_walls h411 h47 h47T hk4 hc le_rfl,
    r6FaceQTwoInfInfRemaining_of_walls h411 h47 h47T hk4 hc le_rfl⟩

/-- **Drop-in for `Wire.T12Asm5.r6Cert_of_leaves5` without `hR6Same`**: Theorem 1.2's binder `hR6Cert` from the fibre
cover alone (R.5, the mixed faces and now the two-outer faces all proved). -/
theorem r6Cert_of_leaves_corner
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → R6Rel.R6NestCertRemaining.{0} k rL rR :=
  Wire.T12Asm4.r6Cert_ofW Wire.T12Asm5.phaseWordM_margin
    (Wire.T12Asm4.outerContM_of_cover R5Init.hOuterCover_proved) hDy0 Wire.T12Asm5.mixedFaces_proved
    twoFaces_proved

end InteractingSLE.Sec7.R6Cor
