/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMart
import InteractingSLE.Spec.Sec5.GlueCondUnionImgMean

/-!
# The junction weights of the image word in Proposition 4.9's direction: the evidence in Lean

Packet PROVE-GLUECOND7 (orchestrator's request after PROVE-GLUECOND6's finding). The image word of `Word49` (the flow
line read in the counterflow chart `Ψ = R ∘ f′_s ∘ R`) has one junction weight on each side. PROVE-GLUECOND5 took them
from Remark 4.10's strip heights (`cL5 = κ/2 − 2 − Σρ_L`, `cR5 = −Σρ_R`); PROVE-GLUECOND6 computed
`cL6 = κ − 4 − Σρ_L`, `cR6 = κ/2 − 2 − Σρ_R`. This file settles the question from the frozen counterflow convention:

1. **The lift.** The chart `cfChart` uses the chain-rule lift `Im L_Ψ` (`psiLog`) with height shift `2πχ`; this is
   exactly the coordinate rule with PROVE-GLUECOND6's lift `arg_Ψ = Im logDerivPsi = Im L_Ψ + 2π`, the branch with
   `arg_Ψ → 0` on the physical real line (`GlueImg.tendsto_im_logDerivPsi`), the only branch for which the image data
   near the flow's base is the original data (`chart_shift_eq`).
2. **The image-chart mean of `h` given the counterflow prefix** (`cfMeanQ_add_eq_retMean_add`): the conditional mean of
   `h` near `R(K′_s)` is `cfMeanQ + 𝔥₀` (PROVE-GLUECOND2/5: `cfMeanQ` is the mean of the centred field
   `cenT κ 𝔥₀ (cfField κ h) = h − 𝔥₀`, built from the counterflow field's data `b − πχ/2`), and
   `cfMeanQ + 𝔥₀ + χ arg_Ψ = retMean ∘ Ψ + πχ/2` (PROVE-GLUECOND6's identity with `u_b = 𝔥₀ − πχ/2`).
   At `s = 0` the right side is `𝔥₀` (the original flow data), as it must be.
3. **The exposed heights** (`exposed_left_height`, `exposed_right_height`): `retMean`'s boundary data plus `πχ/2` on the
   exposed counterflow sides are `−λ + 2πχ` (left of the left junction) and `λ − πχ` (right of the right junction).
4. **The junction weights** (`junction_cL6`, `junction_cR6`): the image word's far-left height
   `−λ(1 + Σρ_L + ρ′_L)` and far-right height `λ(1 + Σρ_R + ρ′_R)` match these exactly for `cL6`, `cR6`; for
   `cL5`, `cR5` they do **not** match for any `0 < κ < 4` (`junction_cL5_ne`, `junction_cR5_ne`). So at image time `0`
   (and hence along the image word) the coupling mean with PROVE-GLUECOND5's weights is not the conditional mean of the
   field in the chart, and `ImageWord49FiltStatement` (`= ImageWord49FiltWStatement cL5 cR5`) is false whenever the
   image word is non-degenerate; the corrected statement is `ImageWord49FiltCStatement := ImageWord49FiltWStatement
   cL6 cR6`.

Consistency check (not in Lean): with `cL6`, `cR6` the cumulative image weights are `κ − 4` on the left (`< κ/2 − 2`:
the image curve can hit the exposed left side, i.e. `η` can exit on the left side of the counterflow prefix, as
Proposition 4.9 asserts) and `κ/2 − 2` on the right (critical: no hit on the right). With `cL5`, `cR5` they would be
`κ/2 − 2` (critical, no hit) and `0` (no hit): the flow line could never exit on the left side, contradicting
Proposition 4.9.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref Sec7.StripSysField

namespace Word49

/-! ### The lift normalization -/

theorem im_logDerivPsi_eq (w : ℝ → ℝ) (s : ℝ) (z : ℂ) :
    (GlueImg.logDerivPsi w s z).im = (psiLog w s z).im + 2 * Real.pi := by
  have e : GlueImg.logDerivPsi w s z = psiLog w s z + 2 * (Real.pi : ℂ) * I := rfl
  rw [e, add_im]
  simp

/-- **The coordinate rule of `cfChart` is PROVE-GLUECOND6's**: height shift `2πχ` plus `χ` times the chain-rule lift is
`χ · arg_Ψ` with the branch normalized on the physical real line. -/
theorem chart_shift_eq (κ : ℝ) (s : ℝ≥0) (y : HistorySpace 0 0) (z : ℂ) :
    2 * Real.pi * chiC κ + chiC κ * (cfChart s y).2.2 z =
      chiC κ * (GlueImg.logDerivPsi (cfDrv0 s y) s z).im := by
  rw [cfChart_lift, im_logDerivPsi_eq]
  ring

/-! ### The image-chart mean of the field given the counterflow prefix -/

section Mean

variable {κ : ℝ} {nL nR : ℕ}

/-- **The conditional mean of `h` near `R(K′_s)`, read through `Ψ` with the normalized lift, is `retMean + πχ/2`**
(PROVE-GLUECOND6's identity for the counterflow field's data `b − πχ/2`, whose bounded harmonic extension is
`𝔥₀ − πχ/2`). -/
theorem cfMeanQ_add_eq_retMean_add (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(Real.pi / 2 * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(Real.pi / 2 * chiC κ)) (forceJumpFinset xL xR))
      u') (t : ℝ≥0) (y : HistorySpace 0 0) {z : ℂ} (hz : z ∈ H \ cfHullQ t y) :
    cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(Real.pi / 2 * chiC κ)) (forceJumpFinset xL xR) u' t y z +
        u₀ z + chiC κ * (GlueImg.logDerivPsi (Ito.rpath (Sec4.regPath (cfStop t y))) t z).im =
      GlueImg.retMean κ (cfU κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(Real.pi / 2 * chiC κ))
          (forceJumpFinset xL xR) t (cfStop t y)) (revChart (Ito.rpath (Sec4.regPath (cfStop t y))) t z) +
        Real.pi / 2 * chiC κ := by
  have hb := isPiecewiseConstant_forceData κ ρL ρR xL xR (-(Real.pi / 2 * chiC κ))
  have hu_b : IsBoundedHarmonicExtension (fun x => forceBoundaryData κ ρL ρR xL xR x + -(Real.pi / 2 * chiC κ))
      (forceJumpFinset xL xR) (fun z => u₀ z + -(Real.pi / 2 * chiC κ)) := by
    rw [coe_forceJumpFinset]
    exact isBoundedHarmonicExtension_add_const hu₀ _
  have h := GlueImg.cfMeanQ_add_eq_retMean hκ hb hu_b hu' t y hz
  linear_combination h

end Mean

/-! ### The exposed heights and the junction weights -/

section Heights

variable {κ : ℝ}

theorem pi_mul_chiC_eq (hκ : 0 < κ) : Real.pi * chiC κ = Real.pi / Real.sqrt κ * (2 - κ / 2) := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  rw [QuantumZipper.chiC]
  field_simp
  nlinarith [hsq]

theorem chiC_pos (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < chiC κ := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  rw [QuantumZipper.chiC, sub_pos, div_lt_div_iff₀ two_pos hr]
  nlinarith [hsq]

/-- **The height of the field in the chart `Ψ` on the exposed left side**: the return data of the counterflow word
(left of the left junction) plus the centring constant `πχ/2` is `−λ + 2πχ`. -/
theorem exposed_left_height (hκ : 0 < κ) {mL mR : ℕ} (ρL : Fin mL → ℝ) (ρR : Fin mR → ℝ) (vL : Fin mL → ℝ)
    (vR : Fin mR → ℝ) {x : ℝ} (hx : x < 0) (hR : ∀ i, -x⁻¹ < vR i) :
    returnData (cfOffset κ) (cfCoeff κ) (forceBoundaryData (16 / κ) ρL ρR vL vR) x + Real.pi / 2 * chiC κ =
      -(Real.pi / Real.sqrt κ) + 2 * (Real.pi * chiC κ) := by
  rw [GlueImg.returnData_forceBoundaryData_left hκ ρL ρR vL vR hx hR, GlueImg.pi_div_sqrt_sixteen_div hκ]
  ring

/-- **The height of the field in the chart `Ψ` on the exposed right side**: `λ − πχ`. -/
theorem exposed_right_height (hκ : 0 < κ) {mL mR : ℕ} (ρL : Fin mL → ℝ) (ρR : Fin mR → ℝ) (vL : Fin mL → ℝ)
    (vR : Fin mR → ℝ) {x : ℝ} (hx : 0 < x) (hL : ∀ i, vL i < -x⁻¹) :
    returnData (cfOffset κ) (cfCoeff κ) (forceBoundaryData (16 / κ) ρL ρR vL vR) x + Real.pi / 2 * chiC κ =
      Real.pi / Real.sqrt κ - Real.pi * chiC κ := by
  rw [GlueImg.returnData_forceBoundaryData_right hκ ρL ρR vL vR hx hL, GlueImg.pi_div_sqrt_sixteen_div hκ]
  ring

/-- **The left junction weight `cL6` matches the exposed left height.** -/
theorem junction_cL6 (hκ : 0 < κ) (S : ℝ) :
    -(Real.pi / Real.sqrt κ) * (1 + S + cL6 κ S) = -(Real.pi / Real.sqrt κ) + 2 * (Real.pi * chiC κ) := by
  rw [pi_mul_chiC_eq hκ, cL6]
  ring

/-- **The right junction weight `cR6` matches the exposed right height.** -/
theorem junction_cR6 (hκ : 0 < κ) (S : ℝ) :
    Real.pi / Real.sqrt κ * (1 + S + cR6 κ S) = Real.pi / Real.sqrt κ - Real.pi * chiC κ := by
  rw [pi_mul_chiC_eq hκ, cR6]
  ring

/-- **PROVE-GLUECOND5's left junction weight does not match the exposed left height** (for `0 < κ < 4`). -/
theorem junction_cL5_ne (hκ : 0 < κ) (hκ4 : κ < 4) (S : ℝ) :
    -(Real.pi / Real.sqrt κ) * (1 + S + cL5 κ S) ≠ -(Real.pi / Real.sqrt κ) + 2 * (Real.pi * chiC κ) := by
  intro h
  have hχ := chiC_pos hκ hκ4
  have h2 : -(Real.pi / Real.sqrt κ) * (1 + S + cL5 κ S) = -(Real.pi / Real.sqrt κ) + Real.pi * chiC κ := by
    rw [pi_mul_chiC_eq hκ, cL5]
    ring
  have : Real.pi * chiC κ = 0 := by linarith
  exact (mul_pos Real.pi_pos hχ).ne' this

/-- **PROVE-GLUECOND5's right junction weight does not match the exposed right height** (for `0 < κ < 4`). -/
theorem junction_cR5_ne (hκ : 0 < κ) (hκ4 : κ < 4) (S : ℝ) :
    Real.pi / Real.sqrt κ * (1 + S + cR5 κ S) ≠ Real.pi / Real.sqrt κ - Real.pi * chiC κ := by
  intro h
  have hχ := chiC_pos hκ hκ4
  have h2 : Real.pi / Real.sqrt κ * (1 + S + cR5 κ S) = Real.pi / Real.sqrt κ := by
    rw [cR5]
    ring
  have : Real.pi * chiC κ = 0 := by linarith
  exact (mul_pos Real.pi_pos hχ).ne' this

end Heights

end Word49

end InteractingSLE.Sec5.CrossCond
