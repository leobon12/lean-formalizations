/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Statement
import InteractingSLE.WangWu.ReverseContactBdryChart
import InteractingSLE.WangWu.Prop418RangeGlue
import InteractingSLE.Spec.Sec5.GlueCondMean

/-!
# The height-shifted two-slit law, part 1: the shift of the boundary data and of the centred field

Packet PROVE-WW-B26. In the shifted setting of `ImageWordFiltShiftStatement` the forward field is `h = X + δλ`
(`λ = π/2`), with the two-seed data of `(r_L; r_R)`, and the glued field `X` has the two-seed data of
`(r_L + δ; r_R − δ)`.

* `forceBoundaryData_twoSeed_shift`: the data of `(r_L + δ; r_R − δ)` are those of `(r_L; r_R)` minus `δλ`;
* `isBoundedHarmonicExtension_shift`: so `u₀ − δλ` is the bounded harmonic extension of the shifted data;
* **`centredField_shift`**: the centred field of `h` (for `u₀`) is the centred field of `X` (for `u₀ − δλ`): the two
  couplings share one centred field, which is what lets the forward slit of `h` and the reverse slit of `X` be glued;
* **`fbd_add_fbd_eq_shift`**: the boundary data of the reversed slit (word `(r_R − δ; r_L + δ)`) and of the image word
  `(r_L, −r_L − δ; r_R, −r_R + δ)` at corresponding real points add up to `δλ` (with `δ = 0` this is
  `fbd_add_fbd_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.Shift

open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

theorem sqrt_four_lambda : Real.pi / Real.sqrt 4 = wwLambda := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

/-- The two-seed data of `(r_L + δ; r_R − δ)` are those of `(r_L; r_R)` minus `δλ`. -/
theorem forceBoundaryData_twoSeed_shift (rL rR δ x : ℝ) :
    forceBoundaryData 4 (fun _ : Fin 1 => rL + δ) (fun _ : Fin 1 => rR - δ) LP.twoSeedXL LP.twoSeedXR x =
      forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR x +
        -(δ * wwLambda) := by
  rw [forceBoundaryData_twoSeed, forceBoundaryData_twoSeed, sqrt_four_lambda]
  split_ifs <;> ring

/-- **The bounded harmonic extension of the shifted data** is `u₀ − δλ`. -/
theorem isBoundedHarmonicExtension_shift {rL rR δ : ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀) :
    IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL + δ) (fun _ : Fin 1 => rR - δ)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) (fun z => u₀ z + -(δ * wwLambda)) := by
  have h := Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu₀ (-(δ * wwLambda))
  have e : (fun x => forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR x +
      -(δ * wwLambda)) = forceBoundaryData 4 (fun _ : Fin 1 => rL + δ) (fun _ : Fin 1 => rR - δ) LP.twoSeedXL
        LP.twoSeedXR := funext fun x => (forceBoundaryData_twoSeed_shift rL rR δ x).symm
  rwa [e] at h

/-- `flowField 0 a` adds `a ∫ φ`. -/
theorem flowField_zero_apply (a : ℝ) (f : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    Exist.flowField 0 a f φ = f φ + a * ∫ w, φ w := by
  rw [Exist.flowField_apply, Sec5.GlueCond.pushTest_shiftChart_zero]

/-- **The shifted field has the same centred field**: if `h = X + δλ`, then `h − u₀ = X − (u₀ − δλ)`. -/
theorem centredField_shift {Ω : Type*} {h X : Ω → DistOn upperHalfPlaneOpens} {δ : ℝ}
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    WholeField.centredField h u₀ = WholeField.centredField X (fun z => u₀ z + -(δ * wwLambda)) := by
  have hu₀' : InnerProductSpace.HarmonicOnNhd (fun z => u₀ z + -(δ * wwLambda)) H := fun z hz =>
    (hu₀ z hz).add (InnerProductSpace.harmonicAt_const _)
  funext ω
  ext φ
  rw [WholeField.centredField_apply h hu₀, WholeField.centredField_apply X hu₀', hX ω, flowField_zero_apply]
  have hi1 : Integrable fun z => u₀ z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  have hi2 : Integrable fun z => -(δ * wwLambda) * φ z :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul _
  have e : (fun z => (u₀ z + -(δ * wwLambda)) * φ z) = fun z => u₀ z * φ z + -(δ * wwLambda) * φ z := by
    funext z; ring
  rw [e, integral_add hi1 hi2, integral_const_mul]
  ring

/-- The shifted centred field is a zero-boundary GFF when the forward one is. -/
theorem isZeroBoundaryGFF_centredField_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h X : Ω → DistOn upperHalfPlaneOpens} {δ : ℝ} (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (WholeField.centredField X (fun z => u₀ z + -(δ * wwLambda))) P := by
  rwa [← centredField_shift hX hu₀]

/-- **The data of the reversed slit and of the shifted image word add up to `δλ`** at corresponding real points
(the shifted form of `fbd_add_fbd_eq_zero`). -/
theorem fbd_add_fbd_eq_shift {rL rR δ vL vR aL aR bL bR ξ x : ℝ}
    (hbaL : bL < aL) (haL : aL ≤ 0) (haR : 0 ≤ aR) (habR : aR < bR)
    (hξ0 : ξ ≠ 0) (hξL : ξ ≠ vL) (hξR : ξ ≠ vR)
    (hA : 0 < ξ → ξ < vR → x < bL) (hB : vR < ξ → bL < x ∧ x < aL)
    (hC : ξ < vL → aR < x ∧ x < bR) (hD : vL < ξ → ξ < 0 → bR < x) :
    forceBoundaryData 4 (fun _ : Fin 1 => rR - δ) (fun _ : Fin 1 => rL + δ) (fun _ => vL) (fun _ => vR) ξ +
      forceBoundaryData 4 ![rL, -rL - δ] ![rR, -rR + δ] ![aL, bL] ![aR, bR] x = δ * wwLambda := by
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · rcases lt_or_gt_of_ne hξL with hlt | hgt
    · obtain ⟨h1, h2⟩ := hC hlt
      rw [fbd_one_neg hneg, fbd_two_nonneg (by linarith), sqrt_four_lambda]
      simp only [hlt, show aR ≤ x from h1.le, show ¬ bR ≤ x from not_le.2 h2, ↓reduceIte]
      ring
    · have h1 := hD hgt hneg
      rw [fbd_one_neg hneg, fbd_two_nonneg (by linarith), sqrt_four_lambda]
      simp only [show ¬ ξ < vL from not_lt.2 hgt.le, show aR ≤ x by linarith, show bR ≤ x from h1.le,
        ↓reduceIte]
      ring
  · rcases lt_or_gt_of_ne hξR with hlt | hgt
    · have h1 := hA hpos hlt
      rw [fbd_one_nonneg hpos.le, fbd_two_neg (by linarith), sqrt_four_lambda]
      simp only [show ¬ vR ≤ ξ from not_le.2 hlt, show x < aL by linarith, show x < bL from h1, ↓reduceIte]
      ring
    · obtain ⟨h1, h2⟩ := hB hgt
      rw [fbd_one_nonneg hpos.le, fbd_two_neg (by linarith), sqrt_four_lambda]
      simp only [show vR ≤ ξ from hgt.le, show x < aL from h2, show ¬ x < bL from not_lt.2 h1.le,
        ↓reduceIte]
      ring

end InteractingSLE.WangWu.Shift
