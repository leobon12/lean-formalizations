/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Conjugate
import InteractingSLE.Spec.Sec7.SideC14Offset

/-! # R98: the implemented inversion transport with its constants exposed

PROVE-SIDE-COLLAR2. The existing `sourceShift` includes the inversion
lift at the inverse argument. It is exactly the corrected R98 frame,
not literal scalar composition with a constant shift.
-/
set_option autoImplicit false
noncomputable section
open Set
open QuantumZipper (H chiC)
open scoped Real

namespace InteractingSLE.Sec7.SideC16
open WangWu SideC12

/-- The upper-half-plane inversion exchanges the argument with its complement. -/
theorem arg_negInv {z : ℂ} (hz : z ∈ H) : Complex.arg (negInv z) = π - Complex.arg z := by
  have hzi : z⁻¹.im < 0 := by
    simpa only [Complex.inv_im, neg_div] using neg_neg_of_pos (div_pos hz (Complex.normSq_pos.mpr
      (StripSysField.mem_H_ne_zero hz)))
  rw [negInv, Complex.arg_neg_eq_arg_add_pi_of_im_neg hzi, Complex.arg_inv]
  have hne : Complex.arg z ≠ π := ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz)))
  rw [ite_eq_right hne]
  ring

/-- The actual deterministic transport correction is `πχ − 2χ Arg z`.
Thus the already installed frame includes R98's nonconstant correction. -/
theorem sourceShift_eq_corrected_frame {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : z ∈ H) :
    sourceShift (-(π * chiC κ)) (chiC (16 / κ)) 0 z =
      π * chiC κ - 2 * chiC κ * Complex.arg z := by
  rw [sourceShift, Sec4.chiC_sixteen_div hκ, StripSysField.infinitySourceChart_lift, arg_negInv hz]
  ring

/-- The source constant is zero, and the normalized offset has exactly
R98's displayed value. This holds pointwise for every integer fibre. -/
theorem sourceFrameOffset_zero (κ : ℝ) (n : ℤ) :
    Wire.sourceFrameOffset κ 0 n = 2 * π * chiC κ * (1 - (n : ℝ)) := by
  rw [Wire.sourceFrameOffset, zero_add]

/-- The inherited source index `1` is precisely the zero-offset choice. -/
theorem sourceFrameOffset_one (κ : ℝ) : Wire.sourceFrameOffset κ 0 1 = 0 := by
  rw [sourceFrameOffset_zero]
  norm_num

end InteractingSLE.Sec7.SideC16
