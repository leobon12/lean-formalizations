import HigherDimLQGContinuity.Rotation.Field
import HigherDimLQGMetric.Kernel.ConvKernelSmooth
import HigherDimLFPP.Paths.Compare

/-!
# Rotation covariance of convolution LFPP

The convolution kernel is radial by the pinned library's Fourier argument. Consequently each
truncated test function and its distributional limit commute with orthogonal pullback. The
LFPP distance then follows from the existing path transport theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Radiality of the convolution kernel, specialized to a linear isometry. -/
theorem convKernel_linearIsometry (κ : Rd d → ℝ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x : Rd d) :
    convKernel κ (O x) = convKernel κ x :=
  HigherDimLQGMetric.convKernel_radial (O.norm_map x)

private lemma convKernelEps_linearIsometry (κ : Rd d → ℝ) (ε : ℝ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x : Rd d) :
    convKernelEps κ ε (O x) = convKernelEps κ ε x := by
  simp only [convKernelEps, ← map_smul, convKernel_linearIsometry]

private lemma radialProfile_linearIsometry (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (x : Rd d) : radialProfile d (O x) = radialProfile d x :=
  HigherDimLQGMetric.radialProfile_eq_of_norm_eq (O.norm_map x)

private lemma convTrunc_rotDistRd (κ : Rd d → ℝ) (ε : ℝ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (z : Rd d) (n : ℕ) :
    testRotPull O (convTrunc κ ε z n) = convTrunc κ ε (O z) n := by
  by_cases hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)
  · apply TestFunction.ext
    intro w
    simp only [testRotPull_apply, convTrunc, dite_eq_left hK]
    change convKernelEps κ ε (z - O.symm w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (O.symm w - z)) =
      convKernelEps κ ε (O z - w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - O z))
    rw [← convKernelEps_linearIsometry κ ε O (z - O.symm w),
      ← radialProfile_linearIsometry O (((n : ℝ) + 1)⁻¹ • (O.symm w - z))]
    simp only [map_sub, O.apply_symm_apply, map_smul]
  · simp only [convTrunc, dite_eq_right hK, map_zero]

/-- Orthogonal covariance of convolution mollification for every distribution. -/
theorem convMollify_rotDistRd (κ : Rd d → ℝ) (ε : ℝ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (g : DistRd d) (z : Rd d) :
    convMollify κ ε (rotDistRd O g) z = convMollify κ ε g (O z) := by
  simp only [convMollify]
  congr 1
  funext n
  exact congrArg g (convTrunc_rotDistRd κ ε O z n)

/-- Orthogonal covariance of the convolution LFPP distance. -/
theorem lfppDist_rotDistRd (κ : Rd d → ℝ) (ξ ε : ℝ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (g : DistRd d) (x y : Rd d) :
    lfppDist κ ξ ε (rotDistRd O g) (x, y) =
      lfppDist κ ξ ε g (O x, O y) := by
  simp only [lfppDist]
  rw [HigherDimLFPP.lfppDistOn_linearIsometryEquiv O ξ (convMollify κ ε g) univ x y]
  simp only [preimage_univ]
  congr 1
  funext z
  exact convMollify_rotDistRd κ ε O g z

end HigherDimLQGContinuity
