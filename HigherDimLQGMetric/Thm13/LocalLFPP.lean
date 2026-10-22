import HigherDimLQGMetric.Thm13.TruncMeas
import HigherDimLQGMetric.Weak.DetLFPPWeylUpper
import HigherDimLQGMetric.Metric.WeylMetric
import HigherDimLQGMetric.Trunc.Locality

/-!
# Locality of internal LFPP distances

The LFPP metric of a continuous field is a Weyl scaling of that of another
continuous field. Consequently its internal metric on an open set depends
only on the field there. This is the deterministic locality step used when
truncated fields are patched.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l8_fieldLfppMetric_eq_weyl (ξ : ℝ) (φ ψ : C(Rd d, ℝ)) :
    fieldLfppMetric ξ ψ =
      weylMetric ξ (ψ - φ) (fieldLfppMetric ξ φ)
        (fieldLfppMetric_isLength ξ φ) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  rw [weylMetric_apply, fieldLfppMetric_apply]
  have hsum : (fun x : Rd d => φ x + (ψ - φ) x) = ψ := by
    funext x
    simp only [ContinuousMap.sub_apply]
    ring
  have hweyl : weylScale ξ (ψ - φ) (fieldLfppMetric ξ φ) p.1 p.2 =
      fieldLfppE ξ ψ p.1 p.2 := by
    rw [← hsum]
    exact le_antisymm
      (weylScale_le_fieldLfppE φ.continuous (ψ - φ) p.1 p.2)
      (fieldLfppE_le_weylScale φ.continuous (ψ - φ) p.1 p.2)
  rw [hweyl]
  rfl

/-- Equal fields on an open set induce equal internal LFPP metrics there. -/
theorem l8_fieldLfppMetric_internal_congr (ξ : ℝ)
    (φ ψ : C(Rd d, ℝ)) {U : Set (Rd d)} (hU : IsOpen U)
    (hφψ : EqOn (⇑φ) (⇑ψ) U) (z w : Rd d) :
    (fieldLfppMetric ξ φ).internal U z w =
      (fieldLfppMetric ξ ψ).internal U z w := by
  rw [l8_fieldLfppMetric_eq_weyl ξ φ ψ,
    weylMetric_internal (fieldLfppMetric_isLength ξ φ) hU]
  have hzero : ∀ x ∈ U, ξ * (ψ - φ) x = (0 : ℝ) := by
    intro x hx
    rw [ContinuousMap.sub_apply, ← hφψ hx]
    ring
  rw [weylScaleOn_of_eq_const hzero]
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- A truncated LFPP internal metric on `U` only sees a slightly larger region.
This is the deterministic restriction statement needed before taking limits. -/
theorem l8_truncInternal_addFun_congr {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) (g : DistRd d)
    (f f' : C(Rd d, ℝ)) (U V : TopologicalSpace.Opens (Rd d))
    (hUV : ∀ z ∈ (U : Set (Rd d)),
      Metric.closedBall z (Real.sqrt ε) ⊆ V)
    (hff' : EqOn (⇑f) (⇑f') V) (z w : Rd d) :
    (fieldLfppMetric ξ
      (l8_truncFieldC hd hκ hε (addFun g f))).internal U z w =
    (fieldLfppMetric ξ
      (l8_truncFieldC hd hκ hε (addFun g f'))).internal U z w := by
  apply l8_fieldLfppMetric_internal_congr ξ _ _ U.isOpen
  intro x hx
  exact l2c_truncMollify_eq_of_restrictTo hd hκ hε x V (hUV x hx)
    (restrictTo_addFun_congr V g hff')

end HigherDimLQGMetric
