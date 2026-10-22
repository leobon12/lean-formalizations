import HigherDimLQGMetric.Limits.MollApprox
import HigherDimLQGMetric.ConvField.Shifts
import HigherDimLQGMetric.Weak.DetLFPPWeylUpper

/-! The exact Weyl identity for a bounded continuous perturbation of LFPP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Fixed-cutoff LFPP of `h+f` is the Weyl transform of LFPP of `h`,
including the deterministic normalization. -/
theorem l6c_scaledLfpp_addFun_weyl {d : ℕ}
    (κ : Rd d → ℝ) (ξ ε a : ℝ) (ha : 0 < a)
    (h : DistRd d) (f : C(Rd d, ℝ))
    (hc : Continuous (convMollify κ ε h))
    (hg : Continuous (convMollify κ ε (ofCont f)))
    (hadd : ∀ z, convMollify κ ε (addFun h f) z =
      convMollify κ ε h z + convMollify κ ε (ofCont f) z)
    (u v : Rd d) :
    (weylScale ξ
      ⟨convMollify κ ε (ofCont f), hg⟩
      ((fieldLfppMetric ξ ⟨convMollify κ ε h, hc⟩).smul a⁻¹ (inv_pos.mpr ha))
      u v).toReal =
      a⁻¹ * lfppDist κ ξ ε (addFun h f) (u, v) := by
  let φ : C(Rd d, ℝ) := ⟨convMollify κ ε h, hc⟩
  let g : C(Rd d, ℝ) := ⟨convMollify κ ε (ofCont f), hg⟩
  have hφ : toCMapRd (fieldLfpp ξ ⇑φ) = (fieldLfppMetric ξ φ).1 := by
    ext p
    change (toCMapRd (fieldLfpp ξ (convMollify κ ε h))) p =
      (fieldLfppMetric ξ φ).1 p
    rw [toCMapRd_apply_of_continuous (continuous_fieldLfpp hc)]
    rfl
  have hm : IsContinuousMetric (toCMapRd (fieldLfpp ξ ⇑φ)) := by
    rw [hφ]
    exact (fieldLfppMetric ξ φ).2
  have hEq : (⟨toCMapRd (fieldLfpp ξ ⇑φ), hm⟩ : ContMetric d) =
      fieldLfppMetric ξ φ := Subtype.ext hφ
  have hsum : ((⇑φ : Rd d → ℝ) + ⇑g) = convMollify κ ε (addFun h f) := by
    funext z
    exact (hadd z).symm
  have hcadd : Continuous (convMollify κ ε (addFun h f)) := by
    rw [←hsum]
    exact hc.add hg
  change (weylScale ξ g ((fieldLfppMetric ξ φ).smul a⁻¹ (inv_pos.mpr ha)) u v).toReal = _
  rw [weylScale_smul, ←hEq, l6e_weylLfpp d ξ φ g hm u v, hsum]
  rw [fieldLfppE_eq_ofReal_lfppDistOn hcadd]
  change (ENNReal.ofReal a⁻¹ * ENNReal.ofReal
    (lfppDist κ ξ ε (addFun h f) (u,v))).toReal = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)]
  rw [ENNReal.toReal_ofReal]
  exact HigherDimLFPP.lfppDistOn_nonneg ξ _ Set.univ u v

/-- Algebraic Weyl identity for a normalized continuous LFPP field. -/
theorem l6c_scaledLfpp_weyl_field {d : ℕ} (ξ a : ℝ) (ha : 0 < a)
    (φ g : C(Rd d, ℝ)) (u v : Rd d) :
    (weylScale ξ g
      ((fieldLfppMetric ξ φ).smul a⁻¹ (inv_pos.mpr ha)) u v).toReal =
      a⁻¹ * fieldLfpp ξ ((⇑φ : Rd d → ℝ) + ⇑g) (u, v) := by
  have hφ : toCMapRd (fieldLfpp ξ ⇑φ) = (fieldLfppMetric ξ φ).1 := by
    ext p
    rw [toCMapRd_apply_of_continuous (continuous_fieldLfpp φ.continuous)]
    rfl
  have hm : IsContinuousMetric (toCMapRd (fieldLfpp ξ ⇑φ)) := by
    rw [hφ]
    exact (fieldLfppMetric ξ φ).2
  have hEq : (⟨toCMapRd (fieldLfpp ξ ⇑φ), hm⟩ : ContMetric d) =
      fieldLfppMetric ξ φ := Subtype.ext hφ
  rw [weylScale_smul, ←hEq, l6e_weylLfpp d ξ φ g hm u v]
  simp only [fieldLfpp, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)]

end HigherDimLQGMetric
