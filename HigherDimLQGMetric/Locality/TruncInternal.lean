import HigherDimLQGMetric.Locality.TruncField
import HigherDimLQGMetric.Weak.DetLFPPWeylUpper
import HigherDimLQGMetric.Metric.WeylMetric
import HigherDimLQGMetric.Limits.JointInternalMeas

/-!
# Local dependence of LFPP internal metrics on the weight

Port of the Weyl-locality argument for continuous LFPP fields. This lets the
truncated field be cut off outside the observed open set without changing an
internal metric on the inner domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Internal LFPP metrics agree when their continuous weights agree on the
open domain. -/
theorem l7a_fieldLfppMetric_internal_congr {d : ℕ} (ξ : ℝ)
    (φ ψ : C(Rd d, ℝ)) {U : Set (Rd d)} (hU : IsOpen U)
    (heq : ∀ x ∈ U, φ x = ψ x) (z w : Rd d) :
    (fieldLfppMetric ξ φ).internal U z w =
      (fieldLfppMetric ξ ψ).internal U z w := by
  let E := fieldLfppMetric ξ (0 : C(Rd d, ℝ))
  have hspec (f : C(Rd d, ℝ)) (x y : Rd d) :
      ENNReal.ofReal ((fieldLfppMetric ξ f).1 (x,y)) =
        weylScale ξ f E x y := by
    have hDc : IsContinuousMetric (toCMapRd (fieldLfpp ξ (0 : Rd d → ℝ))) := by
      rw [show toCMapRd (fieldLfpp ξ (0 : Rd d → ℝ)) = E.1 from by
        apply ContinuousMap.ext
        intro p
        exact toCMapRd_apply_of_continuous (continuous_fieldLfpp continuous_const) p]
      exact E.2
    have hw := l6e_weylLfpp d ξ 0 f hDc x y
    have hEq : (⟨toCMapRd (fieldLfpp ξ (⇑(0 : C(Rd d, ℝ)))), hDc⟩ : ContMetric d) = E := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro p
      exact toCMapRd_apply_of_continuous (continuous_fieldLfpp continuous_const) p
    rw [hEq] at hw
    have hf : ((⇑(0 : C(Rd d, ℝ)) : Rd d → ℝ) + ⇑f) = ⇑f := by
      funext z
      simp
    rw [hf, fieldLfppE_eq_ofReal_fieldLfpp f.continuous] at hw
    exact hw.symm
  calc
    (fieldLfppMetric ξ φ).internal U z w = weylScaleOn ξ φ E U z w :=
      (weylScaleOn_eq_internal (fieldLfppMetric ξ φ)
        (hspec φ) hU z w).symm
    _ = weylScaleOn ξ ψ E U z w :=
      weylScaleOn_congr (fun x hx => by rw [heq x hx])
    _ = (fieldLfppMetric ξ ψ).internal U z w :=
      weylScaleOn_eq_internal (fieldLfppMetric ξ ψ)
        (hspec ψ) hU z w

/-- The internal truncated LFPP metric on a connected open domain is
measurable from the field on a larger open set. -/
theorem l7a_measurable_truncInternalC {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ)
    (V U : TopologicalSpace.Opens (Rd d)) (hUc : IsPreconnected (U : Set (Rd d)))
    (f : C(Rd d, ℝ)) (hfU : ∀ z ∈ U, f z = 1)
    (hfV : ∀ z ∈ Function.support f, Metric.closedBall z (Real.sqrt ε) ⊆ V)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h V]
      (fun ω => internalC
        (fieldLfppMetric ξ ⟨truncMollify κ ε (h ω),
          l2c_continuous_truncMollify hd hκ hε (h ω)⟩)
        (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (h ω),
          l2c_continuous_truncMollify hd hκ hε (h ω)⟩)
        U.isOpen hUc) := by
  letI : MeasurableSpace Ω := fieldSigmaRd h V
  change Measurable (fun ω => internalC
    (fieldLfppMetric ξ ⟨truncMollify κ ε (h ω),
      l2c_continuous_truncMollify hd hκ hε (h ω)⟩)
    (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (h ω),
      l2c_continuous_truncMollify hd hκ hε (h ω)⟩) U.isOpen hUc)
  let F : Ω → C(Rd d, ℝ) := fun ω =>
    ⟨fun z => f z * truncMollify κ ε (h ω) z,
      f.continuous.mul (l2c_continuous_truncMollify hd hκ hε (h ω))⟩
  have hF : Measurable F := l7a_measurable_cutoffTruncCMap hd hκ hε V f hfV h
  have htarget : Measurable (fun ω => internalC (fieldLfppMetric ξ (F ω))
      (fieldLfppMetric_isLength ξ (F ω)) U.isOpen hUc) :=
    (l6c_measurable_fieldLfpp_internalC ξ U.isOpen hUc).comp hF
  convert htarget using 1
  funext ω
  apply ContinuousMap.ext
  rintro ⟨z, w⟩
  change ((fieldLfppMetric ξ
      (⟨truncMollify κ ε (h ω), l2c_continuous_truncMollify hd hκ hε (h ω)⟩)).internal
    U z.1 w.1).toReal = ((fieldLfppMetric ξ (F ω)).internal U z.1 w.1).toReal
  congr 1
  apply l7a_fieldLfppMetric_internal_congr ξ _ _ U.isOpen
  intro x hx
  change truncMollify κ ε (h ω) x = f x * truncMollify κ ε (h ω) x
  rw [hfU x hx, one_mul]

/-- Truncated internal LFPP metrics depend only on the field in the support
neighbourhood of the observed domain. -/
theorem l7a_truncInternalC_congr_of_restrictTo {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ)
    (V U : TopologicalSpace.Opens (Rd d)) (hUc : IsPreconnected (U : Set (Rd d)))
    (hUV : ∀ z ∈ U, Metric.closedBall z (Real.sqrt ε) ⊆ V)
    {g k : DistRd d} (heq : restrictTo V g = restrictTo V k) :
    internalC (fieldLfppMetric ξ ⟨truncMollify κ ε g,
        l2c_continuous_truncMollify hd hκ hε g⟩)
      (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε g,
        l2c_continuous_truncMollify hd hκ hε g⟩) U.isOpen hUc =
    internalC (fieldLfppMetric ξ ⟨truncMollify κ ε k,
        l2c_continuous_truncMollify hd hκ hε k⟩)
      (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε k,
        l2c_continuous_truncMollify hd hκ hε k⟩) U.isOpen hUc := by
  apply ContinuousMap.ext
  rintro ⟨z, w⟩
  change ((fieldLfppMetric ξ _).internal U z.1 w.1).toReal =
    ((fieldLfppMetric ξ _).internal U z.1 w.1).toReal
  congr 1
  apply l7a_fieldLfppMetric_internal_congr ξ _ _ U.isOpen
  intro x hx
  exact l2c_truncMollify_eq_of_restrictTo hd hκ hε x V (hUV x hx) heq

end HigherDimLQGMetric
