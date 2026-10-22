import HigherDimLQGMetric.Trunc.Locality
import HigherDimLQGMetric.Trunc.LFPP
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import HigherDimLFPP.Exist.Sites

/-!
# Truncated convolution as an interior field observation

The truncated field on a region is measurable from the field restricted to any
open set containing its truncation neighborhoods.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A family of truncated convolution values is measurable from the field on `V`
when all its support balls lie in `V`. -/
theorem l7a_measurable_truncField_on {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (V : Opens (Rd d)) (W : Set (Rd d))
    (hWV : ∀ z ∈ W, closedBall z (Real.sqrt ε) ⊆ V)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h V]
      (fun ω => fun z : W => truncMollify κ ε (h ω) z.1) := by
  letI : MeasurableSpace Ω := fieldSigmaRd h V
  change Measurable (fun ω => fun z : W => truncMollify κ ε (h ω) z.1)
  exact measurable_pi_iff.mpr fun z =>
    l2c_measurable_truncMollify_fieldSigmaRd hd hκ hε z.1 V (hWV z.1 z.2) h

/-- The same observation bundled in the compact-open continuous-map space. -/
theorem l7a_measurable_truncCMap_on {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (V W : Opens (Rd d))
    (hWV : ∀ z ∈ W, closedBall z (Real.sqrt ε) ⊆ V)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h V]
      (fun ω => (⟨fun z : W => truncMollify κ ε (h ω) z.1,
        (l2c_continuous_truncMollify hd hκ hε (h ω)).comp continuous_subtype_val⟩ : C(W, ℝ))) := by
  letI : MeasurableSpace Ω := fieldSigmaRd h V
  change Measurable (fun ω => (⟨fun z : W => truncMollify κ ε (h ω) z.1,
    (l2c_continuous_truncMollify hd hκ hε (h ω)).comp continuous_subtype_val⟩ : C(W, ℝ)))
  exact ContinuousMap.measurable_iff_eval.mpr fun z =>
    l2c_measurable_truncMollify_fieldSigmaRd hd hκ hε z.1 V (hWV z.1 z.2) h

/-- A cutoff of the truncated field is a measurable whole-space continuous map.
The cutoff support must have its full truncation neighborhood inside `V`. -/
theorem l7a_measurable_cutoffTruncCMap {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (V : Opens (Rd d)) (f : C(Rd d, ℝ))
    (hfV : ∀ z ∈ Function.support f, closedBall z (Real.sqrt ε) ⊆ V)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) :
    Measurable[fieldSigmaRd h V]
      (fun ω => (⟨fun z => f z * truncMollify κ ε (h ω) z,
        f.continuous.mul (l2c_continuous_truncMollify hd hκ hε (h ω))⟩ : C(Rd d, ℝ))) := by
  letI : MeasurableSpace Ω := fieldSigmaRd h V
  change Measurable (fun ω => (⟨fun z => f z * truncMollify κ ε (h ω) z,
    f.continuous.mul (l2c_continuous_truncMollify hd hκ hε (h ω))⟩ : C(Rd d, ℝ)))
  apply ContinuousMap.measurable_iff_eval.mpr
  intro z
  by_cases hz : z ∈ Function.support f
  · exact measurable_const.mul
      (l2c_measurable_truncMollify_fieldSigmaRd hd hκ hε z V (hfV z hz) h)
  · have hzero : f z = 0 := by
      simp only [Function.mem_support] at hz
      exact not_ne_iff.mp hz
    simp only [ContinuousMap.coe_mk, hzero, zero_mul]
    exact measurable_const

/-- The truncated LFPP internal distance on `U` is an observation of the
field on `V` when a cutoff equal to one on `U` has enough room in `V`. -/
theorem l7a_measurable_truncLfppDistOn {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) (V U : Opens (Rd d))
    (f : C(Rd d, ℝ)) (hfU : ∀ z ∈ U, f z = 1)
    (hfV : ∀ z ∈ Function.support f, closedBall z (Real.sqrt ε) ⊆ V)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d) (x y : Rd d) :
    Measurable[fieldSigmaRd h V]
      (fun ω => HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε (h ω)) U x y) := by
  letI : MeasurableSpace Ω := fieldSigmaRd h V
  change Measurable
    (fun ω => HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε (h ω)) U x y)
  have htarget : Measurable (fun ω => HigherDimLFPP.lfppDistOn ξ
      (fun z => f z * truncMollify κ ε (h ω) z) U x y) := by
    apply HigherDimLFPP.measurable_lfppDistOn
      (H := fun z ω => f z * truncMollify κ ε (h ω) z)
      (fun ω => f.continuous.mul (l2c_continuous_truncMollify hd hκ hε (h ω)))
      ?_ U.isOpen ξ x y
    intro z
    by_cases hz : z ∈ Function.support f
    · exact measurable_const.mul
        (l2c_measurable_truncMollify_fieldSigmaRd hd hκ hε z V (hfV z hz) h)
    · have hzero : f z = 0 := by
        simp only [Function.mem_support] at hz
        exact not_ne_iff.mp hz
      simp only [hzero, zero_mul]
      exact measurable_const
  convert htarget using 1
  funext ω
  exact HigherDimLFPP.DGZ.lfppDistOn_congr
    (fun z hz => by simp only [hfU z hz, one_mul]) x y

end HigherDimLQGMetric
