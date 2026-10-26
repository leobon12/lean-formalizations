import HigherDimLQGMetric.Locality.TruncInternal
import HigherDimLQGMetric.Metric.WeylBasic
import HigherDimLQGMetric.Sec4.Basic

/-!
# Deterministic Weyl comparison bridges

Internal LFPP distances on an open set inherit the usual pointwise density comparison.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace HigherDimLFPPAS.Bridge

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The internal metric of one continuous LFPP field is the Weyl reweighting of the internal
metric associated with a second field. -/
theorem fieldLfppMetric_internal_eq_weylScaleOn
    (ξ : ℝ) (φ ψ : C(Rd d, ℝ)) (V : Set (Rd d)) (hV : IsOpen V) (x y : Rd d) :
    (fieldLfppMetric ξ φ).internal V x y =
      weylScaleOn ξ (φ - ψ) (fieldLfppMetric ξ ψ) V x y := by
  let D := fieldLfppMetric ξ ψ
  have hDc : IsContinuousMetric (toCMapRd (fieldLfpp ξ ⇑ψ)) := by
    rw [show toCMapRd (fieldLfpp ξ ⇑ψ) = D.1 from by
      apply ContinuousMap.ext
      intro p
      exact toCMapRd_apply_of_continuous (continuous_fieldLfpp ψ.continuous) p]
    exact D.2
  have hDEq : (⟨toCMapRd (fieldLfpp ξ ⇑ψ), hDc⟩ : ContMetric d) = D := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    exact toCMapRd_apply_of_continuous (continuous_fieldLfpp ψ.continuous) p
  have hspec (z w : Rd d) :
      ENNReal.ofReal ((fieldLfppMetric ξ φ).1 (z,w)) =
        weylScale ξ (φ - ψ) D z w := by
    have hw := l6e_weylLfpp d ξ ψ (φ - ψ) hDc z w
    have hsum : (⇑ψ + ⇑(φ - ψ) : Rd d → ℝ) = ⇑φ := by
      funext q
      simp
    rw [hDEq] at hw
    rw [hsum, fieldLfppE_eq_ofReal_fieldLfpp φ.continuous] at hw
    simpa only [fieldLfppMetric_apply] using hw.symm
  rw [← weylScaleOn_eq_internal (fieldLfppMetric ξ φ) hspec hV]

/-- Density comparison for internal LFPP metrics. -/
theorem fieldLfppMetric_internal_density_compare
    (ξ s α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (φ ψ : C(Rd d, ℝ)) (V : Set (Rd d)) (hV : IsOpen V)
    (hbound : ∀ z ∈ V,
      |Real.log (α / β) + ξ * (φ z - ψ z)| ≤ s) (x y : Rd d) :
    ENNReal.ofReal α * (fieldLfppMetric ξ φ).internal V x y ≤
      ENNReal.ofReal (Real.exp s * β) * (fieldLfppMetric ξ ψ).internal V x y := by
  let D := fieldLfppMetric ξ ψ
  have hinternal := fieldLfppMetric_internal_eq_weylScaleOn ξ φ ψ V hV x y
  have hweight : ∀ z ∈ V,
      ξ * (φ z - ψ z) ≤ s - Real.log (α / β) := by
    intro z hz
    have hh := (abs_le.mp (hbound z hz)).2
    linarith
  have hscale := weylScaleOn_le_of_le (ξ := ξ) (f := φ - ψ) (D := D)
    (U := V) (z := x) (w := y) (b := s - Real.log (α / β)) hweight
  have hfactor : α * Real.exp (s - Real.log (α / β)) = Real.exp s * β := by
    rw [Real.exp_sub, Real.exp_log (div_pos hα hβ)]
    field_simp
  rw [hinternal]
  calc
    ENNReal.ofReal α * weylScaleOn ξ (φ - ψ) D V x y ≤
        ENNReal.ofReal α *
          (ENNReal.ofReal (Real.exp (s - Real.log (α / β))) * D.internal V x y) :=
      by gcongr
    _ = ENNReal.ofReal (Real.exp s * β) * D.internal V x y := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hα.le, hfactor]

end HigherDimLFPPAS.Bridge
