import SupercriticalLQGUniqueness.B2.Median.Scale
import SupercriticalLQGUniqueness.Frozen.LSCMetricInternalSetDist
import SupercriticalLQGUniqueness.Frozen.LfppCrossingLength
import SupercriticalLQGUniqueness.B2.LscTop.LFPP
import LQGMetric.LFPP.Length

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric (leftSide rightSide)

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

def crossingInf (d : LSCMetric) : ℝ≥0∞ :=
  compactPathInf d unitSquare leftSide rightSide

theorem compactPathInf_eq_internalSetDist (d : LSCMetric) (K A B : Set ℂ) :
    compactPathInf d K A B =
      d.internalSetDist K (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) := by
  apply le_antisymm
  · unfold LSCMetric.internalSetDist
    refine le_iInf fun x => le_iInf fun hx => le_iInf fun y =>
      le_iInf fun hy => ?_
    unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hK => le_iInf fun hA =>
      le_iInf fun hB => ?_
    exact compactPathInf_le_of_curve d K A B P a b hP hK
      (hA ▸ hx) (hB ▸ hy)
  · unfold compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hK => le_iInf fun hA =>
      le_iInf fun hB => ?_
    let x : K := ⟨P a, hK a (left_mem_Icc.mpr hP.1)⟩
    let y : K := ⟨P b, hK b (right_mem_Icc.mpr hP.1)⟩
    have hx : x ∈ Subtype.val ⁻¹' A := hA
    have hy : y ∈ Subtype.val ⁻¹' B := hB
    calc
      d.internalSetDist K (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B)
          ≤ d.internal K (x, y) := by
            unfold LSCMetric.internalSetDist
            exact iInf_le_of_le x <| iInf_le_of_le hx <|
              iInf_le_of_le y <| iInf_le_of_le hy le_rfl
      _ ≤ d.len P a b := by
        unfold LSCMetric.internal
        exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
          iInf_le_of_le hP <| iInf_le_of_le hK <|
          iInf_le_of_le (show P a = (x : ℂ) from rfl) <|
          iInf_le_of_le (show P b = (y : ℂ) from rfl) le_rfl

theorem crossingInf_eq_internalSetDist (d : LSCMetric) :
    crossingInf d =
      d.internalSetDist unitSquare (Subtype.val ⁻¹' leftSide)
        (Subtype.val ⁻¹' rightSide) :=
  compactPathInf_eq_internalSetDist d unitSquare leftSide rightSide

end SupercriticalLQGUniqueness.B2.Median
