import SupercriticalLQGUniqueness.B2.PfeAxioms.PatchOverlapLength
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 

theorem len_eq_of_weyl_shifts_eqOn_patch
    (D E E' : LSCMetric) (ξ : ℝ) (f f' : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f D p)
    (hE' : ∀ p : ℂ × ℂ, E' p = weylScale ξ f' D p)
    (U : Set ℂ) (hff : EqOn f f' U)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hPU : ∀ t ∈ Icc a b, P t ∈ U) :
    E.len P a b = E'.len P a b := by
  have hlenE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f D
          (euclidForget D x, euclidForget D y)) (D.pt ∘ P) a b := by
    rw [E.len_eq_curveLength]
    calc
      LQGMetric.MetricGeometry.curveLength (E.pt ∘ P) a b =
          HigherDimLQGMetric.curveLengthWith (fun x y : D.Space => E (x, y))
            (D.pt ∘ P) a b :=
        (HigherDimLQGMetric.curveLengthWith_edist (E.pt ∘ P) a b).symm
      _ = _ := by congr 1; funext x y; exact hE (x, y)
  have hlenE' : E'.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f' D
          (euclidForget D x, euclidForget D y)) (D.pt ∘ P) a b := by
    rw [E'.len_eq_curveLength]
    calc
      LQGMetric.MetricGeometry.curveLength (E'.pt ∘ P) a b =
          HigherDimLQGMetric.curveLengthWith (fun x y : D.Space => E' (x, y))
            (D.pt ∘ P) a b :=
        (HigherDimLQGMetric.curveLengthWith_edist (E'.pt ∘ P) a b).symm
      _ = _ := by congr 1; funext x y; exact hE' (x, y)
  have hwf : HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f D
        (euclidForget D x, euclidForget D y)) (D.pt ∘ P) a b =
      HigherDimLQGMetric.weightedLength
        (fun x : D.Space => Real.exp (ξ * f (euclidForget D x)))
        (D.pt ∘ P) a b := by
    convert Uniqueness.Toolkit.WeylLength.weylCurveLength_eq_weightedLength
      D ξ f hforget hP using 1
    all_goals rfl
  have hwf' : HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f' D
        (euclidForget D x, euclidForget D y)) (D.pt ∘ P) a b =
      HigherDimLQGMetric.weightedLength
        (fun x : D.Space => Real.exp (ξ * f' (euclidForget D x)))
        (D.pt ∘ P) a b := by
    convert Uniqueness.Toolkit.WeylLength.weylCurveLength_eq_weightedLength
      D ξ f' hforget hP using 1
    all_goals rfl
  rw [hlenE, hlenE', hwf, hwf']
  apply HigherDimLQGMetric.weightedLength_congr_weight
  intro t ht
  exact congrArg (fun q : ℝ => Real.exp (ξ * q)) (hff (hPU t ht))

end SupercriticalLQGUniqueness.B2.PfeAxioms
