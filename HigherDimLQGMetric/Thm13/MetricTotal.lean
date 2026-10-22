import HigherDimLQGMetric.Thm13.DenseExtension
import HigherDimLQGMetric.Select.MetricBorel

/-!
# Total measurable conversion to continuous metrics

The continuous metric locus is Borel. A continuous two-point function on that
locus is kept; off it, the Euclidean metric supplies a fixed value.
Port of the `toContMetric` packaging in `LQGMetric.Papers.DFGPS.T12P1A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The Euclidean metric, bundled as a continuous metric. -/
def l8_euclidMetric : ContMetric d :=
  ⟨⟨fun p => dist p.1 p.2, continuous_dist.comp (continuous_fst.prodMk continuous_snd)⟩,
    { self_eq_zero := fun x => dist_self x
      eq_of_eq_zero := fun x y h => dist_eq_zero.mp h
      symm := fun x y => dist_comm x y
      triangle := fun x y z => dist_triangle x y z
      euclidean_of_small := fun x ε hε =>
        ⟨ε, hε, fun y hy => by
          change dist x y < ε at hy
          simpa only [dist_eq_norm] using hy⟩ }⟩

open Classical in
/-- Keep a continuous metric, with a Euclidean fallback off the Borel metric locus. -/
def l8_toContMetric (F : C(Rd d × Rd d, ℝ)) : ContMetric d :=
  if hF : IsContinuousMetric F then ⟨F, hF⟩ else l8_euclidMetric

theorem l8_toContMetric_coe (D : ContMetric d) : l8_toContMetric D.1 = D := by
  apply Subtype.ext
  simp only [l8_toContMetric, dite_eq_left D.2]

theorem l8_measurable_toContMetric :
    Measurable (l8_toContMetric (d := d)) := by
  classical
  have h1 : Measurable fun F : C(Rd d × Rd d, ℝ) => (l8_toContMetric F).1 := by
    have e : (fun F : C(Rd d × Rd d, ℝ) => (l8_toContMetric F).1) =
        {F : C(Rd d × Rd d, ℝ) | IsContinuousMetric F}.piecewise id
          (fun _ => (l8_euclidMetric (d := d)).1) := by
      funext F
      by_cases hF : IsContinuousMetric F
      · simp [l8_toContMetric, hF]
      · simp [l8_toContMetric, hF]
    rw [e]
    exact Measurable.piecewise (measurableSet_isContinuousMetric_select d)
      measurable_id measurable_const
  exact h1.subtype_mk

end HigherDimLQGMetric
