import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryLSCGlue
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteZeroCirclePoint
import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledRationalAgreement

 


set_option autoImplicit false
noncomputable section

open Filter Topology LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem rational_point_tendsto_of_zero_circle_agreement
    (y : ℕ → (CoordJ → ℝ) × RatCoords)
    (ylim : (CoordJ → ℝ) × RatCoords)
    (hconv : Tendsto y atTop (𝓝 ylim))
    (hrange : ∀ n,
      finiteCircleCoords (circleCoordsInv (y n).2.1) = (y n).2.1)
    (R : RData)
    (hacross : R.across = (fun O Q => ylim.2.1 (O, Q)))
    (hagree : ∀ Z W : RatCircle, Z.radius = 0 → W.radius = 0 →
      R.across Z W = R.DfromR Z.center W.center)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z)
    (u v : ℂ) (hu : B2.Iface.IsRationalPoint u)
    (hv : B2.Iface.IsRationalPoint v) :
    Tendsto (fun n => finiteMetricE (circleCoordsInv (y n).2.1) (u, v))
      atTop (𝓝 ((R.toLSCMetric htri).toLSCFun.1 (u, v))) := by
  obtain ⟨x, ycoord, rfl⟩ := hu
  obtain ⟨x', ycoord', rfl⟩ := hv
  let Z := RatCircle.point x ycoord
  let W := RatCircle.point x' ycoord'
  have hZ : Z.radius = 0 := rfl
  have hW : W.radius = 0 := rfl
  have hcentZ : Z.center = Complex.mk (x : ℝ) (ycoord : ℝ) := rfl
  have hcentW : W.center = Complex.mk (x' : ℝ) (ycoord' : ℝ) := rfl
  have hc : Tendsto (fun n => (y n).2.1 (Z, W)) atTop
      (𝓝 (ylim.2.1 (Z, W))) :=
    ((continuous_apply (Z, W)).comp
      (continuous_fst.comp continuous_snd)).tendsto _ |>.comp hconv
  have hfinite : ∀ n,
      finiteMetricE (circleCoordsInv (y n).2.1)
        (Complex.mk (x : ℝ) (ycoord : ℝ),
          Complex.mk (x' : ℝ) (ycoord' : ℝ)) =
        (((y n).2.1 (Z, W) : ℝ≥0∞) : EReal) := by
    intro n
    let D := circleCoordsInv (y n).2.1
    have hr := congrFun (hrange n) (Z, W)
    change ((ENNReal.ofReal (D.1 (Z.center, W.center)) : ℝ≥0∞) : EReal) = _
    rw [← D.edist_pt, ← finiteCircleCoords_zero_zero D Z W hZ hW, hr]
  have hseq : (fun n => finiteMetricE (circleCoordsInv (y n).2.1)
      (Complex.mk (x : ℝ) (ycoord : ℝ),
        Complex.mk (x' : ℝ) (ycoord' : ℝ))) =
      (fun n => (((y n).2.1 (Z, W) : ℝ≥0∞) : EReal)) := funext hfinite
  rw [hseq]
  have hlim : ylim.2.1 (Z, W) =
      R.DfromR (Complex.mk (x : ℝ) (ycoord : ℝ))
        (Complex.mk (x' : ℝ) (ycoord' : ℝ)) := by
    calc
      ylim.2.1 (Z, W) = R.across Z W := (congrFun (congrFun hacross Z) W).symm
      _ = R.DfromR Z.center W.center := hagree Z W hZ hW
      _ = _ := by rw [hcentZ, hcentW]
  change Tendsto (fun n => (((y n).2.1 (Z, W) : ℝ≥0∞) : EReal))
    atTop (𝓝 ((R.DfromR (Complex.mk (x : ℝ) (ycoord : ℝ))
      (Complex.mk (x' : ℝ) (ycoord' : ℝ)) : ℝ≥0∞) : EReal))
  rw [← hlim]
  exact (continuous_coe_ennreal_ereal.tendsto _).comp hc

end SupercriticalLQGUniqueness.B2.DG20Lim
