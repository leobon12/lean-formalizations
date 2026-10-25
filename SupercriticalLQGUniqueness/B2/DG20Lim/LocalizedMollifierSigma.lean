import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedConstShift
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedRatAnnulusLocality
import LQGMetric.Papers.GM.S2.SpatialIndepCirc

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem measurable_locMollify_centeredRatAnnulus_fieldSigma
    {Ω : Type} [MeasurableSpace Ω] (Y : Ω → DistC)
    (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 2)
    (z : (centeredRatAnnulus x y r hr).toSet) :
    Measurable[fieldSigma Y (bufferedCenteredAnnulus x y r)]
      (fun ω => locMollify (ε : ℝ) ε.property (Y ω) z) := by
  apply LQGMetric.GM.measurable_pair_fieldSigma Y
  exact (tsupport_locTest_subset (ε : ℝ) ε.property z).trans
    (centeredRatAnnulus_locSupport x y r hr ε hεr z z.property)

theorem measurable_locMollify_restrictedAnnulus_fieldSigma
    {Ω : Type} [MeasurableSpace Ω] (Y : Ω → DistC)
    (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 2) :
    Measurable[fieldSigma Y (bufferedCenteredAnnulus x y r)]
      (fun ω (z : (centeredRatAnnulus x y r hr).toSet) =>
        locMollify (ε : ℝ) ε.property (Y ω) z) := by
  letI : MeasurableSpace Ω := fieldSigma Y (bufferedCenteredAnnulus x y r)
  apply measurable_pi_iff.mpr
  intro z
  exact measurable_locMollify_centeredRatAnnulus_fieldSigma Y ε x y r hr hεr z

end SupercriticalLQGUniqueness.B2.DG20Lim
