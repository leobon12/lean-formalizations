import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Circles
import SupercriticalLQGUniqueness.B2.Final.CouplingData
import SupercriticalLQGUniqueness.B2.DG20Lim.RData

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem ae_coupled_positiveCircle_tendsto
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → LQGMetric.DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → LQGMetric.DistC} {hN : ℕ → Ω' → LQGMetric.DistC}
    {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L) :
    ∀ᵐ ω ∂P', ∀ O O' : B2.DG20Lim.RatCircle,
      0 < O.radius → 0 < O'.radius →
      Tendsto (fun n => setDistance
        (normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))).1
        O.toSet O'.toSet) atTop
        (𝓝 (setDistance (L ω).1 O.toSet O'.toSet)) := by
  filter_upwards [hB.metric_tendsto, ae_all_iff.2 hSA] with ω hlim hsmall O O' hO hO'
  have hGlen : ∀ n,
      (normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))).IsLengthSpace :=
    fun n => isLengthSpace_normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))
  have hGforget : ∀ n, Continuous
      (euclidForget (normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))) :=
    fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric
      (ξ : ℝ) (m (e n)) _
  exact sphere_setDistance_tendsto_of_lsc hlim hGlen hGforget hsmall
    (Rat.cast_pos.mpr hO) (Rat.cast_pos.mpr hO')

end SupercriticalLQGUniqueness.B2.PfeWeyl
