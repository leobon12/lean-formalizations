import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TInputs
import SupercriticalLQGUniqueness.B2.PfeWeyl.R68CircCoupled
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircFinal

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem coupledAllRationalCircles_of_coords
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → LQGMetric.DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → LQGMetric.DistC} {hN : ℕ → Ω' → LQGMetric.DistC}
    {L : Ω' → LSCMetric}
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate')
    (hPos : DG20ExponentPositive)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hZ : Final.CoupledRatCoords ξ m e V P' hN L) :
    CoupledAllRationalCircles ξ m e V P' hN L := by
  have hp := ae_coupled_positiveCircle_tendsto hB hSA
  have hz := PfeAxioms.coupled_circle_tendsto_of_coords hS4 hPerc hPos hB hZ
  filter_upwards [hp, hz] with ω hpω hzω O O' hO hO'
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  obtain ⟨x', y', r', hr', rfl⟩ := hO'
  let A : B2.DG20Lim.RatCircle := ⟨x, y, r, hr⟩
  let B : B2.DG20Lim.RatCircle := ⟨x', y', r', hr'⟩
  by_cases hrr : 0 < r ∧ 0 < r'
  · simpa only [A, B, B2.DG20Lim.RatCircle.toSet,
      B2.DG20Lim.RatCircle.center] using hpω A B hrr.1 hrr.2
  · simpa only [A, B, B2.DG20Lim.RatCircle.toSet,
      B2.DG20Lim.RatCircle.center] using hzω A B

end SupercriticalLQGUniqueness.B2.PfeWeyl
