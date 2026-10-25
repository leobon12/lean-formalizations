import SupercriticalLQGUniqueness.B2.PfeLocal.L6Final
import SupercriticalLQGUniqueness.B2.Final.OpenInputs
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeOfInputs

 




















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC normGFFLaw heatMollify)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
theorem l6SmallAnnuli_of_coupledSmallAnnuli {ξ : Set.Ioi (0 : ℝ)}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (h : Final.CoupledSmallAnnuli ξ m e V P' hN L) : Inputs.L6SmallAnnuli ξ m V e P' hN L :=
  h

 
theorem l6_obsLocality_of_couplingData {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L) : Inputs.L5ObsLocality P' h' L :=
  l6_obsLocality ξ m V hB.heat_measurable hB.heat_ae e hB.scale_tendsto P' h' hB.limit_field hN
    hB.field_measurable hB.field_law (DG20Lim.ae_pairing_tendsto_of_ae_tendsto hB.field_tendsto)
    L hB.limit_measurable hB.metric_tendsto (l6SmallAnnuli_of_coupledSmallAnnuli hSA)

 
theorem pfeL5ObsLocality_proved : Final.PfeL5ObsLocality := by
  intro _ ξ Q m e c V Ω' _ _ _ P' _ h' hN L hB hSA _
  exact l6_obsLocality_of_couplingData hB hSA

end SupercriticalLQGUniqueness.B2.PfeLocal
