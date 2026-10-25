import SupercriticalLQGUniqueness.B2.PfeAxioms.S2AroundLimit
import SupercriticalLQGUniqueness.B2.Final.CouplingData

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem ae_selfSmallAnnuli_of_coupledSmallAnnuli
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L) :
    ∀ᵐ ω ∂P', SelfSmallAnnuli (L ω) univ := by
  have hsmall : ∀ᵐ ω ∂P', ∀ j : ℕ, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
        (V (e n) (hN n ω))) (L ω)
      (Metric.closedBall 0 j) (Metric.ball 0 ((j : ℝ) + 1)) :=
    ae_all_iff.mpr hSA
  filter_upwards [hB.metric_tendsto, hsmall] with ω hG hS
  intro z _ hns δ hδ ρ hρ
  obtain ⟨j, hj⟩ := exists_nat_gt ‖z‖
  exact (selfSmallAnnuli_of_smallAnnulusCosts hG (hS j)) z
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hj.le)
    hns δ hδ ρ hρ

 

theorem ae_selfSmallAnnuli_of_coupling
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    {Φ : DistC → LSCMetric} (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, SelfSmallAnnuli (Φ (h ω)) univ := by
  have hTarget : ∀ᵐ ω ∂P', SelfSmallAnnuli (Φ (h' ω)) univ := by
    filter_upwards [ae_selfSmallAnnuli_of_coupledSmallAnnuli hB hSA, hII]
      with ω hS hEq
    rwa [hEq] at hS
  have hLaw : P.map h = P'.map h' :=
    (normGFFLaw_eq_of_normalized P h hh).symm.trans
      (normGFFLaw_eq_of_normalized P' h' hB.limit_field)
  exact ae_field_property_of_standardBorel_coupling P P' h h'
    hh.1.measurable hB.limit_field.1.measurable hLaw
    (fun g => SelfSmallAnnuli (Φ g) univ) hTarget

end SupercriticalLQGUniqueness.B2.PfeAxioms
