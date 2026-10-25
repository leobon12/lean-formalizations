import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VCoupledCrossing
import SupercriticalLQGUniqueness.B2.PfeLocal.L1Limit
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Port
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeOfInputs

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem exists_subseq_ae_coupled_circleAvg
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => circleAvg (hN (ψ n) ω) r z)
        atTop (𝓝 (circleAvg (h' ω) r z)) := by
  have hpair := B2.DG20Lim.ae_pairing_tendsto_of_ae_tendsto hB.field_tendsto
  have hprob (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => P' {ω | δ ≤
        |circleAvg (hN n ω) r z - circleAvg (h' ω) r z|}) atTop (𝓝 0) := by
    have ht := PfeLocal.l1_circleAvg_tendsto_prob P' h' hB.limit_field
      hN hB.field_measurable hB.field_law hpair z r.property (η := δ / 2)
      (by positivity)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun n => zero_le)
    intro n
    apply measure_mono
    intro ω hω
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) hω
  obtain ⟨ψ, hψ, hae⟩ := PfeLocal.l6_exists_subseq_ae
    (P := P') (E := fun n ω =>
      circleAvg (hN n ω) r z - circleAvg (h' ω) r z) hprob
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hae] with ω hω
  have h := hω.add (tendsto_const_nhds (x := circleAvg (h' ω) r z))
  simpa only [sub_add_cancel, zero_add] using h

end SupercriticalLQGUniqueness.B2.PfeAxioms
