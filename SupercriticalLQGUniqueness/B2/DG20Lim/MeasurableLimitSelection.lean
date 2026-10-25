import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryLSCGlue

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_measurable_lscMetric_limit_with_property
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (G : ℕ → Ω' → LSCMetric) (hG : ∀ n, Measurable (G n))
    (Good : Ω' → LSCMetric → Prop)
    (hExists : ∀ᵐ ω ∂P', ∃ L : LSCMetric,
      Tendsto (fun n => G n ω) atTop (𝓝 L) ∧ Good ω L) :
    ∃ L : Ω' → LSCMetric, Measurable L ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => G n ω) atTop (𝓝 (L ω)) ∧ Good ω (L ω) := by
  classical
  let Lraw : Ω' → LSCMetric := fun ω =>
    if hω : ∃ L : LSCMetric,
        Tendsto (fun n => G n ω) atTop (𝓝 L) ∧ Good ω L
    then Classical.choose hω
    else B2.LscTop.euclideanLSCMetric
  have hraw : ∀ᵐ ω ∂P',
      Tendsto (fun n => G n ω) atTop (𝓝 (Lraw ω)) ∧ Good ω (Lraw ω) := by
    filter_upwards [hExists] with ω hω
    simpa only [Lraw, dif_pos hω] using (Classical.choose_spec hω)
  have hAE : AEMeasurable Lraw P' :=
    B2.LscTop.aemeasurable_of_tendsto_lscMetric_ae
      (fun n => (hG n).aemeasurable) (hraw.mono fun _ h => h.1)
  let L : Ω' → LSCMetric := hAE.mk Lraw
  refine ⟨L, hAE.measurable_mk, ?_⟩
  filter_upwards [hraw, hAE.ae_eq_mk] with ω hω heq
  simpa only [L, heq] using hω

end SupercriticalLQGUniqueness.B2.DG20Lim
