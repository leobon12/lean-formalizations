import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.GeodesicBridge




 


set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private def diameterRatPoint (q : ℚ) : unitInterval :=
  projIcc 0 1 zero_le_one (q : ℝ)

private theorem diameterRatPoint_dense : DenseRange diameterRatPoint := by
  change DenseRange (projIcc 0 1 zero_le_one ∘ (fun q : ℚ => (q : ℝ)))
  exact (projIcc_surjective zero_le_one).denseRange.comp
    Rat.denseRange_cast continuous_projIcc

 
def PathDiameterCode (P : Measurability.GeodesicCodes.Path) (R : ℝ) : Prop :=
  ∀ q r : ℚ, dist (P (diameterRatPoint q)) (P (diameterRatPoint r)) ≤ R

theorem pathDiameterCode_measurable (R : ℝ) :
    MeasurableSet {P : Measurability.GeodesicCodes.Path | PathDiameterCode P R} := by
  have hi : MeasurableSet (⋂ q : ℚ, ⋂ r : ℚ,
      {P : Measurability.GeodesicCodes.Path |
        dist (P (diameterRatPoint q)) (P (diameterRatPoint r)) ≤ R}) := by
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro r
    have hq : Measurable (fun P : Measurability.GeodesicCodes.Path => P (diameterRatPoint q)) :=
      (continuous_eval_const _).measurable
    have hr : Measurable (fun P : Measurability.GeodesicCodes.Path => P (diameterRatPoint r)) :=
      (continuous_eval_const _).measurable
    exact measurableSet_le (hq.dist hr) measurable_const
  convert hi using 1
  ext P
  simp only [PathDiameterCode, Set.mem_ofPred_eq, Set.mem_iInter]

theorem pathDiameterCode_iff_diam_le (P : Measurability.GeodesicCodes.Path) (R : ℝ)
    (hR : 0 ≤ R) :
    PathDiameterCode P R ↔ Metric.diam (Set.range P) ≤ R := by
  constructor
  · intro h
    have hclosed : IsClosed {st : unitInterval × unitInterval |
        dist (P st.1) (P st.2) ≤ R} := by
      have hc : Continuous (fun st : unitInterval × unitInterval =>
          dist (P st.1) (P st.2)) :=
        (P.continuous.comp continuous_fst).dist
          (P.continuous.comp continuous_snd)
      exact isClosed_le hc continuous_const
    have hall : ∀ s t : unitInterval, dist (P s) (P t) ≤ R :=
      isClosed_property2
        (p := fun s t => dist (P s) (P t) ≤ R)
        diameterRatPoint_dense hclosed h
    apply Metric.diam_le_of_forall_dist_le hR
    intro x hx y hy
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    exact hall s t
  · intro h q r
    have hc : IsCompact (Set.range P) := by
      simpa only [Set.image_univ] using (isCompact_univ.image P.continuous)
    have hb : Bornology.IsBounded (Set.range P) := hc.isBounded
    exact (Metric.dist_le_diam_of_mem hb
      ⟨diameterRatPoint q, rfl⟩ ⟨diameterRatPoint r, rfl⟩).trans h

theorem pathDiameter_measurable (R : ℝ) (hR : 0 ≤ R) :
    MeasurableSet {P : Measurability.GeodesicCodes.Path | Metric.diam (Set.range P) ≤ R} := by
  convert pathDiameterCode_measurable R using 1
  ext P
  exact (pathDiameterCode_iff_diam_le P R hR).symm

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
