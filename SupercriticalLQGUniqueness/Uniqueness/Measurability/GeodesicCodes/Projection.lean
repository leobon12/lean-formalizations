import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.PathLength
import LQGMetric.Meas.UM
import LQGMetric.Field.StandardBorelRange




 




set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

 

theorem witnessProjection_um
    {W : Type*} [MeasurableSpace W] [StandardBorelSpace W]
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    {R : Set (LSCMetric × W)} (hR : MeasurableSet R) :
    LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC | ∃ w : W, (D g, w) ∈ R} := by
  have hp : Measurable (fun p : LQGMetric.DistC × W => (D p.1, p.2)) :=
    (hD.comp measurable_fst).prodMk measurable_snd
  exact LQGMetric.UMeasurableSet.setOf_exists (hR.preimage hp)

 

theorem witnessProjection_sample_nullMeasurable
    {W Ω : Type*} [MeasurableSpace W] [StandardBorelSpace W]
    [MeasurableSpace Ω]
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    {R : Set (LSCMetric × W)} (hR : MeasurableSet R)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (h : Ω → LQGMetric.DistC) (hh : AEMeasurable h μ) :
    NullMeasurableSet
      (h ⁻¹' {g : LQGMetric.DistC | ∃ w : W, (D g, w) ∈ R}) μ :=
  (witnessProjection_um D hD hR).nullMeasurableSet_preimage hh


end SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes
