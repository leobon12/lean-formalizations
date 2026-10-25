import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.HCodeSource
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.CircleAverageBorel
import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.Projection




 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

abbrev HWitness := (Measurability.GeodesicCodes.Path × (ℂ × ℂ)) × ℝ

private def circleGraphMap (p : LQGMetric.DistC × HWitness) :
    LQGMetric.DistC × ℝ := (p.1, p.2.2)

private theorem circleGraphMap_measurable : Measurable circleGraphMap := by
  have hc : Measurable (fun p : LQGMetric.DistC × HWitness => p.2.2) :=
    measurable_snd.comp measurable_snd
  exact measurable_fst.prodMk hc

private def fieldHMap (D D' : LQGMetric.DistC → LSCMetric)
    (p : LQGMetric.DistC × HWitness) : HInput :=
  ((D p.1, D' p.1), p.2)

private theorem fieldHMap_measurable (D D' : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D') :
    Measurable (fieldHMap D D') := by
  have hleft : Measurable (fun p : LQGMetric.DistC × HWitness => D p.1) :=
    hD.comp measurable_fst
  have hright : Measurable (fun p : LQGMetric.DistC × HWitness => D' p.1) :=
    hD'.comp measurable_fst
  exact (hleft.prodMk hright).prodMk measurable_snd

def FieldHRelation (D D' : LQGMetric.DistC → LSCMetric)
    (ξ Qpar : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ))
    (swap : Bool) (p : LQGMetric.DistC × HWitness) : Prop :=
  IsCircleAverage p.1 r 0 p.2.2 ∧
    HCode ξ Qpar r a C θ swap (fieldHMap D D' p)

theorem fieldHRelation_measurable (D D' : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    (ξ Qpar : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ))
    (swap : Bool) :
    MeasurableSet {p : LQGMetric.DistC × HWitness |
      FieldHRelation D D' ξ Qpar r a C θ swap p} := by
  have hc := (circleAverageGraph_measurable r 0).preimage
    circleGraphMap_measurable
  have hh := (hCode_measurable ξ Qpar r a C θ swap).preimage
    (fieldHMap_measurable D D' hD hD')
  exact hc.inter hh

theorem HEvent_iff_projection (D D' : LQGMetric.DistC → LSCMetric)
    (ξ Qpar : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ))
    (g : LQGMetric.DistC) :
    OptimalConstants.Ratios.HEvent D D' ξ Qpar r a C θ g ↔
      ∃ w : HWitness,
        FieldHRelation D D' ξ Qpar r a C θ false (g, w) := by
  constructor
  · rintro ⟨c, hc, hH⟩
    obtain ⟨P, u, v, hcode⟩ :=
      (H_iff_exists_HCode (D g) (D' g) ξ Qpar r a C θ c).mp hH
    exact ⟨((P, (u, v)), c), hc, hcode⟩
  · rintro ⟨⟨⟨P, ⟨u, v⟩⟩, c⟩, hc, hcode⟩
    exact ⟨c, hc, (H_iff_exists_HCode (D g) (D' g)
      ξ Qpar r a C θ c).mpr ⟨P, u, v, hcode⟩⟩

theorem HtildeEvent_iff_projection (D D' : LQGMetric.DistC → LSCMetric)
    (ξ Qpar : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ))
    (g : LQGMetric.DistC) :
    OptimalConstants.Ratios.HtildeEvent D D' ξ Qpar r a C θ g ↔
      ∃ w : HWitness,
        FieldHRelation D D' ξ Qpar r a C θ true (g, w) := by
  constructor
  · rintro ⟨c, hc, hH⟩
    obtain ⟨P, u, v, hcode⟩ :=
      (Htilde_iff_exists_HCode (D g) (D' g) ξ Qpar r a C θ c).mp hH
    exact ⟨((P, (u, v)), c), hc, hcode⟩
  · rintro ⟨⟨⟨P, ⟨u, v⟩⟩, c⟩, hc, hcode⟩
    exact ⟨c, hc, (Htilde_iff_exists_HCode (D g) (D' g)
      ξ Qpar r a C θ c).mpr ⟨P, u, v, hcode⟩⟩

theorem HEvent_um (D D' : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    (ξ Qpar : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC | OptimalConstants.Ratios.HEvent D D' ξ Qpar r a C θ g} := by
  have hh := LQGMetric.UMeasurableSet.setOf_exists
    (fieldHRelation_measurable D D' hD hD' ξ Qpar r a C θ false)
  convert hh using 1
  ext g
  exact HEvent_iff_projection D D' ξ Qpar r a C θ g

theorem HtildeEvent_um (D D' : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (hD' : Measurable D')
    (ξ Qpar : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC | OptimalConstants.Ratios.HtildeEvent D D' ξ Qpar r a C θ g} := by
  have hh := LQGMetric.UMeasurableSet.setOf_exists
    (fieldHRelation_measurable D D' hD hD' ξ Qpar r a C θ true)
  convert hh using 1
  ext g
  exact HtildeEvent_iff_projection D D' ξ Qpar r a C θ g

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
