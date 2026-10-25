import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.Projection




 






set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

abbrev GeoInput := LSCMetric × (Path × (ℂ × ℂ))

private theorem jointEval_lsc :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) => p.1 p.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hq : Tendsto (fun n => (G n).2) atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hG
  exact (LSCMetric.tendsto_iff.mp hm).1 (fun n => (G n).2) p.2 hq

def GeoCode (p : GeoInput) : Prop :=
  p.2.1 0 = p.2.2.1 ∧ p.2.1 1 = p.2.2.2 ∧
  p.1 (p.2.2.1, p.2.2.2) < ∞ ∧
  ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
    p.1 (p.2.1 (projIcc 0 1 zero_le_one (s : ℝ)),
      p.2.1 (projIcc 0 1 zero_le_one (t : ℝ))) ≤
    ENNReal.ofReal ((t : ℝ) - s) * p.1 (p.2.2.1, p.2.2.2)

private theorem geo_endpoint_measurable :
    Measurable (fun p : GeoInput => p.1 (p.2.2.1, p.2.2.2)) := by
  have hu : Measurable (fun p : GeoInput => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : GeoInput => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact jointEval_lsc.measurable.comp (measurable_fst.prodMk (hu.prodMk hv))

private theorem geo_time_measurable (s t : ℚ) :
    Measurable (fun p : GeoInput =>
      p.1 (p.2.1 (projIcc 0 1 zero_le_one (s : ℝ)),
        p.2.1 (projIcc 0 1 zero_le_one (t : ℝ)))) := by
  have hs : Measurable (fun p : GeoInput =>
      p.2.1 (projIcc 0 1 zero_le_one (s : ℝ))) :=
    (continuous_eval_const _).measurable.comp (measurable_fst.comp measurable_snd)
  have ht : Measurable (fun p : GeoInput =>
      p.2.1 (projIcc 0 1 zero_le_one (t : ℝ))) :=
    (continuous_eval_const _).measurable.comp (measurable_fst.comp measurable_snd)
  exact jointEval_lsc.measurable.comp (measurable_fst.prodMk (hs.prodMk ht))

theorem geoCode_borel : MeasurableSet {p : GeoInput | GeoCode p} := by
  have h0 : Measurable (fun p : GeoInput => p.2.1 (0 : unitInterval)) :=
    (continuous_eval_const _).measurable.comp (measurable_fst.comp measurable_snd)
  have h1 : Measurable (fun p : GeoInput => p.2.1 (1 : unitInterval)) :=
    (continuous_eval_const _).measurable.comp (measurable_fst.comp measurable_snd)
  have hu : Measurable (fun p : GeoInput => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : GeoInput => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hforall : MeasurableSet {p : GeoInput | ∀ s t : ℚ,
      0 ≤ s → s ≤ t → t ≤ 1 →
        p.1 (p.2.1 (projIcc 0 1 zero_le_one (s : ℝ)),
          p.2.1 (projIcc 0 1 zero_le_one (t : ℝ))) ≤
        ENNReal.ofReal ((t : ℝ) - s) * p.1 (p.2.2.1, p.2.2.2)} := by
    have hi : MeasurableSet (⋂ s : ℚ, ⋂ t : ℚ,
        {p : GeoInput | 0 ≤ s → s ≤ t → t ≤ 1 →
          p.1 (p.2.1 (projIcc 0 1 zero_le_one (s : ℝ)),
            p.2.1 (projIcc 0 1 zero_le_one (t : ℝ))) ≤
          ENNReal.ofReal ((t : ℝ) - s) * p.1 (p.2.2.1, p.2.2.2)}) := by
      apply MeasurableSet.iInter
      intro s
      apply MeasurableSet.iInter
      intro t
      by_cases hst : 0 ≤ s ∧ s ≤ t ∧ t ≤ 1
      · have hle : MeasurableSet {p : GeoInput |
            p.1 (p.2.1 (projIcc 0 1 zero_le_one (s : ℝ)),
              p.2.1 (projIcc 0 1 zero_le_one (t : ℝ))) ≤
            ENNReal.ofReal ((t : ℝ) - s) * p.1 (p.2.2.1, p.2.2.2)} :=
          measurableSet_le (geo_time_measurable s t)
            (measurable_const.mul geo_endpoint_measurable)
        simpa only [hst.1, hst.2.1, hst.2.2, true_implies] using hle
      · have hwhole : {p : GeoInput | 0 ≤ s → s ≤ t → t ≤ 1 →
            p.1 (p.2.1 (projIcc 0 1 zero_le_one (s : ℝ)),
              p.2.1 (projIcc 0 1 zero_le_one (t : ℝ))) ≤
            ENNReal.ofReal ((t : ℝ) - s) * p.1 (p.2.2.1, p.2.2.2)} = Set.univ := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          intro hs ht htt
          exact False.elim (hst ⟨hs, ht, htt⟩)
        rw [hwhole]
        exact MeasurableSet.univ
    convert hi using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have hbase := ((measurableSet_eq_fun h0 hu).inter
    (measurableSet_eq_fun h1 hv)).inter
    ((measurableSet_lt geo_endpoint_measurable
      (measurable_const : Measurable (fun _ : GeoInput => (∞ : ENNReal)))).inter hforall)
  simpa only [GeoCode, Set.ofPred_and, Set.inter_assoc] using hbase

theorem geoTraceCode_borel {K E F : Set ℂ}
    (hK : IsClosed K) (hE : IsClosed E) (hF : IsClosed F) :
    MeasurableSet {p : GeoInput | GeoCode p ∧
      MapsTo p.2.1 Set.univ K ∧ p.2.2.1 ∈ E ∧ p.2.2.2 ∈ F} := by
  have htrace : MeasurableSet {P : Path | MapsTo P Set.univ K} :=
    (ContinuousMap.isClosed_setOfPred_mapsTo hK Set.univ).measurableSet
  have hmP : Measurable (fun p : GeoInput => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hu : Measurable (fun p : GeoInput => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : GeoInput => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact geoCode_borel.inter ((htrace.preimage hmP).inter
    ((hE.measurableSet.preimage hu).inter (hF.measurableSet.preimage hv)))

 


theorem geoTraceWitness_um (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) {K E F : Set ℂ}
    (hK : IsClosed K) (hE : IsClosed E) (hF : IsClosed F) :
    LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC | ∃ w : Path × (ℂ × ℂ),
        GeoCode (D g, w) ∧ MapsTo w.1 Set.univ K ∧
          w.2.1 ∈ E ∧ w.2.2 ∈ F} :=
  witnessProjection_um D hD (geoTraceCode_borel hK hE hF)


end SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes
