import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockF3FieldBorelV
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldBorel




 


set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC)

theorem measurableSet_blockRelation (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (Cmid0 : ℝ)
    (D E : DistC → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (hRad : 0 ≤ T.blockRadius) (hR : 0 < T.rho * T.r) :
    MeasurableSet {p : DistC × Objects.BlockWitness.BlockWitness T |
      Objects.BlockWitness.BlockRelation C T Ksh Cmid0 D E p} := by
  let X := DistC × Objects.BlockWitness.BlockWitness T
  let u : X → ℂ := fun p => p.2.1.1
  let v : X → ℂ := fun p => p.2.1.2
  let path : X → Measurability.GeodesicCodes.Path := fun p => p.2.2
  let d : X → LSCMetric := fun p => D p.1
  let e : X → LSCMetric := fun p => E p.1
  have hu : Measurable u := by fun_prop
  have hv : Measurable v := by fun_prop
  have hpath : Measurable path := by fun_prop
  have hd : Measurable d := hD.comp measurable_fst
  have he : Measurable e := hE.comp measurable_fst
  have hduv : Measurable (fun p : X => d p (u p, v p)) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (hd.prodMk (hu.prodMk hv))
  have heuv : Measurable (fun p : X => e p (u p, v p)) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (he.prodMk (hu.prodMk hv))
  have h1 : MeasurableSet {p : X | ‖u p‖ = T.alpha * (T.rho * T.r)} :=
    measurableSet_eq_fun hu.norm measurable_const
  have h2 : MeasurableSet {p : X | dist (u p) (Objects.Excursions.cU T) < T.blockRadius / 2} :=
    measurableSet_lt (hu.dist measurable_const) measurable_const
  have h3 : MeasurableSet {p : X | ‖v p‖ = T.rho * T.r} :=
    measurableSet_eq_fun hv.norm measurable_const
  have h4 : MeasurableSet {p : X | dist (v p) (Objects.Excursions.cV T) < T.blockRadius / 2} :=
    measurableSet_lt (hv.dist measurable_const) measurable_const
  have h5 : MeasurableSet {p : X |
      e p (u p,v p) ≤ ENNReal.ofReal Cmid0 * d p (u p,v p)} :=
    measurableSet_le heuv (measurable_const.mul hduv)
  have h6 : MeasurableSet {p : X | e p (u p,v p) < ⊤} :=
    measurableSet_lt heuv measurable_const
  have hGeoInput : Measurable (fun p : X =>
      Prod.mk (e p) (Prod.mk (path p) (Prod.mk (u p) (v p)))) :=
    he.prodMk (hpath.prodMk (hu.prodMk hv))
  have h7 : MeasurableSet {p : X |
      Measurability.GeodesicCodes.GeoCode (e p, (path p, (u p, v p)))} :=
    Measurability.GeodesicCodes.geoCode_borel.preimage hGeoInput
  have htrace : MeasurableSet {Q : Measurability.GeodesicCodes.Path |
      ∀ t, Q t ∈ closure (Objects.Excursions.blockShape T)} := by
    simpa only [Set.MapsTo, mem_univ, forall_true_left] using
      (ContinuousMap.isClosed_setOfPred_mapsTo isClosed_closure Set.univ).measurableSet
  have h8 : MeasurableSet {p : X |
      ∀ t, path p t ∈ closure (Objects.Excursions.blockShape T)} := htrace.preimage hpath
  have h9 : MeasurableSet {p : X |
      Objects.Shadow.circleOuter (Objects.Excursions.cU T) T.blockRadius.toNNReal 0
        (sphere (Objects.Excursions.cU T) T.blockRadius \
          Objects.Producer.goodSet (d p) (Objects.Excursions.cU T) p.2.1.1 T.blockRadius
            (C.lamConst * (e p (u p, v p)).toReal) p.2.1.1.property) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2)} :=
    measurableSet_le (measurable_block_f3u C T D E hD hE hRad) measurable_const
  have h10 : MeasurableSet {p : X |
      Objects.Shadow.circleOuter (Objects.Excursions.cV T) T.blockRadius.toNNReal 0
        (sphere (Objects.Excursions.cV T) T.blockRadius \
          Objects.Producer.goodSet (d p) (Objects.Excursions.cV T) p.2.1.2 T.blockRadius
            (C.lamConst * (e p (u p, v p)).toReal) p.2.1.2.property) ≤
        ENNReal.ofReal (C.lamConst * T.blockRadius / 2)} :=
    measurableSet_le (measurable_block_f3v C T D E hD hE hRad) measurable_const
  have h11 : MeasurableSet {p : X | Objects.Excursions.shield C T Ksh (d p)} :=
    (Objects.ShieldLocality.measurableSet_shield C T Ksh D hD hR).preimage measurable_fst
  have hAll := h1.inter (h2.inter (h3.inter (h4.inter (h5.inter
    (h6.inter (h7.inter (h8.inter (h9.inter (h10.inter h11)))))))))
  simpa only [Objects.BlockWitness.BlockRelation, X, u, v, path, d, e,
    Set.ofPred_and, Set.inter_assoc] using hAll

 

theorem blockRaw_um (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (Cmid0 : ℝ)
    (D E : DistC → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (hRad : 0 ≤ T.blockRadius) (hR : 0 < T.rho * T.r)
    (hn : ‖T.orientation‖ = 1) :
    LQGMetric.UMeasurableSet {g : DistC | Objects.Excursions.blockRaw C T Ksh Cmid0 D E g} := by
  have hProj : LQGMetric.UMeasurableSet
      {g : DistC | ∃ w : Objects.BlockWitness.BlockWitness T,
        Objects.BlockWitness.BlockRelation C T Ksh Cmid0 D E (g, w)} :=
    LQGMetric.UMeasurableSet.setOf_exists
      (measurableSet_blockRelation C T Ksh Cmid0 D E hD hE hRad hR)
  have hEq : {g : DistC | Objects.Excursions.blockRaw C T Ksh Cmid0 D E g} =
      {g : DistC | ∃ w : Objects.BlockWitness.BlockWitness T,
        Objects.BlockWitness.BlockRelation C T Ksh Cmid0 D E (g, w)} := by
    ext g
    exact Objects.BlockWitness.blockRaw_iff_projection C T Ksh Cmid0 D E hn hR g
  rw [hEq]
  exact hProj

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
