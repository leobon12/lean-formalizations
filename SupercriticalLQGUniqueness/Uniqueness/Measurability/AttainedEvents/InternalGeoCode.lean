import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.GeodesicBridge
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.InternalLength
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.AttainedEvent




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private def ambientPath {K : Set ℂ} (P : InternalPath K) : Measurability.GeodesicCodes.Path :=
  ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ P

private theorem ambientPath_continuous {K : Set ℂ} :
    Continuous (ambientPath (K := K)) := by
  let ι : C(K, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hc : Continuous (ContinuousMap.comp ι : InternalPath K → Measurability.GeodesicCodes.Path) :=
    ContinuousMap.continuous_postcomp ι
  exact hc

private def internalEndpointCost (K : Set ℂ)
    (p : LSCMetric × InternalPath K) : ENNReal :=
  p.1.internal K (p.2 0, p.2 1)

private theorem internalEndpointCost_measurable {K : Set ℂ}
    (hK : IsCompact K) :
    Measurable (internalEndpointCost K) := by
  let f : LSCMetric × (K × K) → ENNReal :=
    fun q => q.1.internal K (q.2.1, q.2.2)
  let h : LSCMetric × InternalPath K → LSCMetric × (K × K) :=
    fun p => (p.1, (p.2 0, p.2 1))
  have h0 : Measurable (fun p : LSCMetric × InternalPath K => p.2 0) :=
    (continuous_eval_const 0).measurable.comp measurable_snd
  have h1 : Measurable (fun p : LSCMetric × InternalPath K => p.2 1) :=
    (continuous_eval_const 1).measurable.comp measurable_snd
  have hh : Measurable h := measurable_fst.prodMk (h0.prodMk h1)
  have hf : Measurable f := (TwoScale.S36Events.internal_compact_joint_lsc hK).measurable
  have hcomp : Measurable (f ∘ h) := hf.comp hh
  exact hcomp

private def internalTimeCost (K : Set ℂ) (s t : ℚ)
    (p : LSCMetric × InternalPath K) : ENNReal :=
  p.1 ((p.2 (projIcc 0 1 zero_le_one (s : ℝ)) : ℂ),
       (p.2 (projIcc 0 1 zero_le_one (t : ℝ)) : ℂ))

private theorem internalTimeCost_measurable (K : Set ℂ) (s t : ℚ) :
    Measurable (internalTimeCost K s t) := by
  let h : LSCMetric × InternalPath K → LSCMetric × (ℂ × ℂ) :=
    fun p => (p.1,
      ((p.2 (projIcc 0 1 zero_le_one (s : ℝ)) : ℂ),
       (p.2 (projIcc 0 1 zero_le_one (t : ℝ)) : ℂ)))
  have hs : Measurable (fun p : LSCMetric × InternalPath K =>
      (p.2 (projIcc 0 1 zero_le_one (s : ℝ)) : ℂ)) :=
    (continuous_subtype_val.comp (continuous_eval_const _)).measurable.comp measurable_snd
  have ht : Measurable (fun p : LSCMetric × InternalPath K =>
      (p.2 (projIcc 0 1 zero_le_one (t : ℝ)) : ℂ)) :=
    (continuous_subtype_val.comp (continuous_eval_const _)).measurable.comp measurable_snd
  have hh : Measurable h := measurable_fst.prodMk (hs.prodMk ht)
  exact TwoScale.S36Events.jointEval_lsc.measurable.comp hh

 

def InternalGeoCode (K : Set ℂ) (p : LSCMetric × InternalPath K) : Prop :=
  internalEndpointCost K p < ⊤ ∧
  p.1.len (Measurability.GeodesicCodes.pathReal (ambientPath p.2)) 0 1 = internalEndpointCost K p ∧
  ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
    internalTimeCost K s t p ≤
      ENNReal.ofReal ((t : ℝ) - s) * internalEndpointCost K p

attribute [local irreducible] internalEndpointCost internalTimeCost ambientPath InternalGeoCode

theorem internalGeoCode_measurable {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {p : LSCMetric × InternalPath K | InternalGeoCode K p} := by
  have hT : Measurable (internalEndpointCost K) :=
    internalEndpointCost_measurable hK
  have hP : Measurable (fun p : LSCMetric × InternalPath K =>
      ambientPath p.2) := ambientPath_continuous.measurable.comp measurable_snd
  have hLen : Measurable (fun p : LSCMetric × InternalPath K =>
      p.1.len (Measurability.GeodesicCodes.pathReal (ambientPath p.2)) 0 1) :=
    Measurability.GeodesicCodes.length_joint_measurable.comp (measurable_fst.prodMk hP)
  have hForall : MeasurableSet {p : LSCMetric × InternalPath K |
      ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
      internalTimeCost K s t p ≤
        ENNReal.ofReal ((t : ℝ) - s) * internalEndpointCost K p} := by
    have hi : MeasurableSet (⋂ s : ℚ, ⋂ t : ℚ,
        {p : LSCMetric × InternalPath K |
          0 ≤ s → s ≤ t → t ≤ 1 →
          internalTimeCost K s t p ≤
            ENNReal.ofReal ((t : ℝ) - s) * internalEndpointCost K p}) := by
      apply MeasurableSet.iInter
      intro s
      apply MeasurableSet.iInter
      intro t
      by_cases hst : 0 ≤ s ∧ s ≤ t ∧ t ≤ 1
      · have hle : MeasurableSet {p : LSCMetric × InternalPath K |
            internalTimeCost K s t p ≤
              ENNReal.ofReal ((t : ℝ) - s) * internalEndpointCost K p} := by
          convert (measurableSet_le (internalTimeCost_measurable K s t)
            (measurable_const.mul hT)) using 1
          ext p
          rfl
        simpa only [hst.1, hst.2.1, hst.2.2, true_implies] using hle
      · have hwhole : {p : LSCMetric × InternalPath K |
            0 ≤ s → s ≤ t → t ≤ 1 →
            internalTimeCost K s t p ≤
              ENNReal.ofReal ((t : ℝ) - s) * internalEndpointCost K p} = univ := by
          ext p
          simp only [mem_ofPred_eq, mem_univ, iff_true]
          intro hs ht htt
          exact False.elim (hst ⟨hs, ht, htt⟩)
        rw [hwhole]
        exact MeasurableSet.univ
    convert hi using 1
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
  have hBase := ((measurableSet_lt hT
    (measurable_const : Measurable (fun _ : LSCMetric × InternalPath K => (⊤ : ENNReal)))).inter
    (measurableSet_eq_fun hLen hT)).inter hForall
  convert hBase using 1
  ext p
  simp only [InternalGeoCode, mem_ofPred_eq, mem_inter_iff]
  exact and_assoc.symm

 

theorem internalGeoCode_isCurve {K : Set ℂ} (D : LSCMetric)
    (P : InternalPath K) (h : InternalGeoCode K (D, P)) :
    D.IsCurve (Measurability.GeodesicCodes.pathReal (ambientPath P)) 0 1 ∧
      D.len (Measurability.GeodesicCodes.pathReal (ambientPath P)) 0 1 =
        D.internal K (P 0, P 1) := by
  unfold InternalGeoCode at h
  rcases h with ⟨hFin, hLen, hSpeed⟩
  unfold internalEndpointCost at hFin hLen hSpeed
  unfold internalTimeCost at hSpeed
  have hT : D.internal K (P 0, P 1) ≠ ⊤ := hFin.ne
  have hBound : ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
      D ((ambientPath P) (projIcc 0 1 zero_le_one (s : ℝ)),
         (ambientPath P) (projIcc 0 1 zero_le_one (t : ℝ))) ≤
      ENNReal.ofReal ((t : ℝ) - s) * D.internal K (P 0, P 1) := by
    intro s t hs hst ht
    unfold ambientPath
    exact hSpeed s t hs hst ht
  have hC := rationalSpeed_isCurve_length_le D (ambientPath P)
    (D.internal K (P 0, P 1)) hT hBound
  exact ⟨hC.1, hLen⟩

 

theorem exists_internalGeoCode_of_source {K : Set ℂ} (hK : IsCompact K)
    (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ)
    (hCurve : D.IsCurve P a b) (hTrace : P '' Icc a b ⊆ K)
    (hu : P a ∈ K) (hv : P b ∈ K)
    (hLen : D.len P a b = D.internal K (⟨P a, hu⟩, ⟨P b, hv⟩))
    (hFin : D.len P a b < ⊤) :
    ∃ Q : InternalPath K, InternalGeoCode K (D, Q) ∧
      (Q 0 : ℂ) = P a ∧ (Q 1 : ℂ) = P b ∧
      ∀ t, (Q t : ℂ) ∈ P '' Icc a b := by
  obtain ⟨γ, hγlen, hγtrace, hγlip⟩ :=
    Toolkit.CompactPathInfimum.exists_lipschitz_reparam D P hCurve hFin.ne (Set.Subset.rfl)
  have hγtraceK (t : unitInterval) : (γ t : ℂ) ∈ K :=
    hTrace (hγtrace t)
  have hγcurve : D.IsCurve (fun t : ℝ => (γ.extend t : ℂ)) 0 1 :=
    ⟨zero_le_one, γ.continuous_extend.continuousOn⟩
  have hγtrace' : (fun t : ℝ => (γ.extend t : ℂ)) '' Icc (0 : ℝ) 1 ⊆ K := by
    rintro y ⟨t, ht, rfl⟩
    change (γ.extend t : ℂ) ∈ K
    rw [Path.extend_apply γ ht]
    exact hγtraceK ⟨t, ht⟩
  have hEuc : @ContinuousOn ℝ ℂ _
      (PseudoMetricSpace.toUniformSpace.toTopologicalSpace)
      (fun t : ℝ => (γ.extend t : ℂ)) (Icc 0 1) :=
    Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace D _ hγcurve hK hγtrace'
  have hγcont : @Continuous unitInterval ℂ _
      (PseudoMetricSpace.toUniformSpace.toTopologicalSpace)
      (fun t : unitInterval => (γ t : ℂ)) := by
    have hc : @Continuous unitInterval ℂ _
        (PseudoMetricSpace.toUniformSpace.toTopologicalSpace)
        (fun t : unitInterval => (γ.extend (t : ℝ) : ℂ)) :=
      continuousOn_iff_continuous_domRestrict.mp hEuc
    have heq : (fun t : unitInterval => (γ t : ℂ)) =
        (fun t : unitInterval => (γ.extend (t : ℝ) : ℂ)) := by
      funext t
      exact (Path.extend_extends' γ t).symm
    rw [heq]
    exact hc
  let Q : InternalPath K := ⟨fun t => ⟨(γ t : ℂ), hγtraceK t⟩,
    Continuous.subtype_mk hγcont hγtraceK⟩
  have hQ0 : (Q 0 : ℂ) = P a := by
    change (γ 0 : ℂ) = P a
    exact γ.source
  have hQ1 : (Q 1 : ℂ) = P b := by
    change (γ 1 : ℂ) = P b
    exact γ.target
  have hT : D.internal K (Q 0, Q 1) = D.len P a b := by
    have he0 : Q 0 = ⟨P a, hu⟩ := Subtype.ext hQ0
    have he1 : Q 1 = ⟨P b, hv⟩ := Subtype.ext hQ1
    rw [he0, he1, ← hLen]
  have hQlip : LipschitzWith (D.len P a b).toNNReal γ := hγlip
  refine ⟨Q, ?_, hQ0, hQ1, ?_⟩
  · unfold InternalGeoCode
    unfold internalEndpointCost
    refine ⟨hT ▸ hFin, ?_, ?_⟩
    · calc
        D.len (Measurability.GeodesicCodes.pathReal (ambientPath Q)) 0 1 =
            LQGMetric.MetricGeometry.pathLength γ := by
          unfold LSCMetric.len LQGMetric.MetricGeometry.pathLength
          apply LQGMetric.MetricGeometry.curveLength_congr
          intro t ht
          change (D.pt ((Measurability.GeodesicCodes.pathReal (ambientPath Q)) t)) = γ.extend t
          unfold Measurability.GeodesicCodes.pathReal
          rw [projIcc_of_mem zero_le_one ht]
          unfold ambientPath
          change (D.pt (γ ⟨t, ht⟩ : ℂ)) = γ.extend t
          exact (Path.extend_apply γ ht).symm
        _ = D.len P a b := hγlen
        _ = D.internal K (Q 0, Q 1) := hT.symm
    · intro s t hs hst ht
      have hsI : (s : ℝ) ∈ Icc (0 : ℝ) 1 :=
        ⟨by exact_mod_cast hs, by exact_mod_cast hst.trans ht⟩
      have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
        ⟨by exact_mod_cast hs.trans hst, by exact_mod_cast ht⟩
      have hsproj : projIcc 0 1 zero_le_one (s : ℝ) = ⟨(s : ℝ), hsI⟩ :=
        projIcc_of_mem zero_le_one hsI
      have htproj : projIcc 0 1 zero_le_one (t : ℝ) = ⟨(t : ℝ), htI⟩ :=
        projIcc_of_mem zero_le_one htI
      have hb := hQlip (projIcc 0 1 zero_le_one (s : ℝ))
        (projIcc 0 1 zero_le_one (t : ℝ))
      change D ((γ (projIcc 0 1 zero_le_one (s : ℝ)) : ℂ),
        (γ (projIcc 0 1 zero_le_one (t : ℝ)) : ℂ)) ≤
        ((D.len P a b).toNNReal : ENNReal) *
          edist (projIcc 0 1 zero_le_one (s : ℝ))
            (projIcc 0 1 zero_le_one (t : ℝ)) at hb
      rw [hsproj, htproj, edist_dist] at hb
      change D ((γ ⟨(s : ℝ), hsI⟩ : ℂ), (γ ⟨(t : ℝ), htI⟩ : ℂ)) ≤
        ((D.len P a b).toNNReal : ENNReal) *
          ENNReal.ofReal (dist (s : ℝ) (t : ℝ)) at hb
      rw [Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hst)), neg_sub,
        ENNReal.coe_toNNReal hFin.ne] at hb
      unfold internalTimeCost
      rw [hsproj, htproj, hT]
      exact hb.trans_eq (mul_comm _ _)
  · intro t
    exact hγtrace t

 

theorem internalBoundaryGeodesic_iff_code (D : LSCMetric)
    (z : ℂ) (r : ℝ) :
    (∃ (P : ℝ → ℂ) (a b : ℝ),
      TwoScale.S36Events.InternalBoundaryGeodesic D z r P a b) ↔
    (∃ Q : InternalPath (TwoScale.S36Events.eventCarrier z r),
      InternalGeoCode (TwoScale.S36Events.eventCarrier z r) (D, Q) ∧
      (Q 0 : ℂ) ∈ TwoScale.S36Events.eventBoundary z r ∧
      (Q 1 : ℂ) ∈ TwoScale.S36Events.eventBoundary z r) := by
  have hK : IsCompact (TwoScale.S36Events.eventCarrier z r) := by
    exact (isCompact_closedBall z (2 * r)).diff Metric.isOpen_ball
  constructor
  · rintro ⟨P, a, b, ⟨hu, hv, hCurve, hTrace, hBound0, hBound1, hLen, hFin⟩⟩
    have hTrace' : P '' Icc a b ⊆ TwoScale.S36Events.eventCarrier z r := by
      rintro y ⟨t, ht, rfl⟩
      exact hTrace t ht
    obtain ⟨Q, hCode, hQ0, hQ1, _⟩ :=
      exists_internalGeoCode_of_source hK D P a b hCurve hTrace' hu hv hLen hFin
    exact ⟨Q, hCode, hQ0.symm ▸ hBound0, hQ1.symm ▸ hBound1⟩
  · rintro ⟨Q, hCode, hBound0, hBound1⟩
    let P : ℝ → ℂ := Measurability.GeodesicCodes.pathReal (ambientPath Q)
    have hP0 : P 0 = (Q 0 : ℂ) := by
      unfold P Measurability.GeodesicCodes.pathReal ambientPath
      rw [projIcc_of_mem zero_le_one (show (0 : ℝ) ∈ Icc 0 1 by norm_num)]
      rfl
    have hP1 : P 1 = (Q 1 : ℂ) := by
      unfold P Measurability.GeodesicCodes.pathReal ambientPath
      rw [projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc 0 1 by norm_num)]
      rfl
    have hu : P 0 ∈ TwoScale.S36Events.eventCarrier z r := hP0 ▸ (Q 0).property
    have hv : P 1 ∈ TwoScale.S36Events.eventCarrier z r := hP1 ▸ (Q 1).property
    have hCurveLen := internalGeoCode_isCurve D Q hCode
    have hTrace : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ TwoScale.S36Events.eventCarrier z r := by
      intro t ht
      unfold P Measurability.GeodesicCodes.pathReal ambientPath
      rw [projIcc_of_mem zero_le_one ht]
      exact (Q ⟨t, ht⟩).property
    have hLen : D.len P 0 1 =
        D.internal (TwoScale.S36Events.eventCarrier z r) (⟨P 0, hu⟩, ⟨P 1, hv⟩) := by
      have he0 : (⟨P 0, hu⟩ : TwoScale.S36Events.eventCarrier z r) = Q 0 :=
        Subtype.ext hP0
      have he1 : (⟨P 1, hv⟩ : TwoScale.S36Events.eventCarrier z r) = Q 1 :=
        Subtype.ext hP1
      rw [he0, he1]
      exact hCurveLen.2
    have hFin : D.len P 0 1 < ⊤ := by
      unfold InternalGeoCode internalEndpointCost at hCode
      rw [hCurveLen.2]
      exact hCode.1
    exact ⟨P, 0, 1,
      ⟨hu, hv, hCurveLen.1, hTrace, hP0 ▸ hBound0,
        hP1 ▸ hBound1, hLen, hFin⟩⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
