import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.GeodesicCode
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.PointLoop
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 


set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private def ratPoint (q : ℚ) : unitInterval :=
  projIcc 0 1 zero_le_one (q : ℝ)

private theorem ratPoint_dense : DenseRange ratPoint := by
  change DenseRange (projIcc 0 1 zero_le_one ∘ (fun q : ℚ => (q : ℝ)))
  exact (projIcc_surjective zero_le_one).denseRange.comp
    Rat.denseRange_cast continuous_projIcc

private def metricPairCost (D : LSCMetric) (P : Measurability.GeodesicCodes.Path)
    (st : unitInterval × unitInterval) : ENNReal :=
  D (P st.1, P st.2)

private theorem metricPairCost_lsc (D : LSCMetric) (P : Measurability.GeodesicCodes.Path) :
    LowerSemicontinuous (metricPairCost D P) := by
  let f : LSCMetric × (ℂ × ℂ) → ENNReal := fun p => p.1 p.2
  let h : unitInterval × unitInterval → LSCMetric × (ℂ × ℂ) :=
    fun st => (D, (P st.1, P st.2))
  have hf : LowerSemicontinuous f := TwoScale.S36Events.jointEval_lsc
  have hc : Continuous h := by
    have hs : Continuous (fun st : unitInterval × unitInterval => P st.1) :=
      P.continuous.comp continuous_fst
    have ht : Continuous (fun st : unitInterval × unitInterval => P st.2) :=
      P.continuous.comp continuous_snd
    exact continuous_const.prodMk (hs.prodMk ht)
  have hcomp : LowerSemicontinuous (f ∘ h) := hf.comp hc
  exact hcomp

private def speedBound (T : ENNReal) (st : unitInterval × unitInterval) : ENNReal :=
  ENNReal.ofReal |(st.2 : ℝ) - (st.1 : ℝ)| * T

private theorem speedBound_continuous {T : ENNReal} (hT : T ≠ ⊤) :
    Continuous (speedBound T) := by
  have hsub : Continuous (fun st : unitInterval × unitInterval =>
      (st.2 : ℝ) - (st.1 : ℝ)) :=
    (continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)
  exact (ENNReal.continuous_mul_const hT).comp
    (ENNReal.continuous_ofReal.comp hsub.abs)

private theorem isOpen_continuous_lt_lsc {α : Type*} [TopologicalSpace α]
    {f g : α → ENNReal} (hf : Continuous f) (hg : LowerSemicontinuous g) :
    IsOpen {x | f x < g x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change f x < g x at hx
  obtain ⟨m, hfm, hmg⟩ := exists_between hx
  have h₁ : {y | f y < m} ∈ 𝓝 x :=
    (isOpen_Iio.preimage hf).mem_nhds hfm
  have h₂ : {y | m < g y} ∈ 𝓝 x :=
    (hg.isOpen_preimage m).mem_nhds hmg
  exact Filter.mem_of_superset (Filter.inter_mem h₁ h₂) (by
    intro y hy
    change f y < m ∧ m < g y at hy
    exact hy.1.trans hy.2)

private theorem rationalSpeed_rat_pair_bound (D : LSCMetric) (P : Measurability.GeodesicCodes.Path)
    (T : ENNReal)
    (hbound : ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
      D (P (projIcc 0 1 zero_le_one (s : ℝ)),
        P (projIcc 0 1 zero_le_one (t : ℝ))) ≤
        ENNReal.ofReal ((t : ℝ) - s) * T)
    (q r : ℚ) :
    metricPairCost D P (ratPoint q, ratPoint r) ≤
      speedBound T (ratPoint q, ratPoint r) := by
  let q' : ℚ := max 0 (min 1 q)
  let r' : ℚ := max 0 (min 1 r)
  have hq : (ratPoint q : ℝ) = (q' : ℝ) := by
    simp only [ratPoint, coe_projIcc]
    exact_mod_cast rfl
  have hr : (ratPoint r : ℝ) = (r' : ℝ) := by
    simp only [ratPoint, coe_projIcc]
    exact_mod_cast rfl
  have hq0 : (0 : ℚ) ≤ q' := le_max_left _ _
  have hq1 : q' ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hr0 : (0 : ℚ) ≤ r' := le_max_left _ _
  have hr1 : r' ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hqcast : ((projIcc 0 1 zero_le_one (q' : ℝ) : unitInterval) : ℝ) = (q' : ℝ) := by
    rw [projIcc_of_mem zero_le_one
      (show (q' : ℝ) ∈ Icc (0 : ℝ) 1 from
        ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩)]
  have hrcast : ((projIcc 0 1 zero_le_one (r' : ℝ) : unitInterval) : ℝ) = (r' : ℝ) := by
    rw [projIcc_of_mem zero_le_one
      (show (r' : ℝ) ∈ Icc (0 : ℝ) 1 from
        ⟨by exact_mod_cast hr0, by exact_mod_cast hr1⟩)]
  by_cases hqr : q' ≤ r'
  · have hb := hbound q' r' hq0 hqr hr1
    have hpq : ratPoint q = projIcc 0 1 zero_le_one (q' : ℝ) := by
      apply Subtype.ext
      rw [hq, projIcc_of_mem zero_le_one]
      exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩
    have hpr : ratPoint r = projIcc 0 1 zero_le_one (r' : ℝ) := by
      apply Subtype.ext
      rw [hr, projIcc_of_mem zero_le_one]
      exact ⟨by exact_mod_cast hr0, by exact_mod_cast hr1⟩
    change D (P (ratPoint q), P (ratPoint r)) ≤
      ENNReal.ofReal |(ratPoint r : ℝ) - (ratPoint q : ℝ)| * T
    rw [hpq, hpr, hrcast, hqcast,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hqr))]
    exact hb
  · have hrq : r' ≤ q' := le_of_not_ge hqr
    have hb := hbound r' q' hr0 hrq hq1
    have hpq : ratPoint q = projIcc 0 1 zero_le_one (q' : ℝ) := by
      apply Subtype.ext
      rw [hq, projIcc_of_mem zero_le_one]
      exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩
    have hpr : ratPoint r = projIcc 0 1 zero_le_one (r' : ℝ) := by
      apply Subtype.ext
      rw [hr, projIcc_of_mem zero_le_one]
      exact ⟨by exact_mod_cast hr0, by exact_mod_cast hr1⟩
    change D (P (ratPoint q), P (ratPoint r)) ≤
      ENNReal.ofReal |(ratPoint r : ℝ) - (ratPoint q : ℝ)| * T
    rw [hpq, hpr, hrcast, hqcast,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hrq))]
    rw [neg_sub]
    exact (D.isExtMetric.2.2.1 _ _).trans_le hb

theorem rationalSpeed_all_times (D : LSCMetric) (P : Measurability.GeodesicCodes.Path)
    (T : ENNReal) (hT : T ≠ ⊤)
    (hbound : ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
      D (P (projIcc 0 1 zero_le_one (s : ℝ)),
        P (projIcc 0 1 zero_le_one (t : ℝ))) ≤
        ENNReal.ofReal ((t : ℝ) - s) * T) :
    ∀ s t : unitInterval,
      D (P s, P t) ≤ ENNReal.ofReal |(t : ℝ) - (s : ℝ)| * T := by
  let f := speedBound T
  let g := metricPairCost D P
  have hf : Continuous f := speedBound_continuous hT
  have hg : LowerSemicontinuous g := metricPairCost_lsc D P
  have hO : IsOpen {st : unitInterval × unitInterval | f st < g st} :=
    isOpen_continuous_lt_lsc hf hg
  have hclosed : IsClosed {st : unitInterval × unitInterval | g st ≤ f st} := by
    have heq : {st : unitInterval × unitInterval | g st ≤ f st} =
        {st | f st < g st}ᶜ := by
      ext st
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [heq]
    exact hO.isClosed_compl
  have hall : ∀ s t : unitInterval, g (s, t) ≤ f (s, t) :=
    isClosed_property2 (p := fun s t => g (s, t) ≤ f (s, t))
      ratPoint_dense hclosed (rationalSpeed_rat_pair_bound D P T hbound)
  exact hall

theorem geoCode_all_times (D : LSCMetric) (P : Measurability.GeodesicCodes.Path) (u v : ℂ)
    (h : Measurability.GeodesicCodes.GeoCode (D, (P, (u, v)))) :
    ∀ s t : unitInterval,
      D (P s, P t) ≤ ENNReal.ofReal |(t : ℝ) - (s : ℝ)| * D (u, v) :=
  rationalSpeed_all_times D P (D (u, v)) h.2.2.1.ne h.2.2.2

 

theorem rationalSpeed_isCurve_length_le (D : LSCMetric) (P : Measurability.GeodesicCodes.Path)
    (T : ENNReal) (hT : T ≠ ⊤)
    (hbound : ∀ s t : ℚ, 0 ≤ s → s ≤ t → t ≤ 1 →
      D (P (projIcc 0 1 zero_le_one (s : ℝ)),
        P (projIcc 0 1 zero_le_one (t : ℝ))) ≤
        ENNReal.ofReal ((t : ℝ) - s) * T) :
    D.IsCurve (Measurability.GeodesicCodes.pathReal P) 0 1 ∧
      D.len (Measurability.GeodesicCodes.pathReal P) 0 1 ≤ T := by
  let K : NNReal := T.toNNReal
  have hpath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      Measurability.GeodesicCodes.pathReal P s = P ⟨s, hs⟩ := by
    unfold Measurability.GeodesicCodes.pathReal
    rw [projIcc_of_mem zero_le_one hs]
  have hLip : LipschitzOnWith K (D.pt ∘ Measurability.GeodesicCodes.pathReal P) (Icc (0 : ℝ) 1) := by
    intro s hs t ht
    have hb := rationalSpeed_all_times D P T hT hbound ⟨s, hs⟩ ⟨t, ht⟩
    have hb' : D (Measurability.GeodesicCodes.pathReal P s, Measurability.GeodesicCodes.pathReal P t) ≤
        ENNReal.ofReal |t - s| * T := by
      rw [hpath s hs, hpath t ht]
      exact hb
    calc
      edist ((D.pt ∘ Measurability.GeodesicCodes.pathReal P) s) ((D.pt ∘ Measurability.GeodesicCodes.pathReal P) t) =
          D (Measurability.GeodesicCodes.pathReal P s, Measurability.GeodesicCodes.pathReal P t) := rfl
      _ ≤ ENNReal.ofReal |t - s| * T := hb'
      _ = (K : ENNReal) * edist s t := by
        rw [edist_dist, Real.dist_eq, ENNReal.coe_toNNReal hT]
        rw [abs_sub_comm s t]
        exact mul_comm (ENNReal.ofReal |t - s|) T
  constructor
  · exact ⟨zero_le_one, hLip.continuousOn⟩
  · change eVariationOn (D.pt ∘ Measurability.GeodesicCodes.pathReal P) (Icc (0 : ℝ) 1) ≤ _
    calc
      eVariationOn (D.pt ∘ Measurability.GeodesicCodes.pathReal P) (Icc (0 : ℝ) 1) =
          eVariationOn ((D.pt ∘ Measurability.GeodesicCodes.pathReal P) ∘ id) (Icc (0 : ℝ) 1) := rfl
      _ ≤ (K : ENNReal) * eVariationOn id (Icc (0 : ℝ) 1) :=
        hLip.comp_eVariationOn_le (mapsTo_id _)
      _ = T := by
        rw [eVariationOn_id_Icc, ENNReal.coe_toNNReal hT]
        simp

 
theorem geoCode_isGeodesic (D : LSCMetric) (P : Measurability.GeodesicCodes.Path) (u v : ℂ)
    (h : Measurability.GeodesicCodes.GeoCode (D, (P, (u, v)))) :
    OptimalConstants.Ratios.Geodesic D (Measurability.GeodesicCodes.pathReal P) 0 1 u v := by
  have hT : D (u, v) ≠ ⊤ := h.2.2.1.ne
  let K : NNReal := (D (u, v)).toNNReal
  have hpath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      Measurability.GeodesicCodes.pathReal P s = P ⟨s, hs⟩ := by
    unfold Measurability.GeodesicCodes.pathReal
    rw [projIcc_of_mem zero_le_one hs]
  have hLip : LipschitzOnWith K (D.pt ∘ Measurability.GeodesicCodes.pathReal P) (Icc (0 : ℝ) 1) := by
    intro s hs t ht
    have hb := geoCode_all_times D P u v h ⟨s, hs⟩ ⟨t, ht⟩
    have hb' : D (Measurability.GeodesicCodes.pathReal P s, Measurability.GeodesicCodes.pathReal P t) ≤
        ENNReal.ofReal |t - s| * D (u, v) := by
      rw [hpath s hs, hpath t ht]
      exact hb
    calc
      edist ((D.pt ∘ Measurability.GeodesicCodes.pathReal P) s) ((D.pt ∘ Measurability.GeodesicCodes.pathReal P) t) =
          D (Measurability.GeodesicCodes.pathReal P s, Measurability.GeodesicCodes.pathReal P t) := rfl
      _ ≤ ENNReal.ofReal |t - s| * D (u, v) := hb'
      _ = (K : ENNReal) * edist s t := by
        rw [edist_dist, Real.dist_eq, ENNReal.coe_toNNReal hT]
        rw [abs_sub_comm s t]
        exact mul_comm (ENNReal.ofReal |t - s|) (D (u, v))
  have hcurve : D.IsCurve (Measurability.GeodesicCodes.pathReal P) 0 1 :=
    ⟨zero_le_one, hLip.continuousOn⟩
  have hupper : D.len (Measurability.GeodesicCodes.pathReal P) 0 1 ≤ D (u, v) := by
    change eVariationOn (D.pt ∘ Measurability.GeodesicCodes.pathReal P) (Icc (0 : ℝ) 1) ≤ _
    calc
      eVariationOn (D.pt ∘ Measurability.GeodesicCodes.pathReal P) (Icc (0 : ℝ) 1) =
          eVariationOn ((D.pt ∘ Measurability.GeodesicCodes.pathReal P) ∘ id) (Icc (0 : ℝ) 1) := rfl
      _ ≤ (K : ENNReal) * eVariationOn id (Icc (0 : ℝ) 1) :=
        hLip.comp_eVariationOn_le (mapsTo_id _)
      _ = D (u, v) := by
        rw [eVariationOn_id_Icc, ENNReal.coe_toNNReal hT]
        simp
  have h0 : Measurability.GeodesicCodes.pathReal P 0 = u := by
    rw [hpath 0 ⟨le_rfl, zero_le_one⟩]
    change P 0 = u
    exact h.1
  have h1 : Measurability.GeodesicCodes.pathReal P 1 = v := by
    rw [hpath 1 ⟨zero_le_one, le_rfl⟩]
    change P 1 = v
    exact h.2.1
  have hlow := LQGMetric.MetricGeometry.edist_le_curveLength
    (D.pt ∘ Measurability.GeodesicCodes.pathReal P) zero_le_one
  have hlower : D (u, v) ≤ D.len (Measurability.GeodesicCodes.pathReal P) 0 1 := by
    change D (Measurability.GeodesicCodes.pathReal P 0, Measurability.GeodesicCodes.pathReal P 1) ≤
      D.len (Measurability.GeodesicCodes.pathReal P) 0 1 at hlow
    rw [h0, h1] at hlow
    exact hlow
  exact ⟨hcurve, h0, h1, le_antisymm hupper hlower, h.2.2.1⟩

 

theorem exists_geoCode_of_compact_geodesic (D : LSCMetric) (K : Set ℂ)
    (hK : IsCompact K) (P : ℝ → ℂ) (a b : ℝ) (u v : ℂ)
    (hGeo : OptimalConstants.Ratios.Geodesic D P a b u v)
    (htrace : P '' Icc a b ⊆ K) :
    ∃ Q : Measurability.GeodesicCodes.Path,
      Measurability.GeodesicCodes.GeoCode (D, (Q, (u, v))) ∧ ∀ t, Q t ∈ K := by
  obtain ⟨hcurve, h0, h1, hlen, hfin⟩ := hGeo
  have hfinlen : D.len P a b ≠ ∞ := by rw [hlen]; exact hfin.ne
  obtain ⟨γ, hγlen, hγtrace, hγlip⟩ :=
    Toolkit.CompactPathInfimum.exists_lipschitz_reparam D P hcurve hfinlen htrace
  have hγcurve : D.IsCurve (fun t : ℝ => (γ.extend t : ℂ)) 0 1 :=
    ⟨zero_le_one, γ.continuous_extend.continuousOn⟩
  have hγtrace' : (fun t : ℝ => (γ.extend t : ℂ)) '' Icc (0 : ℝ) 1 ⊆ K := by
    rintro y ⟨t, ht, rfl⟩
    change (γ.extend t : ℂ) ∈ K
    rw [Path.extend_apply γ ht]
    exact hγtrace ⟨t, ht⟩
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
  let Q : Measurability.GeodesicCodes.Path := ⟨fun t => (γ t : ℂ), hγcont⟩
  have hQ0 : Q 0 = u := by
    change (γ 0 : ℂ) = u
    rw [γ.source]
    exact h0
  have hQ1 : Q 1 = v := by
    change (γ 1 : ℂ) = v
    rw [γ.target]
    exact h1
  have hT : D (u, v) ≠ ⊤ := hfin.ne
  have hQlip : LipschitzWith (D (u, v)).toNNReal γ := by
    simpa only [hlen, h0, h1] using hγlip
  refine ⟨Q, ⟨hQ0, hQ1, hfin, ?_⟩, ?_⟩
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
    change D (Q (projIcc 0 1 zero_le_one (s : ℝ)),
      Q (projIcc 0 1 zero_le_one (t : ℝ))) ≤
      ((D (u, v)).toNNReal : ENNReal) *
        edist (projIcc 0 1 zero_le_one (s : ℝ))
          (projIcc 0 1 zero_le_one (t : ℝ)) at hb
    rw [hsproj, htproj, edist_dist] at hb
    change D (Q ⟨(s : ℝ), hsI⟩, Q ⟨(t : ℝ), htI⟩) ≤
      ((D (u, v)).toNNReal : ENNReal) *
        ENNReal.ofReal (dist (s : ℝ) (t : ℝ)) at hb
    rw [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hst)), neg_sub,
      ENNReal.coe_toNNReal hT] at hb
    calc
      D (Q (projIcc 0 1 zero_le_one (s : ℝ)),
          Q (projIcc 0 1 zero_le_one (t : ℝ))) =
          D (Q ⟨(s : ℝ), hsI⟩, Q ⟨(t : ℝ), htI⟩) := by rw [hsproj, htproj]
      _ ≤ D (u, v) * ENNReal.ofReal ((t : ℝ) - s) := hb
      _ = ENNReal.ofReal ((t : ℝ) - s) * D (u, v) := mul_comm _ _
  · intro t
    exact hγtrace t

 

theorem compact_geodesic_iff_geoCode (D : LSCMetric) (K : Set ℂ)
    (hK : IsCompact K) (u v : ℂ) :
    (∃ (P : ℝ → ℂ) (a b : ℝ),
      OptimalConstants.Ratios.Geodesic D P a b u v ∧ P '' Icc a b ⊆ K) ↔
    (∃ Q : Measurability.GeodesicCodes.Path,
      Measurability.GeodesicCodes.GeoCode (D, (Q, (u, v))) ∧ ∀ t, Q t ∈ K) := by
  constructor
  · rintro ⟨P, a, b, hGeo, htrace⟩
    exact exists_geoCode_of_compact_geodesic D K hK P a b u v hGeo htrace
  · rintro ⟨Q, hcode, htrace⟩
    refine ⟨Measurability.GeodesicCodes.pathReal Q, 0, 1, geoCode_isGeodesic D Q u v hcode, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    unfold Measurability.GeodesicCodes.pathReal
    rw [projIcc_of_mem zero_le_one ht]
    exact htrace ⟨t, ht⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
