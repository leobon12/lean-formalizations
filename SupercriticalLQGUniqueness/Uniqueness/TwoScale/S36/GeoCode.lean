import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.PointLoop
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointCompactPort
import Mathlib.Topology.ContinuousMap.SecondCountableSpace




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 
abbrev PathCode : Type := C(unitInterval, ℂ)

instance : MeasurableSpace PathCode := borel PathCode

instance : BorelSpace PathCode := ⟨rfl⟩

 

def IsGeoCode (D : LSCMetric) (γ : PathCode) : Prop :=
  D (γ 0, γ 1) < ⊤ ∧ ∀ s t : unitInterval, (s : ℝ) ≤ t →
    D (γ s, γ t) ≤ ENNReal.ofReal ((t : ℝ) - s) * D (γ 0, γ 1)

 
abbrev RatTimes : Type := {q : ℚ × ℚ // 0 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ q.2 ∧ (q.2 : ℝ) ≤ 1}

 
def RatTimes.lo (q : RatTimes) : unitInterval :=
  ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩

 
def RatTimes.hi (q : RatTimes) : unitInterval :=
  ⟨q.1.2, q.2.1.trans q.2.2.1, q.2.2.2⟩

 
def IsGeoCodeRat (D : LSCMetric) (γ : PathCode) : Prop :=
  D (γ 0, γ 1) < ⊤ ∧ ∀ q : RatTimes,
    D (γ q.lo, γ q.hi) ≤ ENNReal.ofReal ((q.hi : ℝ) - q.lo) * D (γ 0, γ 1)

 
theorem isOpen_lt_of_continuous_lsc {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ≥0∞} (hf : Continuous f) (hg : LowerSemicontinuous g) :
    IsOpen {x | f x < g x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨m, hfm, hmg⟩ := exists_between (show f x < g x from hx)
  have h₁ : {y | f y < m} ∈ 𝓝 x := (isOpen_Iio.preimage hf).mem_nhds hfm
  have h₂ : {y | m < g y} ∈ 𝓝 x := (hg.isOpen_preimage m).mem_nhds hmg
  exact Filter.mem_of_superset (Filter.inter_mem h₁ h₂) fun y hy =>
    show f y < g y from lt_trans hy.1 hy.2

 
theorem exists_rat_below (s : unitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s ∧ (s : ℝ) - ε < q := by
  by_cases hs : (s : ℝ) = 0
  · refine ⟨0, by simp, by simp [hs], by simp [hs, hε]⟩
  · have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hs0 (sub_lt_self (s : ℝ) hε))
    exact ⟨q, (le_max_left _ _).trans hq1.le, hq2.le, (le_max_right _ _).trans_lt hq1⟩

 
theorem exists_rat_above (t : unitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, (q : ℝ) ≤ 1 ∧ (t : ℝ) ≤ q ∧ (q : ℝ) < t + ε := by
  by_cases ht : (t : ℝ) = 1
  · refine ⟨1, by simp, by simp [ht], by simp [ht, hε]⟩
  · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min ht1 (lt_add_of_pos_right (t : ℝ) hε))
    exact ⟨q, hq2.le.trans (min_le_left _ _), hq1.le, hq2.trans_le (min_le_right _ _)⟩

 
theorem isGeoCode_iff_rat (D : LSCMetric) (γ : PathCode) :
    IsGeoCode D γ ↔ IsGeoCodeRat D γ := by
  constructor
  · rintro ⟨hfin, hall⟩
    exact ⟨hfin, fun q => hall q.lo q.hi q.2.2.1⟩
  · rintro ⟨hfin, hrat⟩
    refine ⟨hfin, fun s t hst => ?_⟩
    by_contra hbad
    rw [not_le] at hbad
    
    let F : unitInterval × unitInterval → ℝ≥0∞ := fun p => D (γ p.1, γ p.2)
    let G : unitInterval × unitInterval → ℝ≥0∞ :=
      fun p => ENNReal.ofReal ((p.2 : ℝ) - p.1) * D (γ 0, γ 1)
    have hFl : LowerSemicontinuous F := by
      have hc : Continuous fun p : unitInterval × unitInterval => (γ p.1, γ p.2) :=
        (γ.continuous.comp continuous_fst).prodMk (γ.continuous.comp continuous_snd)
      exact D.lowerSemicontinuous.comp hc
    have hGc : Continuous G := by
      have h1 : Continuous fun p : unitInterval × unitInterval =>
          ENNReal.ofReal ((p.2 : ℝ) - p.1) :=
        ENNReal.continuous_ofReal.comp
          ((continuous_subtype_val.comp continuous_snd).sub
            (continuous_subtype_val.comp continuous_fst))
      exact (ENNReal.continuous_mul_const hfin.ne).comp h1
    have hO : IsOpen {p | G p < F p} := isOpen_lt_of_continuous_lsc hGc hFl
    have hmem : (s, t) ∈ {p | G p < F p} := hbad
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (s, t) hmem
    obtain ⟨q₁, hq₁0, hq₁s, hq₁ε⟩ := exists_rat_below s hε
    obtain ⟨q₂, hq₂1, hq₂t, hq₂ε⟩ := exists_rat_above t hε
    let q : RatTimes := ⟨(q₁, q₂), hq₁0, hq₁s.trans (hst.trans hq₂t), hq₂1⟩
    have hqball : (q.lo, q.hi) ∈ Metric.ball (s, t) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        change -ε < (q₁ : ℝ) - s ∧ (q₁ : ℝ) - s < ε
        constructor <;> linarith
      · rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        change -ε < (q₂ : ℝ) - t ∧ (q₂ : ℝ) - t < ε
        constructor <;> linarith
    have hviol : G (q.lo, q.hi) < F (q.lo, q.hi) := hball hqball
    exact (not_lt_of_ge (hrat q)) hviol

 
theorem measurableSet_isGeoCode :
    MeasurableSet {p : LSCMetric × PathCode | IsGeoCode p.1 p.2} := by
  have hev (x y : unitInterval) :
      Measurable fun p : LSCMetric × PathCode => p.1 (p.2 x, p.2 y) := by
    have hc : Measurable fun p : LSCMetric × PathCode =>
        ((p.1, (p.2 x, p.2 y)) : LSCMetric × (ℂ × ℂ)) := by
      refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
      · exact (continuous_eval_const x).measurable.comp measurable_snd
      · exact (continuous_eval_const y).measurable.comp measurable_snd
    exact TwoScale.S36Events.jointEval_lsc.measurable.comp hc
  have hfin : MeasurableSet {p : LSCMetric × PathCode | p.1 (p.2 0, p.2 1) < ⊤} :=
    measurableSet_lt (hev 0 1) measurable_const
  have hq (q : RatTimes) : MeasurableSet {p : LSCMetric × PathCode |
      p.1 (p.2 q.lo, p.2 q.hi) ≤
        ENNReal.ofReal ((q.hi : ℝ) - q.lo) * p.1 (p.2 0, p.2 1)} :=
    measurableSet_le (hev q.lo q.hi) (measurable_const.mul (hev 0 1))
  have hall : MeasurableSet {p : LSCMetric × PathCode | ∀ q : RatTimes,
      p.1 (p.2 q.lo, p.2 q.hi) ≤
        ENNReal.ofReal ((q.hi : ℝ) - q.lo) * p.1 (p.2 0, p.2 1)} := by
    have h := MeasurableSet.iInter hq
    have heq : {p : LSCMetric × PathCode | ∀ q : RatTimes,
        p.1 (p.2 q.lo, p.2 q.hi) ≤
          ENNReal.ofReal ((q.hi : ℝ) - q.lo) * p.1 (p.2 0, p.2 1)} =
        ⋂ q : RatTimes, {p : LSCMetric × PathCode |
          p.1 (p.2 q.lo, p.2 q.hi) ≤
            ENNReal.ofReal ((q.hi : ℝ) - q.lo) * p.1 (p.2 0, p.2 1)} := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact h
  have heq : {p : LSCMetric × PathCode | IsGeoCode p.1 p.2} =
      {p : LSCMetric × PathCode | p.1 (p.2 0, p.2 1) < ⊤} ∩
        {p : LSCMetric × PathCode | ∀ q : RatTimes,
          p.1 (p.2 q.lo, p.2 q.hi) ≤
            ENNReal.ofReal ((q.hi : ℝ) - q.lo) * p.1 (p.2 0, p.2 1)} := by
    ext p
    rw [mem_ofPred_eq, isGeoCode_iff_rat]
    rfl
  rw [heq]
  exact hfin.inter hall

 

 
theorem edist_unitInterval_of_le {s t : unitInterval} (hst : (s : ℝ) ≤ t) :
    edist s t = ENNReal.ofReal ((t : ℝ) - s) := by
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hst)]

 

theorem exists_code_of_geodesic (D : LSCMetric) {P : ℝ → ℂ} {s t : ℝ} {u v : ℂ}
    (hP : OptimalConstants.Ratios.Geodesic D P s t u v) {K : Set ℂ} (hK : IsCompact K)
    (htrace : ∀ τ ∈ Icc s t, P τ ∈ K) :
    ∃ γ : PathCode, IsGeoCode D γ ∧ γ 0 = u ∧ γ 1 = v ∧
      ∀ τ, γ τ ∈ P '' Icc s t := by
  obtain ⟨hcurve, hPs, hPt, hlenEq, hfinite⟩ := hP
  have hEuc : ContinuousOn P (Icc s t) :=
    hcurve.continuousOn_of_mapsTo hK fun τ hτ => htrace τ hτ
  have hKP : IsCompact (P '' Icc s t) := isCompact_Icc.image_of_continuousOn hEuc
  have hlenfin : D.len P s t ≠ ⊤ := by
    rw [hlenEq]
    exact hfinite.ne
  obtain ⟨γ, hγlen, hγrange, hγlip⟩ :=
    Toolkit.CompactPathInfimum.exists_lipschitz_reparam D P hcurve hlenfin (subset_refl _)
  let f : unitInterval → ℂ := fun τ => (γ τ : ℂ)
  have hfD : Continuous (D.pt ∘ f) := γ.continuous
  have hfc : Continuous f :=
    Toolkit.CompactPathInfimum.continuous_euclidean_of_metric_on_compact D hKP hγrange hfD
  let c : PathCode := ⟨f, hfc⟩
  have hc0 : c 0 = u := by
    change (γ 0 : ℂ) = u
    rw [γ.source]
    exact hPs
  have hc1 : c 1 = v := by
    change (γ 1 : ℂ) = v
    rw [γ.target]
    exact hPt
  refine ⟨c, ⟨?_, ?_⟩, hc0, hc1, hγrange⟩
  · rw [hc0, hc1]
    exact hfinite
  · intro x y hxy
    have hlip := hγlip x y
    have hL : ((D.len P s t).toNNReal : ℝ≥0∞) = D (c 0, c 1) := by
      rw [ENNReal.coe_toNNReal hlenfin, hc0, hc1]
      exact hlenEq
    change edist (γ x) (γ y) ≤ _
    calc
      edist (γ x) (γ y) ≤ (D.len P s t).toNNReal * edist x y := hlip
      _ = ENNReal.ofReal ((y : ℝ) - x) * D (c 0, c 1) := by
        rw [hL, edist_unitInterval_of_le hxy, mul_comm]

 

 
def codeExt (γ : PathCode) : ℝ → ℂ :=
  Set.IccExtend (zero_le_one' ℝ) γ

theorem codeExt_of_mem (γ : PathCode) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    codeExt γ τ = γ ⟨τ, hτ⟩ :=
  Set.IccExtend_of_mem _ _ hτ

theorem codeExt_zero (γ : PathCode) : codeExt γ 0 = γ 0 :=
  codeExt_of_mem γ unitInterval.zero_mem

theorem codeExt_one (γ : PathCode) : codeExt γ 1 = γ 1 :=
  codeExt_of_mem γ unitInterval.one_mem

theorem codeExt_image (γ : PathCode) : codeExt γ '' Icc 0 1 = range γ := by
  ext z
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, (codeExt_of_mem γ hτ).symm⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ, τ.2, codeExt_of_mem γ τ.2⟩

 
theorem IsGeoCode.dist_le {D : LSCMetric} {γ : PathCode} (hγ : IsGeoCode D γ)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    D (codeExt γ x, codeExt γ y) ≤
      (D (γ 0, γ 1)).toNNReal * edist x y := by
  have hL : ((D (γ 0, γ 1)).toNNReal : ℝ≥0∞) = D (γ 0, γ 1) :=
    ENNReal.coe_toNNReal hγ.1.ne
  rw [hL, codeExt_of_mem γ hx, codeExt_of_mem γ hy]
  rcases le_total x y with hxy | hyx
  · have h := hγ.2 ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy), mul_comm]
    exact h
  · have h := hγ.2 ⟨y, hy⟩ ⟨x, hx⟩ hyx
    rw [D.isExtMetric.2.2.1, edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
      mul_comm]
    exact h

 
theorem geodesic_of_code {D : LSCMetric} {γ : PathCode} (hγ : IsGeoCode D γ) :
    OptimalConstants.Ratios.Geodesic D (codeExt γ) 0 1 (γ 0) (γ 1) := by
  have hlip : LipschitzOnWith (D (γ 0, γ 1)).toNNReal (D.pt ∘ codeExt γ) (Icc 0 1) :=
    fun x hx y hy => hγ.dist_le hx hy
  have hcurve : D.IsCurve (codeExt γ) 0 1 := ⟨zero_le_one, hlip.continuousOn⟩
  have hle : D.len (codeExt γ) 0 1 ≤ D (γ 0, γ 1) := by
    have h1 : eVariationOn (D.pt ∘ codeExt γ ∘ id) (Icc (0 : ℝ) 1) ≤
        (D (γ 0, γ 1)).toNNReal * eVariationOn (id : ℝ → ℝ) (Icc 0 1) :=
      hlip.comp_eVariationOn_le (mapsTo_id _)
    have h2 : eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (1 - 0) := by
      have h := (monotone_id.monotoneOn (Icc (0 : ℝ) 1)).eVariationOn_eq
        (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
      simp only [inter_self, id] at h
      exact h.le
    have hL : ((D (γ 0, γ 1)).toNNReal : ℝ≥0∞) = D (γ 0, γ 1) :=
      ENNReal.coe_toNNReal hγ.1.ne
    calc
      D.len (codeExt γ) 0 1 = eVariationOn (D.pt ∘ codeExt γ ∘ id) (Icc (0 : ℝ) 1) := rfl
      _ ≤ (D (γ 0, γ 1)).toNNReal * eVariationOn (id : ℝ → ℝ) (Icc 0 1) := h1
      _ ≤ (D (γ 0, γ 1)).toNNReal * ENNReal.ofReal (1 - 0) := mul_le_mul' le_rfl h2
      _ = D (γ 0, γ 1) := by rw [hL]; norm_num
  have hge : D (γ 0, γ 1) ≤ D.len (codeExt γ) 0 1 := by
    have h := eVariationOn.edist_le (D.pt ∘ codeExt γ)
      (left_mem_Icc.mpr (zero_le_one' ℝ)) (right_mem_Icc.mpr (zero_le_one' ℝ))
    change D (codeExt γ 0, codeExt γ 1) ≤ _ at h
    rwa [codeExt_zero, codeExt_one] at h
  exact ⟨hcurve, codeExt_zero γ, codeExt_one γ, le_antisymm hle hge, hγ.1⟩

 

theorem exists_geodesic_iff_code (D : LSCMetric) (u v : ℂ) {K : Set ℂ}
    (hK : IsCompact K) (c : ℝ) :
    (∃ (P : ℝ → ℂ) (s t : ℝ), OptimalConstants.Ratios.Geodesic D P s t u v ∧
        (∀ τ ∈ Icc s t, P τ ∈ K) ∧ Metric.diam (P '' Icc s t) ≤ c) ↔
      ∃ γ : PathCode, IsGeoCode D γ ∧ γ 0 = u ∧ γ 1 = v ∧ (∀ τ, γ τ ∈ K) ∧
        ∀ τ₁ τ₂, dist (γ τ₁) (γ τ₂) ≤ c := by
  constructor
  · rintro ⟨P, s, t, hP, htrace, hdiam⟩
    obtain ⟨γ, hγ, hγ0, hγ1, hγtr⟩ := exists_code_of_geodesic D hP hK htrace
    have hbdd : Bornology.IsBounded (P '' Icc s t) := by
      have hEuc : ContinuousOn P (Icc s t) :=
        hP.1.continuousOn_of_mapsTo hK fun τ hτ => htrace τ hτ
      exact (isCompact_Icc.image_of_continuousOn hEuc).isBounded
    refine ⟨γ, hγ, hγ0, hγ1, fun τ => ?_, fun τ₁ τ₂ => ?_⟩
    · obtain ⟨σ, hσ, hσeq⟩ := hγtr τ
      rw [← hσeq]
      exact htrace σ hσ
    · exact (Metric.dist_le_diam_of_mem hbdd (hγtr τ₁) (hγtr τ₂)).trans hdiam
  · rintro ⟨γ, hγ, hγ0, hγ1, hγK, hγd⟩
    refine ⟨codeExt γ, 0, 1, hγ0 ▸ hγ1 ▸ geodesic_of_code hγ, fun τ hτ => ?_, ?_⟩
    · rw [codeExt_of_mem γ hτ]
      exact hγK _
    · rw [codeExt_image]
      have hc : 0 ≤ c := (dist_self (γ 0)).symm.le.trans (hγd 0 0)
      refine Metric.diam_le_of_forall_dist_le hc ?_
      rintro _ ⟨τ₁, rfl⟩ _ ⟨τ₂, rfl⟩
      exact hγd τ₁ τ₂

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
