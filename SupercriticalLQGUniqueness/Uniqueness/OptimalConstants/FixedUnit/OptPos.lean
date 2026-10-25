import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit.Events




 






set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit

open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios
open LQGMetric (DistC)

 
theorem endpoint_le_chain (E : LSCMetric) (P : ℝ → ℂ)
    (t : ℕ → ℝ) (n : ℕ) :
    E (P (t 0), P (t n)) ≤
      ∑ i ∈ Finset.range n, E (P (t i), P (t (i + 1))) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, E.isExtMetric.1, le_refl]
  | succ n ih =>
      calc
        E (P (t 0), P (t (n + 1))) ≤
            E (P (t 0), P (t n)) + E (P (t n), P (t (n + 1))) :=
          E.isExtMetric.2.2.2 _ _ _
        _ ≤ (∑ i ∈ Finset.range n, E (P (t i), P (t (i + 1)))) +
            E (P (t n), P (t (n + 1))) :=
          add_le_add ih le_rfl
        _ = _ := by rw [Finset.sum_range_succ]

 

theorem endpoint_le_length_of_local_comparison
    (D E : LSCMetric) (c : NNReal)
    (hLocal : ∀ x y : ℂ, dist x y < 1 →
      E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hCont : ContinuousOn P (Icc a b)) :
    E (P a, P b) ≤ (c : ℝ≥0∞) * D.len P a b := by
  by_cases heq : a = b
  · subst b
    simp only [E.isExtMetric.1, zero_le]
  have hab' : a < b := lt_of_le_of_ne hab heq
  have hU : UniformContinuousOn P (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hCont
  obtain ⟨ε, hε, hUC⟩ := (Metric.uniformContinuousOn_iff.mp hU) 1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / ε + 1)
  have hn0 : 0 < n := by
    have hq : 0 ≤ (b - a) / ε := div_nonneg (sub_nonneg.mpr hab) hε.le
    exact_mod_cast (show (0 : ℝ) < n by linarith only [hn, hq])
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hstep : (b - a) / (n : ℝ) < ε := by
    have hn' : (b - a) / ε < (n : ℝ) := by linarith only [hn]
    have hmul : b - a < ε * (n : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hn'
    exact (div_lt_iff₀ hnR).mpr (by nlinarith only [hmul])
  let t : ℕ → ℝ := fun i => a + (b - a) * (i : ℝ) / (n : ℝ)
  have ht0 : t 0 = a := by simp only [t, Nat.cast_zero, mul_zero, zero_div, add_zero]
  have htn : t n = b := by
    dsimp only [t]
    rw [mul_div_cancel_right₀ (b - a) hnR.ne']
    ring
  have htmono : StrictMonoOn t (Iic n) := by
    intro i _ j _ hij
    dsimp only [t]
    have hc : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    have hdiv : (i : ℝ) / n < (j : ℝ) / n :=
      div_lt_div_of_pos_right hc hnR
    calc
      a + (b - a) * (i : ℝ) / n =
          a + (b - a) * ((i : ℝ) / n) := by ring
      _ < a + (b - a) * ((j : ℝ) / n) := by gcongr
      _ = a + (b - a) * (j : ℝ) / n := by ring
  have htmem (i : ℕ) (hi : i ≤ n) : t i ∈ Icc a b := by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
    dsimp only [t]
    constructor
    · have hnonneg : 0 ≤ (b - a) * (i : ℝ) / (n : ℝ) :=
        div_nonneg (mul_nonneg (sub_nonneg.mpr hab) hi0) hnR.le
      linarith only [hnonneg]
    · have hle : (i : ℝ) / n ≤ 1 := (div_le_iff₀ hnR).2 (by simpa using hin)
      have hmul := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hab)
      have hnorm : (b - a) * (i : ℝ) / n =
          (b - a) * ((i : ℝ) / n) := by ring
      rw [hnorm]
      nlinarith only [hmul]
  have htstep (i : ℕ) : t (i + 1) - t i = (b - a) / (n : ℝ) := by
    dsimp only [t]
    push_cast
    ring
  have hlocalStep (i : ℕ) (hi : i ∈ Finset.range n) :
      E (P (t i), P (t (i + 1))) ≤
        (c : ℝ≥0∞) * D (P (t i), P (t (i + 1))) := by
    have hi' : i < n := Finset.mem_range.mp hi
    have hi1 : i + 1 ≤ n := by omega
    have hdistTime : dist (t i) (t (i + 1)) < ε := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg]
      · rw [htstep]
        exact hstep
      · rw [htstep]
        exact div_nonneg (sub_nonneg.mpr hab) hnR.le
    exact hLocal _ _ (hUC (t i) (htmem i hi'.le)
      (t (i + 1)) (htmem (i + 1) hi1) hdistTime)
  have hEchain : E (P a, P b) ≤
      ∑ i ∈ Finset.range n, E (P (t i), P (t (i + 1))) := by
    simpa only [ht0, htn] using endpoint_le_chain E P t n
  have hsumD : (∑ i ∈ Finset.range n, D (P (t (i + 1)), P (t i))) ≤
      D.len P a b := by
    rw [D.len_eq_partitionSup]
    exact le_iSup_of_le n <| le_iSup_of_le t <|
      le_iSup_of_le htmono <| le_iSup_of_le ht0 <| le_iSup_of_le htn le_rfl
  calc
    E (P a, P b) ≤
        ∑ i ∈ Finset.range n, E (P (t i), P (t (i + 1))) := hEchain
    _ ≤ ∑ i ∈ Finset.range n,
        (c : ℝ≥0∞) * D (P (t i), P (t (i + 1))) :=
          Finset.sum_le_sum hlocalStep
    _ = (c : ℝ≥0∞) *
        ∑ i ∈ Finset.range n, D (P (t (i + 1)), P (t i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [D.isExtMetric.2.2.1 (P (t i)) (P (t (i + 1)))]
    _ ≤ (c : ℝ≥0∞) * D.len P a b := by gcongr

 

theorem near_comparison_of_dense_centers
    (D E : LSCMetric) (c : NNReal)
    (S : Set ℂ) (hDense : Dense S)
    (hCenters : ∀ a ∈ S, ∀ x ∈ Metric.closedBall a 1,
      ∀ y ∈ Metric.closedBall a 1,
        E (x, y) ≤ (c : ℝ≥0∞) * D (x, y)) :
    ∀ x y : ℂ, dist x y < 1 →
      E (x, y) ≤ (c : ℝ≥0∞) * D (x, y) := by
  intro x y hxy
  have hrad : 0 < 1 - dist x y := sub_pos.mpr hxy
  obtain ⟨a, haS, ha⟩ :=
    hDense.exists_mem_open Metric.isOpen_ball
      ⟨x, Metric.mem_ball_self hrad⟩
  have hax : dist a x < 1 - dist x y := by
    simpa only [Metric.mem_ball] using ha
  have hx : x ∈ Metric.closedBall a 1 := by
    rw [Metric.mem_closedBall, dist_comm]
    have hnonneg : 0 ≤ dist x y := dist_nonneg
    linarith only [hax, hnonneg]
  have hy : y ∈ Metric.closedBall a 1 := by
    rw [Metric.mem_closedBall]
    have htri := dist_triangle y x a
    rw [dist_comm y x, dist_comm x a] at htri
    linarith only [htri, hax]
  exact hCenters a haS x hx y hy

 

theorem allPairs_of_local_comparison
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → ContinuousOn P (Icc a b))
    (hLocal : ∀ x y : ℂ, dist x y < 1 →
      E (x, y) ≤ (c : ℝ≥0∞) * D (x, y)) :
    ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y) := by
  intro x y
  rw [(D.isLengthSpace_iff_eq_iInf.mp hDlen) x y]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hcTop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun ha => le_iInf fun hb => ?_
  rw [← ha, ← hb]
  exact endpoint_le_length_of_local_comparison D E c hLocal
    P a b hP.1 (hDreg P a b hP)

 
theorem G_iff_projected_witness (D E : LSCMetric)
    (r κ C : Set.Ioi (0 : ℝ)) :
    G D E r κ C ↔
      ∃ z w : ℂ, Toolkit.MovingEndpoints.GWitness r κ C ((D, E), (z, w)) := by
  simp only [G, Toolkit.MovingEndpoints.GWitness, Toolkit.MovingEndpoints.movingOpenSetDist,
    ← setDist_eq_iInf_prod, ratioPair_iff_finite_positive]
  simp only [and_assoc]

theorem GEvent_um_local (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    (r κ C : Set.Ioi (0 : ℝ)) :
    LQGMetric.UMeasurableSet (GEvent D E r κ C) := by
  have h := Toolkit.MovingEndpoints.GWitnessEvent_um D E hD hE r κ C
  have heq : GEvent D E r κ C =
      {g : DistC | ∃ z w : ℂ, Toolkit.MovingEndpoints.GWitness r κ C ((D g, E g), (z, w))} := by
    ext g
    exact G_iff_projected_witness (D g) (E g) r κ C
  exact heq ▸ h

 

theorem ae_no_G_normalized_translate
    (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (C : Set.Ioi (0 : ℝ))
    (hNo : ∀ κ : Set.Ioi (0 : ℝ),
      P {ω : Ω | G (D (h ω)) (E (h ω))
        ⟨1, by norm_num⟩ κ C} = 0)
    (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ κ : Set.Ioi (0 : ℝ),
      ¬ G
        (D (LQGMetric.addConst (translateDist z (h ω))
          (-LQGMetric.circleAvg (h ω) 1 z)))
        (E (LQGMetric.addConst (translateDist z (h ω))
          (-LQGMetric.circleAvg (h ω) 1 z)))
        ⟨1, by norm_num⟩ κ C := by
  let k : Ω → DistC := fun ω =>
    LQGMetric.addConst (translateDist z (h ω))
      (-LQGMetric.circleAvg (h ω) 1 z)
  have hhk : IsNormalizedWholePlaneGFF k P := by
    simpa only [k] using normalized_translate_sub_circleAvg hh z
  have hlaw : P.map k = P.map h := by
    simpa only [k] using map_normalized_translate_sub_circleAvg hh z
  let κn : ℕ → Set.Ioi (0 : ℝ) := fun n =>
    ⟨1 / (n + 1 : ℝ), by
      simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity)⟩
  have hNoneNat : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ¬ G (D (k ω)) (E (k ω)) ⟨1, by norm_num⟩ (κn n) C := by
    apply MeasureTheory.ae_all_iff.mpr
    intro n
    let S : Set DistC := GEvent D E ⟨1, by norm_num⟩ (κn n) C
    have hS : NullMeasurableSet S (P.map h) :=
      (GEvent_um_local D E hD hE ⟨1, by norm_num⟩ (κn n) C).nullMeasurableSet _
    have hSk : NullMeasurableSet S (P.map k) :=
      (GEvent_um_local D E hD hE ⟨1, by norm_num⟩ (κn n) C).nullMeasurableSet _
    have hzero : P {ω : Ω | G (D (k ω)) (E (k ω))
        ⟨1, by norm_num⟩ (κn n) C} = 0 := by
      calc
        P {ω : Ω | G (D (k ω)) (E (k ω))
            ⟨1, by norm_num⟩ (κn n) C} =
            (P.map k) S := by
              exact (Measure.map_apply₀ hhk.1.measurable.aemeasurable hSk).symm
        _ = (P.map h) S := by rw [hlaw]
        _ = P {ω : Ω | G (D (h ω)) (E (h ω))
            ⟨1, by norm_num⟩ (κn n) C} :=
              Measure.map_apply₀ hh.1.measurable.aemeasurable hS
        _ = 0 := hNo (κn n)
    exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hNoneNat] with ω hnone κ hG
  obtain ⟨n, hn⟩ :=
    (OptimalConstants.Bridge.exists_G_iff_exists_nat_radius
      (D (k ω)) (E (k ω)) ⟨1, by norm_num⟩ C).1 ⟨κ, hG⟩
  exact hnone n hn

 

theorem ae_closedBall_comparison_at_center
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (C : Set.Ioi (0 : ℝ))
    (hNo : ∀ κ : Set.Ioi (0 : ℝ),
      P {ω : Ω | G (D (h ω)) (E (h ω))
        ⟨1, by norm_num⟩ κ C} = 0)
    (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ x ∈ Metric.closedBall z 1,
      ∀ y ∈ Metric.closedBall z 1,
        E (h ω) (x, y) ≤ ENNReal.ofReal (C : ℝ) * D (h ω) (x, y) := by
  let t : Ω → DistC := fun ω => translateDist z (h ω)
  let k : Ω → DistC := fun ω =>
    LQGMetric.addConst (t ω) (-LQGMetric.circleAvg (h ω) 1 z)
  have ht : LQGMetric.IsWholePlaneGFF t P := by
    simpa only [t, translateDist_eq_affineComp_one] using
      hh.1.affineComp one_pos z
  have htPlus : LQGMetric.IsGFFPlusCont t P :=
    LQGMetric.GM.detGFFPlusCont ht
  have hhPlus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hh.1
  have hNoK : ∀ᵐ ω ∂P, ∀ κ : Set.Ioi (0 : ℝ),
      ¬ G (D (k ω)) (E (k ω)) ⟨1, by norm_num⟩ κ C := by
    simpa only [k, t] using
      ae_no_G_normalized_translate D E hD.measurable hE.measurable
        P h hh C hNo z
  filter_upwards [hNoK,
    hD.translation P h hhPlus z, hE.translation P h hhPlus z,
    hD.length P t htPlus, hE.length P t htPlus,
    hD.weyl P t htPlus, hE.weyl P t htPlus]
    with ω hno htransD htransE hLD hLE hwD hwE
  let scale : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp ((ξ : ℝ) * (-LQGMetric.circleAvg (h ω) 1 z)))
  have hs0 : scale ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hsTop : scale ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdScale (x y : ℂ) :
      D (k ω) (x, y) = scale * D (t ω) (x, y) := by
    have hw := hwD (ContinuousMap.const ℂ (-LQGMetric.circleAvg (h ω) 1 z))
    have hc := weylScale_const (ξ : ℝ)
      (-LQGMetric.circleAvg (h ω) 1 z) (D (t ω)) hLD (x, y)
    simpa only [k, LQGMetric.addConst, scale] using (hw ▸ hc)
  have heScale (x y : ℂ) :
      E (k ω) (x, y) = scale * E (t ω) (x, y) := by
    have hw := hwE (ContinuousMap.const ℂ (-LQGMetric.circleAvg (h ω) 1 z))
    have hc := weylScale_const (ξ : ℝ)
      (-LQGMetric.circleAvg (h ω) 1 z) (E (t ω)) hLE (x, y)
    simpa only [k, LQGMetric.addConst, scale] using (hw ▸ hc)
  have hcompK :=
    closedBall_comparison_of_no_G (D (k ω)) (E (k ω)) C hno
  intro x hx y hy
  have hx0 : x - z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero,
      zero_sub, norm_neg, norm_sub_rev] using hx
  have hy0 : y - z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero,
      zero_sub, norm_neg, norm_sub_rev] using hy
  have hscaled := hcompK (x - z) hx0 (y - z) hy0
  rw [heScale, hdScale] at hscaled
  have htranslated :
      E (t ω) (x - z, y - z) ≤
        ENNReal.ofReal (C : ℝ) * D (t ω) (x - z, y - z) := by
    apply (ENNReal.mul_le_mul_iff_right hs0 hsTop).1
    simpa only [mul_left_comm, mul_assoc] using hscaled
  have hd (p q : ℂ) :
      D (t ω) (p - z, q - z) = D (h ω) (p, q) := by
    have hh := htransD (p - z) (q - z)
    simpa only [t, sub_add_cancel] using hh
  have he (p q : ℂ) :
      E (t ω) (p - z, q - z) = E (h ω) (p, q) := by
    have hh := htransE (p - z) (q - z)
    simpa only [t, sub_add_cancel] using hh
  simpa only [hd, he] using htranslated

 


theorem ae_allPairs_of_no_unit_G
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (C : Set.Ioi (0 : ℝ))
    (hNo : ∀ κ : Set.Ioi (0 : ℝ),
      P {ω : Ω | G (D (h ω)) (E (h ω))
        ⟨1, by norm_num⟩ κ C} = 0) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ,
      E (h ω) (x, y) ≤ ENNReal.ofReal (C : ℝ) * D (h ω) (x, y) := by
  obtain ⟨S, hCount, hDense⟩ :=
    TopologicalSpace.exists_countable_dense ℂ
  have : Countable S := hCount.to_subtype
  have hCenters : ∀ᵐ ω ∂P,
      ∀ a : S, ∀ x ∈ Metric.closedBall (a : ℂ) 1,
        ∀ y ∈ Metric.closedBall (a : ℂ) 1,
          E (h ω) (x, y) ≤
            ENNReal.ofReal (C : ℝ) * D (h ω) (x, y) := by
    apply MeasureTheory.ae_all_iff.mpr
    intro a
    exact ae_closedBall_comparison_at_center
      ξ Q D E hD hE P h hh C hNo a
  have hPlus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hh.1
  have hDlen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace :=
    hD.length P h hPlus
  have hDreg : ∀ᵐ ω ∂P,
      ∀ (γ : ℝ → ℂ) (s t : ℝ),
        (D (h ω)).IsCurve γ s t → ContinuousOn γ (Icc s t) := by
    filter_upwards [BiLipschitz.Barrier.ae_curves_continuous hD hQ P h hh] with ω hreg
    exact hreg.2.1
  let c : NNReal := Real.toNNReal (C : ℝ)
  have hc : 0 < c := by
    have hC : (0 : ℝ) < (C : ℝ) := C.property
    simpa only [c, Real.lt_toNNReal_iff_coe_lt, NNReal.coe_zero] using hC
  have hcoe : (c : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) := rfl
  filter_upwards [hCenters, hDlen, hDreg] with ω hcent hlen hreg
  have hLocal : ∀ x y : ℂ, dist x y < 1 →
      E (h ω) (x, y) ≤ (c : ℝ≥0∞) * D (h ω) (x, y) := by
    apply near_comparison_of_dense_centers (D (h ω)) (E (h ω)) c S hDense
    intro a ha x hx y hy
    simpa only [hcoe] using hcent ⟨a, ha⟩ x hx y hy
  intro x y
  simpa only [hcoe] using
    allPairs_of_local_comparison (D (h ω)) (E (h ω)) c hc
      hlen hreg hLocal x y

 

theorem upperOptimal_le_of_allPairs (D E : LSCMetric) (C : ℝ≥0∞)
    (hAll : ∀ x y : ℂ, E (x, y) ≤ C * D (x, y)) :
    upperOptimal D E ≤ C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply iSup_le
  intro hp
  exact (ENNReal.div_le_iff' hp.2.2.2.1.ne' hp.2.2.2.2.ne).2
    (by simpa only [mul_comm] using hAll x y)

 

theorem positive_unit_G_of_upperOptimal_ae_constant
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (cPlus : ℝ≥0∞)
    (hPlus : ∀ᵐ ω ∂P, upperOptimal (D (h ω)) (E (h ω)) = cPlus)
    (C : Set.Ioi (0 : ℝ))
    (hC : ENNReal.ofReal (C : ℝ) < cPlus) :
    ∃ κ : Set.Ioi (0 : ℝ),
      0 < P {ω : Ω | G (D (h ω)) (E (h ω))
        ⟨1, by norm_num⟩ κ C} := by
  by_contra hn
  have hNo : ∀ κ : Set.Ioi (0 : ℝ),
      P {ω : Ω | G (D (h ω)) (E (h ω))
        ⟨1, by norm_num⟩ κ C} = 0 := by
    intro κ
    have hnot : ¬ 0 < P {ω : Ω | G (D (h ω)) (E (h ω))
        ⟨1, by norm_num⟩ κ C} := by
      intro hp
      exact hn ⟨κ, hp⟩
    exact le_antisymm (le_of_not_gt hnot) bot_le
  have hAll := ae_allPairs_of_no_unit_G
    ξ Q hQ D E hD hE P h hh C hNo
  obtain ⟨ω, hω, hOpt⟩ := (hAll.and hPlus).exists
  have hbound : cPlus ≤ ENNReal.ofReal (C : ℝ) := by
    rw [← hOpt]
    exact upperOptimal_le_of_allPairs (D (h ω)) (E (h ω))
      (ENNReal.ofReal (C : ℝ)) hω
  exact (not_lt_of_ge hbound) hC

 

theorem lem_opt_pos_unit
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ cPlus : ℝ≥0∞, 0 < cPlus ∧ cPlus < ⊤ ∧
      ∀ C : Set.Ioi (0 : ℝ),
        ENNReal.ofReal (C : ℝ) < cPlus →
        ∃ κ : Set.Ioi (0 : ℝ),
          0 < P {ω : Ω | G (D (h ω)) (E (h ω))
            ⟨1, by norm_num⟩ κ C} := by
  obtain ⟨_cMinus, cPlus, _hMinusPos, _hMinusTop, hPlusPos, hPlusTop,
    _hMinus, hPlus⟩ := OptimalConstants.Determinism.hDET_proved ξ Q hQ D E hD hE P h hh
  refine ⟨cPlus, hPlusPos, hPlusTop, ?_⟩
  intro C hC
  exact positive_unit_G_of_upperOptimal_ae_constant
    ξ Q hQ D E hD hE P h hh cPlus hPlus C hC




end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit
