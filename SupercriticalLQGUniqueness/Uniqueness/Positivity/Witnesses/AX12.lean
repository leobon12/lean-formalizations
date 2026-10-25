import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import NV1Evidence




 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses

open LQGMetric (DistC circleAvg)
open SupercriticalLQGUniqueness

def largeAnnulus : EuclideanAnnulus :=
  ⟨(0, 1, 2), by constructor <;> norm_num⟩

def smallAnnulus (j : Fin 11) : EuclideanAnnulus :=
  ⟨(((1 + (j : ℕ) / 10 : ℝ) : ℂ), 1 / 15, 2 / 15),
    by constructor <;> norm_num⟩

def witnessAnnulus (i : Fin 12) : EuclideanAnnulus :=
  if hi : i.val = 0 then largeAnnulus
  else smallAnnulus ⟨i.val - 1, by omega⟩

theorem witnessAnnulus_zero : witnessAnnulus 0 = largeAnnulus := by
  simp [witnessAnnulus]

theorem witnessAnnulus_succ (j : Fin 11) :
    witnessAnnulus ⟨j.val + 1, by omega⟩ = smallAnnulus j := by
  simp only [witnessAnnulus, Fin.val_mk, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, not_false_eq_true, dif_neg, Nat.add_sub_cancel_right]

 
theorem witnessAnnulus_subset_ball_three (i : Fin 12) :
    (witnessAnnulus i).toSet ⊆ Metric.ball (0 : ℂ) 3 := by
  classical
  by_cases hi : i.val = 0
  · intro x hx
    have hbig : witnessAnnulus i = largeAnnulus := by simp only [witnessAnnulus, dif_pos hi]
    rw [hbig] at hx
    have hx2 : dist x 0 < 2 := hx.1
    exact Metric.mem_ball.mpr (lt_trans hx2 (by norm_num))
  · let j : Fin 11 := ⟨i.val - 1, by omega⟩
    have hsmall : witnessAnnulus i = smallAnnulus j := by
      simp only [witnessAnnulus, dif_neg hi]
      congr 1
    intro x hx
    rw [hsmall] at hx
    have hxrad : dist x (smallAnnulus j).center < (smallAnnulus j).outerRadius := hx.1
    have hj : (j.val : ℝ) ≤ 10 := by
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hc : dist (smallAnnulus j).center 0 ≤ 2 := by
      change dist (((1 + (j.val : ℝ) / 10 : ℝ) : ℂ)) 0 ≤ 2
      rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have houter : (smallAnnulus j).outerRadius = 2 / 15 := rfl
    apply Metric.mem_ball.mpr
    calc
      dist x 0 ≤ dist x (smallAnnulus j).center + dist (smallAnnulus j).center 0 :=
        dist_triangle _ _ _
      _ < 2 / 15 + 2 := by rw [houter] at hxrad; linarith
      _ < 3 := by norm_num

 
theorem aroundDist_exists_curve (D : LSCMetric) (A : EuclideanAnnulus)
    (M : ℝ) (hM : 0 ≤ M) (h : aroundDist D A ≤ ENNReal.ofReal M) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ A.toSet) ∧
      Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary ∧
      D.len P a b ≤ ENNReal.ofReal (M + 1) := by
  have hlt : aroundDist D A < ENNReal.ofReal (M + 1) :=
    lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  unfold aroundDist at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨P, a, b, hP, hA, hdisc, hlen⟩ := hlt
  exact ⟨P, a, b, hP, hA, hdisc, hlen.le⟩

 
theorem aroundCurve_trace_geometry (D : LSCMetric) (A : EuclideanAnnulus)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hA : ∀ t ∈ Icc a b, P t ∈ A.toSet)
    (hdisc : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary) :
    IsCompact (P '' Icc a b) ∧ IsPathConnected (P '' Icc a b) ∧
      (∃ x ∈ P '' Icc a b, ∃ y ∈ P '' Icc a b,
        2 * A.innerRadius ≤ dist x y) := by
  have hbounded : Bornology.IsBounded (P '' Icc a b) := by
    apply (Metric.isBounded_ball (x := A.center) (r := A.outerRadius)).subset
    rintro x ⟨t, ht, rfl⟩
    exact (hA t ht).1
  have hcont := D.continuousOn_euclidean_of_bounded P hP hbounded
  refine ⟨isCompact_Icc.image_of_continuousOn hcont,
    (convex_Icc a b).isPathConnected
      ⟨a, left_mem_Icc.mpr hP.1⟩ |>.image' hcont, ?_⟩
  exact disconnects_has_opposite_points A.innerRadius_pos.le
    A.innerRadius_lt_outerRadius.le hdisc

theorem dilate_one (A : EuclideanAnnulus) :
    A.dilate 1 one_pos = A := by
  apply Subtype.ext
  rcases A with ⟨⟨z, r, R⟩, hA⟩
  simp [EuclideanAnnulus.dilate, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius]

 
theorem ae_around_radius_one {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (A : EuclideanAnnulus) :
    (fun ω => ENNReal.ofReal ((1 : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) 1 0))) *
      aroundDist (D (h ω)) (A.dilate 1 one_pos)) =ᵐ[P]
    (fun ω => aroundDist (D (h ω)) A) := by
  filter_upwards [hh.2] with ω hω
  have hc : circleAvg (h ω) 1 0 = 0 := hω.limUnder_eq
  simp only [hc, mul_zero, neg_zero, Real.exp_zero, mul_one, Real.one_rpow,
    ENNReal.ofReal_one, one_mul, dilate_one]

 
theorem twelve_around_upper_tails {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ M : ℝ, 0 < M ∧ ∀ i : Fin 12,
      P {ω | ENNReal.ofReal M < aroundDist (D (h ω)) (witnessAnnulus i)} ≤
        ENNReal.ofReal (1 / 96 : ℝ) := by
  let r1 : Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let X : Fin 12 → Ω → ℝ≥0∞ := fun i ω =>
    ENNReal.ofReal ((1 : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) 1 0))) *
      aroundDist (D (h ω)) ((witnessAnnulus i).dilate 1 one_pos)
  let Y : Fin 12 → Ω → ℝ≥0∞ := fun i ω =>
    aroundDist (D (h ω)) (witnessAnnulus i)
  have hXY (i : Fin 12) : X i =ᵐ[P] Y i :=
    ae_around_radius_one P h hh ξ Q D (witnessAnnulus i)
  have htail : ∀ i : Fin 12, ∃ M : ℝ, 0 < M ∧
      P {ω | ENNReal.ofReal M < X i ω} ≤ ENNReal.ofReal (1 / 96 : ℝ) := by
    intro i
    have hV := (hD.tightness P h hh
      (fun r ω => circleAvg (h ω) r 0)
      (fun r => ae_isCircleAverage_old hh.1 r 0) (witnessAnnulus i)).2
    obtain ⟨M, hM, hbound⟩ := hV.2 (1 / 96) (by norm_num)
    exact ⟨M, hM, (hbound r1).1⟩
  choose m hm hbound using htail
  let M : ℝ := 1 + ∑ i : Fin 12, m i
  have hM : 0 < M := by
    dsimp [M]
    have hs : 0 ≤ ∑ i : Fin 12, m i := Finset.sum_nonneg fun i _ => (hm i).le
    linarith
  refine ⟨M, hM, ?_⟩
  intro i
  have hmi : m i ≤ M := by
    dsimp [M]
    have hsingle : m i ≤ ∑ j : Fin 12, m j :=
      Finset.single_le_sum (fun j _ => (hm j).le) (Finset.mem_univ i)
    linarith
  calc
    P {ω | ENNReal.ofReal M < Y i ω} =
        P {ω | ENNReal.ofReal M < X i ω} := by
      apply measure_congr
      filter_upwards [hXY i] with ω hω
      simp only [hω]
    _ ≤ P {ω | ENNReal.ofReal (m i) < X i ω} := by
      apply measure_mono
      intro ω hω
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmi) hω
    _ ≤ _ := hbound i

 
theorem twelve_around_good_event {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ (M : ℝ) (V : Set Ω), 0 < M ∧ MeasurableSet V ∧
      ENNReal.ofReal (7 / 8 : ℝ) ≤ P V ∧
      ∀ᵐ ω ∂P, ω ∈ V → ∀ i : Fin 12,
        aroundDist (D (h ω)) (witnessAnnulus i) ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM, htail⟩ := twelve_around_upper_tails P h hh ξ Q D hD
  let Y : Fin 12 → Ω → ℝ≥0∞ := fun i ω =>
    aroundDist (D (h ω)) (witnessAnnulus i)
  let r1 : Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  have hAe (i : Fin 12) : AEMeasurable (Y i) P := by
    have hV := (hD.tightness P h hh
      (fun r ω => circleAvg (h ω) r 0)
      (fun r => ae_isCircleAverage_old hh.1 r 0) (witnessAnnulus i)).2
    exact (hV.1 r1).congr (ae_around_radius_one P h hh ξ Q D (witnessAnnulus i))
  let F : Fin 12 → Ω → ℝ≥0∞ := fun i => (hAe i).mk (Y i)
  have hFm (i : Fin 12) : Measurable (F i) := (hAe i).measurable_mk
  have hFY (i : Fin 12) : F i =ᵐ[P] Y i := (hAe i).ae_eq_mk.symm
  let V : Set Ω := ⋂ i : Fin 12, {ω | F i ω ≤ ENNReal.ofReal M}
  have hVm : MeasurableSet V := MeasurableSet.iInter fun i =>
    measurableSet_le (hFm i) measurable_const
  have hFi (i : Fin 12) :
      P {ω | ENNReal.ofReal M < F i ω} ≤ ENNReal.ofReal (1 / 96 : ℝ) := by
    calc
      P {ω | ENNReal.ofReal M < F i ω} = P {ω | ENNReal.ofReal M < Y i ω} := by
        apply measure_congr
        filter_upwards [hFY i] with ω hω
        simp only [hω]
      _ ≤ _ := htail i
  have hbad : P Vᶜ ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
    calc
      P Vᶜ = P (⋃ i : Fin 12, {ω | ENNReal.ofReal M < F i ω}) := by
        simp only [V, Set.compl_iInter, Set.compl_ofPred, not_le]
      _ ≤ ∑' i : Fin 12, P {ω | ENNReal.ofReal M < F i ω} :=
        measure_iUnion_le _
      _ ≤ ∑' _i : Fin 12, ENNReal.ofReal (1 / 96 : ℝ) :=
        ENNReal.tsum_le_tsum hFi
      _ = ENNReal.ofReal (1 / 8 : ℝ) := by
        simp only [tsum_fintype]
        norm_num [ENNReal.ofReal_div_of_pos]
        have hn : (12 : NNReal) * (96 : NNReal)⁻¹ = (8 : NNReal)⁻¹ := by norm_num
        simpa using congrArg (fun x : NNReal => (x : ℝ≥0∞)) hn
  have hprob : ENNReal.ofReal (7 / 8 : ℝ) ≤ P V := by
    have h7 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 8 : ℝ) =
        ENNReal.ofReal (7 / 8 : ℝ) := by
      norm_num [ENNReal.ofReal_sub, ENNReal.ofReal_div_of_pos]
      have hn : (1 : NNReal) - (8 : NNReal)⁻¹ = (7 : NNReal) / 8 := by
        apply NNReal.eq
        norm_num [NNReal.sub_def]
      simpa using congrArg (fun x : NNReal => (x : ℝ≥0∞)) hn
    calc
      ENNReal.ofReal (7 / 8 : ℝ) = 1 - ENNReal.ofReal (1 / 8 : ℝ) := h7.symm
      _ ≤ 1 - P Vᶜ := tsub_le_tsub_left hbad 1
      _ = P V := by simpa only [compl_compl] using
        (prob_compl_eq_one_sub hVm.compl).symm
  refine ⟨M, V, hM, hVm, hprob, ?_⟩
  filter_upwards [ae_all_iff.2 hFY] with ω hω hωV i
  have hi : F i ω ≤ ENNReal.ofReal M := (Set.mem_iInter.mp hωV i)
  simpa only [hω i] using hi

 
theorem ax12_twelve_around_witnesses {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ (M : ℝ) (V : Set Ω), 0 < M ∧ MeasurableSet V ∧
      ENNReal.ofReal (7 / 8 : ℝ) ≤ P V ∧
      ∀ᵐ ω ∂P, ω ∈ V → ∀ i : Fin 12,
        ∃ (C : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve C a b ∧
          (∀ t ∈ Icc a b, C t ∈ (witnessAnnulus i).toSet) ∧
          (∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3) ∧
          Disconnects (C '' Icc a b)
            (witnessAnnulus i).innerBoundary (witnessAnnulus i).outerBoundary ∧
          (D (h ω)).len C a b ≤ ENNReal.ofReal (M + 1) ∧
          IsCompact (C '' Icc a b) ∧ IsPathConnected (C '' Icc a b) ∧
          (∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
            2 * (witnessAnnulus i).innerRadius ≤ dist x y) := by
  obtain ⟨M, V, hM, hVm, hprob, hV⟩ := twelve_around_good_event P h hh ξ Q D hD
  refine ⟨M, V, hM, hVm, hprob, ?_⟩
  filter_upwards [hV] with ω hω hωV i
  obtain ⟨C, a, b, hC, hA, hdisc, hlen⟩ :=
    aroundDist_exists_curve (D (h ω)) (witnessAnnulus i) M hM.le
      (hω hωV i)
  obtain ⟨hcompact, hpc, hdiam⟩ :=
    aroundCurve_trace_geometry (D (h ω)) (witnessAnnulus i) C a b hC hA hdisc
  have hB : ∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3 :=
    fun t ht => witnessAnnulus_subset_ball_three i (hA t ht)
  exact ⟨C, a, b, hC, hA, hB, hdisc, hlen, hcompact, hpc, hdiam⟩

 
theorem ax12_canonical_witnesses (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ (M : ℝ) (V : Set DistC), 0 < M ∧ MeasurableSet V ∧
      ENNReal.ofReal (7 / 8 : ℝ) ≤ μ V ∧
      ∀ᵐ u ∂μ, u ∈ V → ∀ i : Fin 12,
        ∃ (C : ℝ → ℂ) (a b : ℝ), (D u).IsCurve C a b ∧
          (∀ t ∈ Icc a b, C t ∈ (witnessAnnulus i).toSet) ∧
          (∀ t ∈ Icc a b, C t ∈ Metric.ball (0 : ℂ) 3) ∧
          Disconnects (C '' Icc a b)
            (witnessAnnulus i).innerBoundary (witnessAnnulus i).outerBoundary ∧
          (D u).len C a b ≤ ENNReal.ofReal (M + 1) ∧
          IsCompact (C '' Icc a b) ∧ IsPathConnected (C '' Icc a b) ∧
          (∃ x ∈ C '' Icc a b, ∃ y ∈ C '' Icc a b,
            2 * (witnessAnnulus i).innerRadius ≤ dist x y) :=
  ax12_twelve_around_witnesses μ id hμ ξ Q D hD


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses
