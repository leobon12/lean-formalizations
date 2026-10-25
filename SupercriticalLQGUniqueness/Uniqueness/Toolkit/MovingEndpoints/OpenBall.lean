import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.MovingSetDist




 


set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.MovingEndpoints

 
def openBallPathInf (D : LSCMetric) (c : ℂ) (R : ℝ) (x y : ℂ) : ENNReal :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b)
    (_ : ∀ t ∈ Icc a b, P t ∈ Metric.ball c R)
    (_ : P a = x) (_ : P b = y), D.len P a b

 

theorem curve_trace_in_inner_closedBall (D : LSCMetric) (c : ℂ) (R : ℝ)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ Metric.ball c R) :
    ∃ n : ℕ, ∀ t ∈ Icc a b,
      P t ∈ Metric.closedBall c (R - 1 / (n + 1 : ℝ)) := by
  have hcont : ContinuousOn P (Icc a b) :=
    Toolkit.CountableBase.curve_continuousOn_euclidean_of_bounded D Metric.isBounded_ball hP htrace
  have hcomp : IsCompact (P '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hcont
  have hnon : (P '' Icc a b).Nonempty := by
    refine ⟨P a, a, ?_, rfl⟩
    exact left_mem_Icc.mpr hP.1
  have hdistcont : ContinuousOn (fun z : ℂ => dist z c) (P '' Icc a b) := by fun_prop
  obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn hnon hdistcont
  have hzR : dist z c < R := by
    obtain ⟨t, ht, rfl⟩ := hz
    exact Metric.mem_ball.mp (htrace t ht)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hzR)
  refine ⟨n, fun t ht => Metric.mem_closedBall.mpr ?_⟩
  have hPt : P t ∈ P '' Icc a b := ⟨t, ht, rfl⟩
  have hle : dist (P t) c ≤ dist z c := hmax hPt
  linarith only [hle, hn]

 
theorem openBallPathInf_eq_iInf_closedBallPathInf
    (D : LSCMetric) (c : ℂ) (R : ℝ) (x y : ℂ) :
    openBallPathInf D c R x y =
      ⨅ n : ℕ, closedBallPathInf D c (R - 1 / (n + 1 : ℝ)) x y := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    unfold closedBallPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hB => le_iInf fun hx => le_iInf fun hy => ?_
    have hU : ∀ t ∈ Icc a b, P t ∈ Metric.ball c R := by
      intro t ht
      have hdist := Metric.mem_closedBall.mp (hB t ht)
      exact Metric.mem_ball.mpr (by linarith only [hdist, show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity])
    unfold openBallPathInf
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <| iInf_le_of_le hU <|
      iInf_le_of_le hx <| iInf_le_of_le hy le_rfl
  · unfold openBallPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hU => le_iInf fun hx => le_iInf fun hy => ?_
    obtain ⟨n, hn⟩ := curve_trace_in_inner_closedBall D c R hP hU
    refine (iInf_le (fun n : ℕ => closedBallPathInf D c
      (R - 1 / (n + 1 : ℝ)) x y) n).trans ?_
    unfold closedBallPathInf
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <| iInf_le_of_le hn <|
      iInf_le_of_le hx <| iInf_le_of_le hy le_rfl

 

theorem openBallPathInf_joint_borel :
    @Measurable (LSCMetric × (ℂ × (ℝ × (ℂ × ℂ)))) ENNReal (borel _) inferInstance
      (fun p => openBallPathInf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × (ℝ × (ℂ × ℂ)))) := borel _
  have hm (n : ℕ) : Measurable
      (fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
        closedBallPathInf p.1 p.2.1 (p.2.2.1 - 1 / (n + 1 : ℝ))
          p.2.2.2.1 p.2.2.2.2) := by
    have hshift : Continuous (fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
        (p.1, (p.2.1, (p.2.2.1 - 1 / (n + 1 : ℝ), p.2.2.2)))) := by
      fun_prop
    have h := closedBallPathInf_joint_borel.comp hshift.borel_measurable
    simpa only [Function.comp_def] using h
  have hmi : Measurable (fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
      ⨅ n : ℕ, closedBallPathInf p.1 p.2.1
        (p.2.2.1 - 1 / (n + 1 : ℝ)) p.2.2.2.1 p.2.2.2.2) :=
    Measurable.iInf hm
  convert hmi using 1
  funext p
  exact openBallPathInf_eq_iInf_closedBallPathInf p.1 p.2.1
    p.2.2.1 p.2.2.2.1 p.2.2.2.2

 
theorem openBallPathInf_eq_internal (D : LSCMetric) (c : ℂ) (R : ℝ)
    {x y : ℂ} (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R) :
    openBallPathInf D c R x y =
      D.internal (Metric.ball c R) (⟨x, hx⟩, ⟨y, hy⟩) := rfl


end Uniqueness.Toolkit.MovingEndpoints
end SupercriticalLQGUniqueness
