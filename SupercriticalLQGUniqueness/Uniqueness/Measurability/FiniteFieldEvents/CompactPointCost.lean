import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.OpenInternalExhaust
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointCompactPort




 





set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

theorem internal_eq_iInf_compactPointInf (D : LSCMetric)
    (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget D))
    {V : Set ℂ} (hV : IsOpen V) (hne : Vᶜ.Nonempty)
    (u v : V) :
    D.internal V (u, v) =
      ⨅ n : ℕ, Toolkit.CompactPathInfimum.compactPathInf D
        (closure (LQGMetric.LM.exhaustO V n : Set ℂ))
        {(u : ℂ)} {(v : ℂ)} := by
  unfold LSCMetric.internal
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    unfold Toolkit.CompactPathInfimum.compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hK => le_iInf fun hu => le_iInf fun hv => ?_
    have hKV : closure (LQGMetric.LM.exhaustO V n : Set ℂ) ⊆ V := by
      have hthick := LQGMetric.LM.thickening_closure_exhaustO_subset V n
      exact (self_subset_thickening (by positivity) _).trans hthick
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <| iInf_le_of_le (fun t ht => hKV (hK t ht)) <|
      iInf_le_of_le (Set.mem_singleton_iff.mp hu) <|
      iInf_le_of_le (Set.mem_singleton_iff.mp hv) le_rfl
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hVtrace => le_iInf fun hu =>
        le_iInf fun hv => ?_
    have hcont : ContinuousOn P (Icc a b) := by
      have hc := hforget.comp_continuousOn hP.2
      change ContinuousOn P (Icc a b) at hc
      exact hc
    let K : Set ℂ := P '' Icc a b
    have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hcont
    have hKV : K ⊆ V := by
      rintro x ⟨t, ht, rfl⟩
      exact hVtrace t ht
    obtain ⟨δ, hδ, hδV⟩ := hKc.exists_thickening_subset_open hV hKV
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hKW : K ⊆ LQGMetric.LM.exhaustO V n := by
      intro z hz
      show 1 / ((n : ℝ) + 1) < infDist z Vᶜ
      refine hn.trans_le ((le_infDist hne).2 fun y hy =>
        le_of_not_gt fun hlt => hy ?_)
      exact hδV (mem_thickening_iff.2 ⟨z, hz, by rw [dist_comm]; exact hlt⟩)
    refine iInf_le_of_le n ?_
    unfold Toolkit.CompactPathInfimum.compactPathInf
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <|
      iInf_le_of_le (fun t ht => subset_closure (hKW ⟨t, ht, rfl⟩)) <|
      iInf_le_of_le (Set.mem_singleton_iff.mpr hu) <|
      iInf_le_of_le (Set.mem_singleton_iff.mpr hv) le_rfl

theorem compactPointInf_total_lsc {K : Set ℂ} (hK : IsCompact K) :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) =>
      Toolkit.CompactPathInfimum.compactPathInf p.1 K {p.2.1} {p.2.2}) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hx : Tendsto (fun n => (G n).2.1) Filter.atTop (nhds p.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto p).comp hG
  have hy : Tendsto (fun n => (G n).2.2) Filter.atTop (nhds p.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto p).comp hG
  exact TwoScale.S36Events.compactPathInf_seq_liminf_moving hm hK hx hy

theorem compactPointInf_total_measurable {K : Set ℂ} (hK : IsCompact K) :
    Measurable (fun p : LSCMetric × (ℂ × ℂ) =>
      Toolkit.CompactPathInfimum.compactPathInf p.1 K {p.2.1} {p.2.2}) :=
  (compactPointInf_total_lsc hK).measurable

 

def openInternalProxy (V : Set ℂ) (p : LSCMetric × (ℂ × ℂ)) : ℝ≥0∞ :=
  ⨅ n : ℕ, Toolkit.CompactPathInfimum.compactPathInf p.1
    (closure (LQGMetric.LM.exhaustO V n : Set ℂ))
    {p.2.1} {p.2.2}

theorem openInternalProxy_measurable {V : Set ℂ}
    (hVc : IsCompact (closure V)) :
    Measurable (openInternalProxy V) := by
  unfold openInternalProxy
  exact Measurable.iInf (fun n =>
    compactPointInf_total_measurable (isCompact_closure_exhaustO hVc n))

theorem openInternalProxy_eq_internal (D : LSCMetric)
    (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget D))
    {V : Set ℂ} (hV : IsOpen V) (hne : Vᶜ.Nonempty)
    (u v : V) :
    openInternalProxy V (D, ((u : ℂ), (v : ℂ))) = D.internal V (u, v) :=
  (internal_eq_iInf_compactPointInf D hforget hV hne u v).symm

theorem openBallInternalProxy_measurable (z : ℂ) (R : ℝ) :
    Measurable (openInternalProxy (Metric.ball z R)) := by
  apply openInternalProxy_measurable
  exact (isCompact_closedBall z R).of_isClosed_subset isClosed_closure
    Metric.closure_ball_subset_closedBall

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
