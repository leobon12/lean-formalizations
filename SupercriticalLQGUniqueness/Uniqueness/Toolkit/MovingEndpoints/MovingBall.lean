import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact




 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.MovingEndpoints

 

def closedBallPathInf (D : LSCMetric) (c : ℂ) (R : ℝ) (x y : ℂ) : ENNReal :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b)
    (_ : ∀ t ∈ Icc a b, P t ∈ Metric.closedBall c R)
    (_ : P a = x) (_ : P b = y), D.len P a b

 

theorem compact_path_limit_moving_ball {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D)) {K : Set ℂ} (hK : IsCompact K)
    {c : ℕ → ℂ} {R : ℕ → ℝ} {c₀ : ℂ} {R₀ : ℝ}
    (hc : Tendsto c atTop (nhds c₀)) (hR : Tendsto R atTop (nhds R₀))
    {x y : ℕ → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x atTop (nhds x₀)) (hy : Tendsto y atTop (nhds y₀))
    {P : ℕ → unitInterval → ℂ} (htrace : ∀ n t, P n t ∈ K)
    (hball : ∀ n t, P n t ∈ Metric.closedBall (c n) (R n))
    (hends : ∀ n, P n 0 = x n ∧ P n 1 = y n)
    {M : NNReal} (hLip : ∀ n, LipschitzWith M ((G n).pt ∘ P n))
    {L : ENNReal}
    (hbound : ∀ n, (G n).len (fun t => P n (projIcc 0 1 zero_le_one t)) 0 1 ≤ L) :
    ∃ P₀ : C(unitInterval, ℂ),
      D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ∧
      (∀ t, P₀ t ∈ Metric.closedBall c₀ R₀) ∧ P₀ 0 = x₀ ∧ P₀ 1 = y₀ ∧
      D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L := by
  obtain ⟨φ, P₀, hφ, hlim, htrace₀⟩ :=
    Toolkit.CompactPathInfimum.compact_trace_path_subseq hG hK htrace hLip
  have hGφ : Tendsto (fun n => G (φ n)) atTop (nhds D) :=
    hG.comp hφ.tendsto_atTop
  have hDlip : LipschitzWith M (D.pt ∘ P₀) :=
    Toolkit.PathInfimum.lipschitz_limit_of_epi hGφ hlim (fun n => hLip (φ n))
  have hcurve : D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact (hDlip.continuous.comp continuous_projIcc).continuousOn
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => P (φ n) (projIcc 0 1 zero_le_one t)) atTop
        (nhds (P₀ (projIcc 0 1 zero_le_one t))) :=
    fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hlen := Toolkit.CompactPathInfimum.joint_len_le_liminf hGφ hpoint
  have hlen' : D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L :=
    hlen.trans (liminf_le_of_frequently_le'
      (Frequently.of_forall fun n => hbound (φ n)))
  have hball₀ (t : unitInterval) : P₀ t ∈ Metric.closedBall c₀ R₀ := by
    have hdist : Tendsto (fun n => dist (P (φ n) t) (c (φ n))) atTop
        (nhds (dist (P₀ t) c₀)) :=
      (hlim.tendsto_at t).dist (hc.comp hφ.tendsto_atTop)
    have hRφ : Tendsto (fun n => R (φ n)) atTop (nhds R₀) :=
      hR.comp hφ.tendsto_atTop
    exact Metric.mem_closedBall.mpr <|
      le_of_tendsto_of_tendsto' hdist hRφ
        (fun n => Metric.mem_closedBall.mp (hball (φ n) t))
  have hstart : P₀ 0 = x₀ := by
    have ht : Tendsto (fun n => P (φ n) 0) atTop (nhds (P₀ 0)) :=
      hlim.tendsto_at 0
    have heq : (fun n => P (φ n) 0) = (fun n => x (φ n)) :=
      funext fun n => (hends (φ n)).1
    rw [heq] at ht
    exact tendsto_nhds_unique ht
      (by simpa only [Function.comp_def] using hx.comp hφ.tendsto_atTop)
  have hend : P₀ 1 = y₀ := by
    have ht : Tendsto (fun n => P (φ n) 1) atTop (nhds (P₀ 1)) :=
      hlim.tendsto_at 1
    have heq : (fun n => P (φ n) 1) = (fun n => y (φ n)) :=
      funext fun n => (hends (φ n)).2
    rw [heq] at ht
    exact tendsto_nhds_unique ht
      (by simpa only [Function.comp_def] using hy.comp hφ.tendsto_atTop)
  exact ⟨P₀, hcurve, hball₀, hstart, hend, hlen'⟩

 

theorem closedBallPathInf_seq_liminf_of_common_compact
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (nhds D))
    {K : Set ℂ} (hK : IsCompact K)
    {c : ℕ → ℂ} {R : ℕ → ℝ} {c₀ : ℂ} {R₀ : ℝ}
    (hc : Tendsto c atTop (nhds c₀)) (hR : Tendsto R atTop (nhds R₀))
    (hcontain : ∀ n, Metric.closedBall (c n) (R n) ⊆ K)
    {x y : ℕ → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x atTop (nhds x₀)) (hy : Tendsto y atTop (nhds y₀)) :
    closedBallPathInf D c₀ R₀ x₀ y₀ ≤
      liminf (fun n => closedBallPathInf (G n) (c n) (R n) (x n) (y n)) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have hwfin : w ≠ ∞ := ne_top_of_lt hw
  have htail : ∀ᶠ n in atTop,
      w ≤ closedBallPathInf (G n) (c n) (R n) (x n) (y n) := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n,
        closedBallPathInf (G (φ n)) (c (φ n)) (R (φ n))
          (x (φ n)) (y (φ n)) < w := fun n => lt_of_not_ge (hbad n)
    have hpaths : ∀ n, ∃ (P : ℝ → ℂ) (a b : ℝ),
        (G (φ n)).IsCurve P a b ∧
        (∀ t ∈ Icc a b, P t ∈ Metric.closedBall (c (φ n)) (R (φ n))) ∧
        P a = x (φ n) ∧ P b = y (φ n) ∧
        (G (φ n)).len P a b < w := by
      intro n
      unfold closedBallPathInf at hbad'
      obtain ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩ :=
        (by simpa only [iInf_lt_iff] using hbad' n)
      exact ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩
    choose P a b hP htrace hEa hFb hlen using hpaths
    have hfin : ∀ n, (G (φ n)).len (P n) (a n) (b n) ≠ ∞ :=
      fun n => ne_top_of_lt (hlen n)
    have htrace' : ∀ n, P n '' Icc (a n) (b n) ⊆
        Metric.closedBall (c (φ n)) (R (φ n)) := by
      intro n z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact htrace n t ht
    choose γ hγlen hγtrace hγlip using fun n =>
      Toolkit.CompactPathInfimum.exists_lipschitz_reparam (G (φ n)) (P n) (hP n) (hfin n) (htrace' n)
    let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
    have hQball : ∀ n t, Q n t ∈ Metric.closedBall (c (φ n)) (R (φ n)) :=
      fun n t => hγtrace n t
    have hQtrace : ∀ n t, Q n t ∈ K :=
      fun n t => hcontain (φ n) (hQball n t)
    have hQends : ∀ n, Q n 0 = x (φ n) ∧ Q n 1 = y (φ n) := by
      intro n
      change (γ n 0 : ℂ) = x (φ n) ∧ (γ n 1 : ℂ) = y (φ n)
      rw [(γ n).source, (γ n).target]
      exact ⟨hEa n, hFb n⟩
    have hQlip : ∀ n, LipschitzWith w.toNNReal
        ((G (φ n)).pt ∘ Q n) := by
      intro n
      have hmono : ((G (φ n)).len (P n) (a n) (b n)).toNNReal ≤ w.toNNReal :=
        ENNReal.toNNReal_mono hwfin (hlen n).le
      exact (hγlip n).weaken hmono
    have hQbound : ∀ n,
        (G (φ n)).len (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 ≤ w := by
      intro n
      change LQGMetric.MetricGeometry.pathLength (γ n) ≤ w
      exact (hγlen n).le.trans (hlen n).le
    obtain ⟨P₀, hP₀, hB₀, hE₀, hF₀, hlen₀⟩ :=
      compact_path_limit_moving_ball (hG.comp hφ.tendsto_atTop) hK
        (by simpa only [Function.comp_def] using hc.comp hφ.tendsto_atTop)
        (by simpa only [Function.comp_def] using hR.comp hφ.tendsto_atTop)
        (by simpa only [Function.comp_def] using hx.comp hφ.tendsto_atTop)
        (by simpa only [Function.comp_def] using hy.comp hφ.tendsto_atTop)
        hQtrace hQball hQends hQlip hQbound
    have hInf : closedBallPathInf D c₀ R₀ x₀ y₀ ≤
        D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
      unfold closedBallPathInf
      apply iInf_le_of_le (fun t => P₀ (projIcc 0 1 zero_le_one t))
      apply iInf_le_of_le (0 : ℝ)
      apply iInf_le_of_le (1 : ℝ)
      apply iInf_le_of_le hP₀
      apply iInf_le_of_le ?_
      · exact iInf_le_of_le (by simpa using hE₀) <|
          iInf_le_of_le (by simpa using hF₀) le_rfl
      · intro t ht
        change P₀ (projIcc 0 1 zero_le_one t) ∈ Metric.closedBall c₀ R₀
        rw [projIcc_of_mem zero_le_one ht]
        exact hB₀ ⟨t, ht⟩
    exact (not_le_of_gt hw) (hInf.trans hlen₀)
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

 

theorem closedBallPathInf_seq_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (nhds D))
    {c : ℕ → ℂ} {R : ℕ → ℝ} {c₀ : ℂ} {R₀ : ℝ}
    (hc : Tendsto c atTop (nhds c₀)) (hR : Tendsto R atTop (nhds R₀))
    {x y : ℕ → ℂ} {x₀ y₀ : ℂ}
    (hx : Tendsto x atTop (nhds x₀)) (hy : Tendsto y atTop (nhds y₀)) :
    closedBallPathInf D c₀ R₀ x₀ y₀ ≤
      liminf (fun n => closedBallPathInf (G n) (c n) (R n) (x n) (y n)) atTop := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto c hc).subset_closedBall 0
  obtain ⟨S, hS⟩ := (Metric.isBounded_range_of_tendsto R hR).subset_closedBall 0
  let K : Set ℂ := Metric.closedBall 0 (C + S)
  have hK : IsCompact K := isCompact_closedBall 0 (C + S)
  have hcontain (n : ℕ) : Metric.closedBall (c n) (R n) ⊆ K := by
    intro z hz
    have hcn : dist (c n) 0 ≤ C := hC ⟨n, rfl⟩
    have hRn : R n ≤ S := by
      have hRn' : dist (R n) 0 ≤ S := hS ⟨n, rfl⟩
      rw [Real.dist_eq, sub_zero] at hRn'
      exact (le_abs_self _).trans hRn'
    exact Metric.mem_closedBall.mpr (by
      calc
        dist z 0 ≤ dist z (c n) + dist (c n) 0 := dist_triangle _ _ _
        _ ≤ R n + C := add_le_add (Metric.mem_closedBall.mp hz) hcn
        _ ≤ C + S := by linarith only [hRn])
  exact closedBallPathInf_seq_liminf_of_common_compact hG hK hc hR hcontain hx hy

 

theorem closedBallPathInf_joint_lsc :
    LowerSemicontinuous
      (fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
        closedBallPathInf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hcCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) => q.2.1) := by
    fun_prop
  have hRCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) => q.2.2.1) := by
    fun_prop
  have hxCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) => q.2.2.2.1) := by
    fun_prop
  have hyCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) => q.2.2.2.2) := by
    fun_prop
  exact closedBallPathInf_seq_liminf hm
    ((hcCont.tendsto p).comp hG) ((hRCont.tendsto p).comp hG)
    ((hxCont.tendsto p).comp hG) ((hyCont.tendsto p).comp hG)

 

theorem closedBallPathInf_joint_borel :
    @Measurable (LSCMetric × (ℂ × (ℝ × (ℂ × ℂ)))) ENNReal (borel _) inferInstance
      (fun p => closedBallPathInf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × (ℝ × (ℂ × ℂ)))) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (ℂ × (ℝ × (ℂ × ℂ)))) := ⟨le_rfl⟩
  exact closedBallPathInf_joint_lsc.measurable

 
theorem internal_closedBall_eq_closedBallPathInf (D : LSCMetric) (c : ℂ) (R : ℝ)
    {x y : ℂ} (hx : x ∈ Metric.closedBall c R)
    (hy : y ∈ Metric.closedBall c R) :
    D.internal (Metric.closedBall c R) (⟨x, hx⟩, ⟨y, hy⟩) =
      closedBallPathInf D c R x y := rfl

 
abbrev ClosedBallInput : Type :=
  {p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) //
    p.2.2.2.1 ∈ Metric.closedBall p.2.1 p.2.2.1 ∧
    p.2.2.2.2 ∈ Metric.closedBall p.2.1 p.2.2.1}

 
def closedBallInternal (p : ClosedBallInput) : ENNReal :=
  p.1.1.internal (Metric.closedBall p.1.2.1 p.1.2.2.1)
    (⟨p.1.2.2.2.1, p.2.1⟩, ⟨p.1.2.2.2.2, p.2.2⟩)

 

theorem closedBallInternal_joint_borel :
    @Measurable ClosedBallInput ENNReal (borel _) inferInstance closedBallInternal := by
  have hval : @Measurable ClosedBallInput
      (LSCMetric × (ℂ × (ℝ × (ℂ × ℂ)))) (borel _) (borel _)
      (fun p => p.1) := continuous_subtype_val.borel_measurable
  convert closedBallPathInf_joint_borel.comp hval using 1
  funext p
  exact internal_closedBall_eq_closedBallPathInf p.1.1 p.1.2.1 p.1.2.2.1
    p.2.1 p.2.2

 
theorem jointEval_lsc :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) => p.1 p.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hq : Tendsto (fun n => (G n).2) atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hG
  exact (LSCMetric.tendsto_iff.mp hm).1 (fun n => (G n).2) p.2 hq

 
theorem jointEval_borel :
    @Measurable (LSCMetric × (ℂ × ℂ)) ENNReal (borel _) inferInstance
      (fun p => p.1 p.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × ℂ)) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (ℂ × ℂ)) := ⟨le_rfl⟩
  exact jointEval_lsc.measurable


end Uniqueness.Toolkit.MovingEndpoints
end SupercriticalLQGUniqueness
