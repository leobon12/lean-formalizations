import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.OpenBall




 


set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.MovingEndpoints

 
def boundaryBallInf (D : LSCMetric) (c : ℂ) (R : ℝ) (u : ℂ) : ENNReal :=
  ⨅ y ∈ Metric.sphere c R, closedBallPathInf D c R u y

 
theorem exists_common_compact_ball {c : ℕ → ℂ} {R : ℕ → ℝ}
    {c₀ : ℂ} {R₀ : ℝ} (hc : Tendsto c atTop (nhds c₀))
    (hR : Tendsto R atTop (nhds R₀)) :
    ∃ K : Set ℂ, IsCompact K ∧ ∀ n, Metric.closedBall (c n) (R n) ⊆ K := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto c hc).subset_closedBall 0
  obtain ⟨S, hS⟩ := (Metric.isBounded_range_of_tendsto R hR).subset_closedBall 0
  refine ⟨Metric.closedBall 0 (C + S), isCompact_closedBall 0 (C + S), ?_⟩
  intro n z hz
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

 

theorem boundaryBallInf_seq_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (nhds D))
    {c : ℕ → ℂ} {R : ℕ → ℝ} {c₀ : ℂ} {R₀ : ℝ}
    (hc : Tendsto c atTop (nhds c₀)) (hR : Tendsto R atTop (nhds R₀))
    {u : ℕ → ℂ} {u₀ : ℂ} (hu : Tendsto u atTop (nhds u₀)) :
    boundaryBallInf D c₀ R₀ u₀ ≤
      liminf (fun n => boundaryBallInf (G n) (c n) (R n) (u n)) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have htail : ∀ᶠ n in atTop,
      w ≤ boundaryBallInf (G n) (c n) (R n) (u n) := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n, boundaryBallInf (G (φ n)) (c (φ n)) (R (φ n))
        (u (φ n)) < w := fun n => lt_of_not_ge (hbad n)
    have hpoints : ∀ n, ∃ y : ℂ, y ∈ Metric.sphere (c (φ n)) (R (φ n)) ∧
        closedBallPathInf (G (φ n)) (c (φ n)) (R (φ n)) (u (φ n)) y < w := by
      intro n
      unfold boundaryBallInf at hbad'
      simpa only [iInf_lt_iff, exists_prop] using hbad' n
    choose y hyS hycost using hpoints
    obtain ⟨K, hK, hcontain⟩ :=
      exists_common_compact_ball (hc.comp hφ.tendsto_atTop)
        (hR.comp hφ.tendsto_atTop)
    have hyK (n : ℕ) : y n ∈ K :=
      hcontain n (Metric.sphere_subset_closedBall (hyS n))
    obtain ⟨y₀, _, ψ, hψ, hyψ⟩ := hK.tendsto_subseq hyK
    have hG' : Tendsto (fun n => G (φ (ψ n))) atTop (nhds D) :=
      (hG.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hc' : Tendsto (fun n => c (φ (ψ n))) atTop (nhds c₀) :=
      (hc.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hR' : Tendsto (fun n => R (φ (ψ n))) atTop (nhds R₀) :=
      (hR.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hu' : Tendsto (fun n => u (φ (ψ n))) atTop (nhds u₀) :=
      (hu.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hyS₀ : y₀ ∈ Metric.sphere c₀ R₀ := by
      have hdist : Tendsto (fun n => dist (y (ψ n)) (c (φ (ψ n)))) atTop
          (nhds (dist y₀ c₀)) := hyψ.dist hc'
      have heq : (fun n => dist (y (ψ n)) (c (φ (ψ n)))) =
          (fun n => R (φ (ψ n))) := by
        funext n
        exact Metric.mem_sphere.mp (hyS (ψ n))
      rw [heq] at hdist
      exact Metric.mem_sphere.mpr (tendsto_nhds_unique hdist hR')
    have hlim := closedBallPathInf_seq_liminf hG' hc' hR' hu' hyψ
    have hlim' : liminf (fun n => closedBallPathInf
        (G (φ (ψ n))) (c (φ (ψ n))) (R (φ (ψ n)))
        (u (φ (ψ n))) (y (ψ n))) atTop ≤ w :=
      liminf_le_of_frequently_le'
        (Frequently.of_forall fun n => (hycost (ψ n)).le)
    have hInf : boundaryBallInf D c₀ R₀ u₀ ≤
        closedBallPathInf D c₀ R₀ u₀ y₀ := by
      unfold boundaryBallInf
      exact iInf₂_le y₀ hyS₀
    exact (not_le_of_gt hw) (hInf.trans (hlim.trans hlim'))
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

 
theorem boundaryBallInf_joint_lsc :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × (ℝ × ℂ)) =>
      boundaryBallInf p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hcCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × ℂ)) => q.2.1) := by
    fun_prop
  have hRCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × ℂ)) => q.2.2.1) := by
    fun_prop
  have huCont : Continuous (fun q : LSCMetric × (ℂ × (ℝ × ℂ)) => q.2.2.2) := by
    fun_prop
  exact boundaryBallInf_seq_liminf hm ((hcCont.tendsto p).comp hG)
    ((hRCont.tendsto p).comp hG) ((huCont.tendsto p).comp hG)

 
theorem boundaryBallInf_joint_borel :
    @Measurable (LSCMetric × (ℂ × (ℝ × ℂ))) ENNReal (borel _) inferInstance
      (fun p => boundaryBallInf p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × (ℝ × ℂ))) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (ℂ × (ℝ × ℂ))) := ⟨le_rfl⟩
  exact boundaryBallInf_joint_lsc.measurable

 

theorem boundaryBallInf_eq_internal (D : LSCMetric) (c : ℂ) (R : ℝ)
    {u : ℂ} (hu : u ∈ Metric.closedBall c R) :
    boundaryBallInf D c R u =
      ⨅ y ∈ Metric.sphere c R,
        D.internal (Metric.closedBall c R)
          (⟨u, hu⟩, ⟨y, Metric.sphere_subset_closedBall ‹y ∈ Metric.sphere c R›⟩) := by
  unfold boundaryBallInf
  refine iInf_congr fun y => iInf_congr fun hy => ?_
  exact (internal_closedBall_eq_closedBallPathInf D c R hu
    (Metric.sphere_subset_closedBall hy)).symm


end Uniqueness.Toolkit.MovingEndpoints
end SupercriticalLQGUniqueness
