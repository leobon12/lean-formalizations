import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointEval




 




set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 
def spherePairInf (D : LSCMetric) (c : ℂ) (ρ σ : ℝ) : ENNReal :=
  ⨅ x ∈ Metric.sphere c ρ, ⨅ y ∈ Metric.sphere c σ, D (x, y)

 
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

 
theorem spherePairInf_seq_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (nhds D))
    {c : ℕ → ℂ} {c₀ : ℂ} (hc : Tendsto c atTop (nhds c₀))
    {ρ σ : ℕ → ℝ} {ρ₀ σ₀ : ℝ}
    (hρ : Tendsto ρ atTop (nhds ρ₀)) (hσ : Tendsto σ atTop (nhds σ₀)) :
    spherePairInf D c₀ ρ₀ σ₀ ≤
      liminf (fun n => spherePairInf (G n) (c n) (ρ n) (σ n)) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have htail : ∀ᶠ n in atTop, w ≤ spherePairInf (G n) (c n) (ρ n) (σ n) := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n, spherePairInf (G (φ n)) (c (φ n))
        (ρ (φ n)) (σ (φ n)) < w := fun n => lt_of_not_ge (hbad n)
    have hpoints : ∀ n, ∃ x y : ℂ,
        x ∈ Metric.sphere (c (φ n)) (ρ (φ n)) ∧
        y ∈ Metric.sphere (c (φ n)) (σ (φ n)) ∧
        G (φ n) (x, y) < w := by
      intro n
      unfold spherePairInf at hbad'
      obtain ⟨x, hx, y, hy, hcost⟩ :=
        (by simpa only [iInf_lt_iff] using hbad' n)
      exact ⟨x, y, hx, hy, hcost⟩
    choose x y hxS hyS hxy using hpoints
    have hρσ : Tendsto (fun n => max (ρ (φ n)) (σ (φ n))) atTop
        (nhds (max ρ₀ σ₀)) := (hρ.comp hφ.tendsto_atTop).max
          (hσ.comp hφ.tendsto_atTop)
    obtain ⟨K, hK, hcontain⟩ := exists_common_compact_ball
      (hc.comp hφ.tendsto_atTop) hρσ
    have hxyK (n : ℕ) : (x n, y n) ∈ K ×ˢ K := by
      constructor
      · apply hcontain n
        apply Metric.mem_closedBall.mpr
        change dist (x n) (c (φ n)) ≤ max (ρ (φ n)) (σ (φ n))
        rw [Metric.mem_sphere.mp (hxS n)]
        exact le_max_left _ _
      · apply hcontain n
        apply Metric.mem_closedBall.mpr
        change dist (y n) (c (φ n)) ≤ max (ρ (φ n)) (σ (φ n))
        rw [Metric.mem_sphere.mp (hyS n)]
        exact le_max_right _ _
    obtain ⟨xy₀, _, ψ, hψ, hxyψ⟩ := (hK.prod hK).tendsto_subseq hxyK
    have hxψ : Tendsto (fun n => x (ψ n)) atTop (nhds xy₀.1) :=
      (continuous_fst.tendsto xy₀).comp hxyψ
    have hyψ : Tendsto (fun n => y (ψ n)) atTop (nhds xy₀.2) :=
      (continuous_snd.tendsto xy₀).comp hxyψ
    have hc' : Tendsto (fun n => c (φ (ψ n))) atTop (nhds c₀) :=
      (hc.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hρ' : Tendsto (fun n => ρ (φ (ψ n))) atTop (nhds ρ₀) :=
      (hρ.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hσ' : Tendsto (fun n => σ (φ (ψ n))) atTop (nhds σ₀) :=
      (hσ.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hx₀ : xy₀.1 ∈ Metric.sphere c₀ ρ₀ := by
      have hdist : Tendsto (fun n => dist (x (ψ n)) (c (φ (ψ n)))) atTop
          (nhds (dist xy₀.1 c₀)) := hxψ.dist hc'
      have heq : (fun n => dist (x (ψ n)) (c (φ (ψ n)))) =
          (fun n => ρ (φ (ψ n))) := funext fun n => Metric.mem_sphere.mp (hxS (ψ n))
      rw [heq] at hdist
      exact Metric.mem_sphere.mpr (tendsto_nhds_unique hdist hρ')
    have hy₀ : xy₀.2 ∈ Metric.sphere c₀ σ₀ := by
      have hdist : Tendsto (fun n => dist (y (ψ n)) (c (φ (ψ n)))) atTop
          (nhds (dist xy₀.2 c₀)) := hyψ.dist hc'
      have heq : (fun n => dist (y (ψ n)) (c (φ (ψ n)))) =
          (fun n => σ (φ (ψ n))) := funext fun n => Metric.mem_sphere.mp (hyS (ψ n))
      rw [heq] at hdist
      exact Metric.mem_sphere.mpr (tendsto_nhds_unique hdist hσ')
    have hmetric : Tendsto (fun n => G (φ (ψ n))) atTop (nhds D) :=
      (hG.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
    have hlsc := (LSCMetric.tendsto_iff.mp hmetric).1
      (fun n => (x (ψ n), y (ψ n))) xy₀ hxyψ
    have hlim : liminf (fun n => G (φ (ψ n)) (x (ψ n), y (ψ n))) atTop ≤ w :=
      liminf_le_of_frequently_le' (Frequently.of_forall fun n => (hxy (ψ n)).le)
    have hInf : spherePairInf D c₀ ρ₀ σ₀ ≤ D xy₀ := by
      unfold spherePairInf
      exact iInf₂_le_of_le xy₀.1 hx₀ (iInf₂_le xy₀.2 hy₀)
    exact (not_le_of_gt hw) (hInf.trans (hlsc.trans hlim))
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

 
theorem spherePairInf_joint_lsc :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × (ℝ × ℝ)) =>
      spherePairInf p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hc : Continuous (fun q : LSCMetric × (ℂ × (ℝ × ℝ)) => q.2.1) := by
    fun_prop
  have hρ : Continuous (fun q : LSCMetric × (ℂ × (ℝ × ℝ)) => q.2.2.1) := by
    fun_prop
  have hσ : Continuous (fun q : LSCMetric × (ℂ × (ℝ × ℝ)) => q.2.2.2) := by
    fun_prop
  exact spherePairInf_seq_liminf hm ((hc.tendsto p).comp hG)
    ((hρ.tendsto p).comp hG) ((hσ.tendsto p).comp hG)

 
theorem spherePairInf_joint_borel :
    @Measurable (LSCMetric × (ℂ × (ℝ × ℝ))) ENNReal (borel _) inferInstance
      (fun p => spherePairInf p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × (ℝ × ℝ))) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (ℂ × (ℝ × ℝ))) := ⟨le_rfl⟩
  exact spherePairInf_joint_lsc.measurable

 
theorem spherePairInf_joint_measurable :
    Measurable (fun p : LSCMetric × (ℂ × (ℝ × ℝ)) =>
      spherePairInf p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  spherePairInf_joint_lsc.measurable

 
theorem spherePairInf_eq_acrossDist (D : LSCMetric) (A : EuclideanAnnulus) :
    spherePairInf D A.center A.innerRadius A.outerRadius = acrossDist D A := rfl

 
theorem spherePairInf_zero_eq (D : LSCMetric) (c : ℂ) (R : ℝ) :
    spherePairInf D c 0 R = ⨅ y ∈ Metric.sphere c R, D (c, y) := by
  simp only [spherePairInf, Metric.sphere_zero, iInf_singleton]

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
