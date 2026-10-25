import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 





set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Bridge

open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios

 

theorem exists_ball_setDist_ge_of_lt (D : LSCMetric) (z w : ℂ)
    {t : ℝ≥0∞} (ht : t < D (z, w)) :
    ∃ ε : ℝ, 0 < ε ∧ t ≤ setDist D (Metric.ball z ε) (Metric.ball w ε) := by
  have ho : IsOpen {p : ℂ × ℂ | t < D p} := by
    exact D.lowerSemicontinuous.isOpen_preimage t
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho (z, w) ht
  refine ⟨ε, hε, ?_⟩
  apply le_iInf₂
  intro x hx
  apply le_iInf₂
  intro y hy
  have hxy : (x, y) ∈ Metric.ball (z, w) ε := by
    rw [← ball_prod_same]
    exact ⟨hx, hy⟩
  exact le_of_lt (hball hxy)

 


theorem point_eq_iSup_ball_setDist (D : LSCMetric) (z w : ℂ) :
    D (z, w) = ⨆ ε : Set.Ioi (0 : ℝ),
      setDist D (Metric.ball z ε) (Metric.ball w ε) := by
  apply le_antisymm
  · by_contra h
    have hlt : (⨆ ε : Set.Ioi (0 : ℝ),
        setDist D (Metric.ball z ε) (Metric.ball w ε)) < D (z, w) :=
      lt_of_not_ge h
    obtain ⟨t, hsup_t, ht⟩ := exists_between hlt
    obtain ⟨ε, hε, hbound⟩ := exists_ball_setDist_ge_of_lt D z w ht
    have hle : setDist D (Metric.ball z ε) (Metric.ball w ε) ≤
        (⨆ δ : Set.Ioi (0 : ℝ),
          setDist D (Metric.ball z δ) (Metric.ball w δ)) :=
      le_iSup (fun δ : Set.Ioi (0 : ℝ) =>
        setDist D (Metric.ball z δ) (Metric.ball w δ)) ⟨ε, hε⟩
    exact (not_lt_of_ge (hbound.trans hle)) hsup_t
  · apply iSup_le
    intro ε
    exact iInf₂_le_of_le z (Metric.mem_ball_self ε.property)
      (iInf₂_le w (Metric.mem_ball_self ε.property))

theorem setDist_ball_antitone_radius (D : LSCMetric) (z w : ℂ)
    {ρ ε : ℝ} (hρε : ρ ≤ ε) :
    setDist D (Metric.ball z ε) (Metric.ball w ε) ≤
      setDist D (Metric.ball z ρ) (Metric.ball w ρ) := by
  apply le_iInf₂
  intro x hx
  apply le_iInf₂
  intro y hy
  exact iInf₂_le_of_le x (Metric.ball_subset_ball hρε hx)
    (iInf₂_le y (Metric.ball_subset_ball hρε hy))

 
theorem tendsto_shrinking_ball_setDist (D : LSCMetric) (z w : ℂ) :
    Tendsto (fun n : ℕ =>
      setDist D (Metric.ball z (1 / (n + 1 : ℝ)))
        (Metric.ball w (1 / (n + 1 : ℝ)))) atTop (𝓝 (D (z, w))) := by
  let f : ℕ → ℝ≥0∞ := fun n =>
    setDist D (Metric.ball z (1 / (n + 1 : ℝ)))
      (Metric.ball w (1 / (n + 1 : ℝ)))
  have hm : Monotone f := by
    intro n m hnm
    apply setDist_ball_antitone_radius D z w
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hs : (⨆ n, f n) = D (z, w) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      exact iInf₂_le_of_le z (Metric.mem_ball_self (by positivity))
        (iInf₂_le w (Metric.mem_ball_self (by positivity)))
    · by_contra h
      have hlt : (⨆ n, f n) < D (z, w) := lt_of_not_ge h
      obtain ⟨t, hsup_t, ht⟩ := exists_between hlt
      obtain ⟨ε, hε, hbound⟩ := exists_ball_setDist_ge_of_lt D z w ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have hle : setDist D (Metric.ball z ε) (Metric.ball w ε) ≤ f n :=
        setDist_ball_antitone_radius D z w hn.le
      exact (not_lt_of_ge (hbound.trans (hle.trans (le_iSup f n)))) hsup_t
  simpa only [f, ← hs] using tendsto_atTop_iSup hm

 

theorem exists_G_one_of_strict_local_pair (D D' : LSCMetric)
    (C : Set.Ioi (0 : ℝ)) {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1)
    (hp : RatioPair D z w)
    (hstrict : ENNReal.ofReal (C : ℝ) * D (z, w) < D' (z, w)) :
    ∃ κ : Set.Ioi (0 : ℝ),
      G D D' ⟨1, by norm_num⟩ κ C := by
  obtain ⟨ε, hε, hbound⟩ :=
    exists_ball_setDist_ge_of_lt D' z w hstrict
  refine ⟨⟨ε, hε⟩, z, w, hz, hw, hp, ?_⟩
  simpa only [mul_one] using hbound

 

theorem ratioPair_of_H_witness (D : LSCMetric)
    (r : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    {u v : ℂ} (hu : u ∈ Metric.sphere (0 : ℂ) (a * r))
    (hv : v ∈ Metric.sphere (0 : ℂ) r)
    (hfinite : D (u, v) < ⊤) : RatioPair D u v := by
  have hrad : (a : ℝ) * r < r := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right a.property.2 r.property
  have hu' : dist u (0 : ℂ) = a * r := by
    simpa only [Metric.mem_sphere, dist_comm] using hu
  have hv' : dist v (0 : ℂ) = r := by
    simpa only [Metric.mem_sphere, dist_comm] using hv
  have hne : u ≠ v := by
    intro h
    rw [h] at hu'
    exact (ne_of_lt hrad) (hu'.symm.trans hv')
  have hpos : 0 < D (u, v) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    exact hne (D.isExtMetric.2.1 u v hzero)
  exact (ratioPair_iff_finite_positive D u v).2 ⟨hne, hpos, hfinite⟩

 
theorem exists_strict_pair_of_lt_upperOptimal (D D' : LSCMetric)
    {c : ℝ≥0∞} (hc : c < upperOptimal D D') :
    ∃ z w : ℂ, RatioPair D z w ∧ c * D (z, w) < D' (z, w) := by
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hc
  obtain ⟨w, hw⟩ := lt_iSup_iff.mp hz
  obtain ⟨hp, hratio⟩ := lt_iSup_iff.mp hw
  refine ⟨z, w, hp, ?_⟩
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hp.2.2.2.1.ne')
    (Or.inl hp.2.2.2.2.ne)).mp hratio

 
theorem G_mono_ball_radius (D D' : LSCMetric)
    (r C κ κ' : Set.Ioi (0 : ℝ)) (hκ : (κ' : ℝ) ≤ κ)
    (hG : G D D' r κ C) : G D D' r κ' C := by
  obtain ⟨z, w, hz, hw, hp, hbound⟩ := hG
  refine ⟨z, w, hz, hw, hp, hbound.trans ?_⟩
  apply setDist_ball_antitone_radius D' z w
  exact mul_le_mul_of_nonneg_right hκ r.property.le

 
theorem exists_G_iff_exists_nat_radius (D D' : LSCMetric)
    (r C : Set.Ioi (0 : ℝ)) :
    (∃ κ : Set.Ioi (0 : ℝ), G D D' r κ C) ↔
      ∃ n : ℕ, G D D' r ⟨1 / (n + 1 : ℝ), by
        simpa only [Set.mem_Ioi] using (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity)⟩ C := by
  constructor
  · rintro ⟨κ, hκ⟩
    have hκpos : (0 : ℝ) < κ := by simpa only [Set.mem_Ioi] using κ.property
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hκpos
    exact ⟨n, G_mono_ball_radius D D' r C κ
      ⟨1 / (n + 1 : ℝ), by
        simpa only [Set.mem_Ioi] using (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity)⟩ hn.le hκ⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨1 / (n + 1 : ℝ), by
      simpa only [Set.mem_Ioi] using (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity)⟩, hn⟩


end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Bridge
