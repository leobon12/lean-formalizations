import SupercriticalLQGUniqueness.B2.PfeLocal.L1Main

 



















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
theorem l3_sup_ball_tendsto_zero (μ : Measure ℝ) [IsFiniteMeasure μ] (P : ℝ → ℂ) {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hfib : ∀ y : ℂ, μ (Icc a b ∩ P ⁻¹' {y}) = 0) :
    Tendsto (fun n : ℕ => ⨆ y : ℂ, μ (Icc a b ∩ P ⁻¹' ball y (1 / ((n : ℝ) + 1)))) atTop
      (𝓝 0) := by
  
  have hmeas : ∀ (y : ℂ) (ρ : ℝ), MeasurableSet (Icc a b ∩ P ⁻¹' ball y ρ) := by
    intro y ρ
    obtain ⟨U, hU, hUeq⟩ := (_root_.continuousOn_iff'.1 hP) (ball y ρ) isOpen_ball
    rw [inter_comm, hUeq]
    exact hU.measurableSet.inter measurableSet_Icc
  by_contra hcon
  rw [ENNReal.tendsto_nhds_zero] at hcon
  push Not at hcon
  obtain ⟨δ, hδ, hfreq⟩ := hcon
  
  have hfreq' : ∃ᶠ n : ℕ in atTop, ∃ y : ℂ, δ < μ (Icc a b ∩ P ⁻¹' ball y (1 / ((n : ℝ) + 1))) := by
    refine hfreq.mono fun n hn => ?_
    rw [lt_iSup_iff] at hn
    exact hn
  obtain ⟨ns, hns, hns'⟩ := Filter.extraction_of_frequently_atTop hfreq'
  choose y hy using hns'
  
  have hcK : IsCompact (P '' Icc a b) := isCompact_Icc.image_of_continuousOn hP
  have hnear : ∀ k, ∃ t ∈ Icc a b, dist (y k) (P t) < 1 := by
    intro k
    have hpos : 0 < μ (Icc a b ∩ P ⁻¹' ball (y k) (1 / ((ns k : ℝ) + 1))) :=
      lt_of_le_of_lt (zero_le) (hy k)
    obtain ⟨t, ht1, ht2⟩ := nonempty_of_measure_ne_zero hpos.ne'
    refine ⟨t, ht1, ?_⟩
    have : dist (P t) (y k) < 1 / ((ns k : ℝ) + 1) := ht2
    rw [dist_comm]
    calc dist (P t) (y k) < 1 / ((ns k : ℝ) + 1) := this
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) (ns k)]
  have hbdd : IsCompact (cthickening 1 (P '' Icc a b)) := hcK.cthickening
  have hymem : ∀ k, y k ∈ cthickening 1 (P '' Icc a b) := by
    intro k
    obtain ⟨t, ht, hdt⟩ := hnear k
    exact mem_cthickening_of_dist_le _ (P t) 1 _ ⟨t, ht, rfl⟩ hdt.le
  obtain ⟨y₀, -, φ, hφ, hlim⟩ := hbdd.tendsto_subseq hymem
  
  have hbig : ∀ ρ : ℝ, 0 < ρ → δ ≤ μ (Icc a b ∩ P ⁻¹' ball y₀ ρ) := by
    intro ρ hρ
    have hrad : Tendsto (fun k => 1 / ((ns (φ k) : ℝ) + 1)) atTop (𝓝 0) := by
      exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp ((hns.comp hφ).tendsto_atTop)
    have h1 := (tendsto_order.1 hrad).2 (ρ / 2) (by positivity)
    have h2 := (Metric.tendsto_nhds.1 hlim) (ρ / 2) (by positivity)
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    refine le_trans (hy (φ k)).le (measure_mono ?_)
    intro t ht
    refine ⟨ht.1, ?_⟩
    have := ht.2
    simp only [mem_preimage, mem_ball] at this ⊢
    have hd : dist (y (φ k)) y₀ < ρ / 2 := hk2
    calc dist (P t) y₀ ≤ dist (P t) (y (φ k)) + dist (y (φ k)) y₀ := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add (this.trans hk1) hd
      _ = ρ := by ring
  
  have hdec : Antitone fun n : ℕ => Icc a b ∩ P ⁻¹' ball y₀ (1 / ((n : ℝ) + 1)) := by
    intro n m hnm
    refine inter_subset_inter_right _ (preimage_mono (ball_subset_ball ?_))
    gcongr
  have hinter : (⋂ n : ℕ, Icc a b ∩ P ⁻¹' ball y₀ (1 / ((n : ℝ) + 1))) =
      Icc a b ∩ P ⁻¹' {y₀} := by
    ext t
    simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_ball, mem_singleton_iff]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_⟩
      by_contra hne
      have hpos : 0 < dist (P t) y₀ := dist_pos.2 hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd (h n).2 (not_lt.2 hn.le)
    · rintro ⟨h1, h2⟩ n
      refine ⟨h1, ?_⟩
      rw [h2, dist_self]; positivity
  have hlim2 := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (hmeas y₀ _).nullMeasurableSet) hdec ⟨0, measure_ne_top μ _⟩
  rw [hinter, hfib y₀] at hlim2
  have hδle : ∀ n : ℕ, δ ≤ μ (Icc a b ∩ P ⁻¹' ball y₀ (1 / ((n : ℝ) + 1))) :=
    fun n => hbig _ (by positivity)
  have := ge_of_tendsto' hlim2 hδle
  exact absurd this (not_le.2 hδ)

end SupercriticalLQGUniqueness.B2.PfeLocal
