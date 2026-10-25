import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAngleWindow

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 

theorem laneC_positive_turn_bounded_sweep
    (D : ContMetric) {τ M : ℝ → ℂ}
    (hc : τ 0 = τ 1)
    (hM : ContinuousOn M (Icc (0 : ℝ) 1))
    (hperiod : 2 * Real.pi ≤ (M 1 - M 0).im) :
    ∃ (k : ℤ) (s t : ℝ),
      s ∈ Icc (0 : ℝ) 2 ∧ t ∈ Icc (0 : ℝ) 2 ∧
      s ≤ t ∧ t ≤ s + 1 ∧
      (laneCRepeatLift M s).im = Real.pi + 2 * Real.pi * (k : ℝ) ∧
      (laneCRepeatLift M t).im = 5 * Real.pi / 2 + 2 * Real.pi * (k : ℝ) ∧
      (∀ x ∈ Icc s t,
        Real.pi + 2 * Real.pi * (k : ℝ) ≤
          (laneCRepeatLift M x).im ∧
        (laneCRepeatLift M x).im ≤
          5 * Real.pi / 2 + 2 * Real.pi * (k : ℝ)) ∧
      D.len (SupercriticalLQGUniqueness.B2.Strong.seg
        (laneCRepeatLoop τ) s t) 0 1 ≤ D.len τ 0 1 := by
  let w : ℝ := (M 0).im
  obtain ⟨k, hwlo, hwhi⟩ := laneC_exists_west_level w
  let A : ℝ := Real.pi + 2 * Real.pi * (k : ℝ)
  let B : ℝ := A + 3 * Real.pi / 2
  have hπ : 0 < Real.pi := Real.pi_pos
  have hMend : A ≤ (M 1).im := by
    have hsub : (M 1 - M 0).im = (M 1).im - (M 0).im :=
      Complex.sub_im _ _
    dsimp [A, w] at hwlo hwhi ⊢
    linarith
  have hMim : ContinuousOn (fun x => (M x).im) (Icc (0 : ℝ) 1) :=
    Complex.continuous_im.comp_continuousOn hM
  obtain ⟨q, hq, hqA⟩ : ∃ q ∈ Icc (0 : ℝ) 1, (M q).im = A :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hMim
      ⟨hwlo, hMend⟩
  have hRq : (laneCRepeatLift M q).im = A := by
    rw [(laneC_repeatLift_first M) (x := q) hq]
    exact hqA
  have hRend : B ≤ (laneCRepeatLift M (q + 1)).im := by
    rw [laneC_repeatLift_shift M hq, Complex.add_im, Complex.sub_im]
    dsimp [B]
    rw [Complex.sub_im] at hperiod
    linarith
  have hq2 : q + 1 ≤ 2 := by linarith [hq.2]
  have hRcont : ContinuousOn (fun x => (laneCRepeatLift M x).im)
      (Icc q (q + 1)) := by
    have h := laneC_repeatLift_continuousOn hM
    exact (Complex.continuous_im.comp_continuousOn h).mono
      (Icc_subset_Icc hq.1 hq2)
  obtain ⟨s, hs, t, ht, hst, hsA, htB, hband⟩ :=
    laneC_exists_bounded_level_sweep (A := A) (B := B)
      (by linarith : q ≤ q + 1)
      (by dsimp [B]; linarith) hRcont hRq.le hRend
  have hs2 : s ∈ Icc (0 : ℝ) 2 :=
    ⟨hq.1.trans hs.1, hs.2.trans hq2⟩
  have ht2 : t ∈ Icc (0 : ℝ) 2 :=
    ⟨hq.1.trans ht.1, ht.2.trans hq2⟩
  refine ⟨k, s, t, hs2, ht2, hst,
    (by linarith [ht.2, hs.1]), ?_, ?_, ?_, ?_⟩
  · simpa [A] using hsA
  · dsimp [B, A] at htB
    convert htB using 1; ring
  · intro x hx
    have h := hband x hx
    constructor
    · simpa [A] using h.1
    · dsimp [B, A] at h
      convert h.2 using 1; ring
  · exact laneC_repeatLoop_segment_cost_any D hc hs2 hst ht2.2
      (by linarith [ht.2, hs.1])

end SupercriticalLQGUniqueness.B2.DG20Conc
