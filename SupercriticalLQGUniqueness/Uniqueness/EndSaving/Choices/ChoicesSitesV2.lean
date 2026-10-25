import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChoicesNumV2




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
def oneIoi : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩

 
theorem covered_level_sites {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (η : Set.Ioo (0 : ℝ) 1) (b : Set.Ioi (0 : ℝ)) (ε : ℝ) (hε : 0 < ε)
    (hεη : ε ≤ (η : ℝ) / 1000)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁)
    (hball₁ : K₁ ⊆ ball (0 : ℂ) (2 * (b : ℝ)))
    (hsep₁₂ : ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ EndSaving.Interfaces.euclidSetDist K₁ K₂)
    (hsep₁b : ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ EndSaving.Interfaces.euclidSetDist K₁ (sphere (0 : ℂ) b))
    (ω : Ω) (hbr : ℝ)
    (hsize : ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ ε * (b : ℝ) →
      ∀ z ∈ ball (0 : ℂ) (3 * (b : ℝ)),
        ∃ hrz : ℝ, IsCircleAverage (h ω) r z hrz ∧
          EndSaving.InterfaceV2.PrintedSizeWindow ξ Q ⟨ε, hε⟩ b r hbr hrz)
    (hcover : ∀ z ∈ ball (0 : ℂ) (3 * (b : ℝ)),
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈ ball z ((r : ℝ) / 25) ∧
        h ω ∈ (family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr).E)
    (P : ℝ → ℂ) (T : ℝ) (hP : ContinuousOn P (Icc 0 T)) (hT : 0 ≤ T)
    (hP0 : P 0 ∈ K₁) (hPT : P T ∈ K₂) :
    ∃ (t : ℕ → ℝ) (rr : ℕ → Set.Ioi (0 : ℝ))
      (ii : ℕ → ℤ × ℤ) (hrz : ℕ → ℝ) (ℓ : ℕ → ℤ),
      ∀ j ≤ nLev η ε,
        let w := LQGMetric.GM.gridPt (((rr j : ℝ)) / 100) (ii j)
        t j ∈ Icc 0 T ∧ (rr j).1 ∈ R.radii ∧
        ε ^ 2 * (b : ℝ) ≤ (rr j : ℝ) ∧ (rr j : ℝ) ≤ ε * (b : ℝ) ∧
        P (t j) ∈ ball w ((rr j : ℝ) / 25) ∧
        (∃ hr : (rr j).1 ∈ R.radii, h ω ∈ (family w (rr j) hr).E) ∧
        IsCircleAverage (h ω) (rr j) w (hrz j) ∧
        (2 : ℝ) ^ (ℓ j) * scaleB ξ Q b oneIoi hbr ≤ scaleN ξ Q (rr j) (hrz j) ∧
        scaleN ξ Q (rr j) (hrz j) ≤ 2 * (2 : ℝ) ^ (ℓ j) * scaleB ξ Q b oneIoi hbr ∧
        (1 / 2) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) ≤ (2 : ℝ) ^ (ℓ j) ∧
        (2 : ℝ) ^ (ℓ j) ≤ ε ^ ((ξ : ℝ) * (Q - 3)) ∧
        Disjoint (ball w (4 * (rr j : ℝ))) (K₁ ∪ K₂ ∪ sphere (0 : ℂ) b) ∧
        ∀ j' ≤ nLev η ε, j ≠ j' →
          Disjoint (ball w (4 * (rr j : ℝ)))
            (ball (LQGMetric.GM.gridPt (((rr j' : ℝ)) / 100) (ii j')) (4 * (rr j' : ℝ))) := by
  set J := nLev η ε with hJ
  have hb : (0 : ℝ) < b := b.property
  have hη0 : (0 : ℝ) < η := η.property.1
  have hη1 : (η : ℝ) < 1 := η.property.2
  have hε1 : ε ≤ 1 := hεη.trans (by linarith)
  have h8 : 8 * ε ≤ (η : ℝ) / 4 := by linarith
  have hne₁ : K₁.Nonempty := ⟨P 0, hP0⟩
  
  set lev : ℕ → ℝ := fun j => 8 * ε * b + (j : ℝ) * (11 * ε * b) with hlev
  have hlevle : ∀ j ≤ J, lev j ≤ (η : ℝ) * b / 4 := by
    intro j hj
    have := nLev_level_le hε h8 j hj
    simp only [hlev]
    nlinarith
  have hPTfar : (η : ℝ) * b ≤ Metric.infDist (P T) K₁ := by
    rw [Metric.le_infDist hne₁]
    intro y hy
    rw [dist_comm]
    exact le_dist_of_euclidSetDist hsep₁₂ hy hPT
  obtain ⟨t, ht⟩ := exists_level_times hP hT hP0 hPTfar lev J
    (fun j _ => by simp only [hlev]; positivity)
    (fun j hj => (hlevle j hj).trans (by nlinarith))
  
  have hnear : ∀ j ≤ J, Metric.infDist (P (t j)) K₁ ≤ (η : ℝ) * b / 4 := by
    intro j hj; rw [(ht j hj).2]; exact hlevle j hj
  have hin3 : ∀ j ≤ J, ‖P (t j)‖ < 2 * b + (η : ℝ) * b / 4 := by
    intro j hj
    obtain ⟨w, hw, hwx⟩ := hK₁.exists_infDist_eq_dist hne₁ (P (t j))
    have hw2 := mem_ball_zero_iff.mp (hball₁ hw)
    have : ‖P (t j)‖ ≤ ‖w‖ + dist (P (t j)) w := by
      have := norm_le_norm_add_norm_sub' (P (t j)) w
      rw [dist_eq_norm]; linarith [norm_sub_rev (P (t j)) w]
    rw [← hwx] at this
    linarith [hnear j hj]
  have hx3 : ∀ j ≤ J, P (t j) ∈ ball (0 : ℂ) (3 * (b : ℝ)) := by
    intro j hj
    rw [mem_ball_zero_iff]
    nlinarith [hin3 j hj]
  
  have hcov : ∀ j, j ≤ J → ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
      LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈ ball (P (t j)) ((r : ℝ) / 25) ∧
      h ω ∈ (family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr).E :=
    fun j hj => hcover _ (hx3 j hj)
  choose! rr hrr ii hrlo hrhi hwx hEw using hcov
  set w : ℕ → ℂ := fun j => LQGMetric.GM.gridPt (((rr j : ℝ)) / 100) (ii j) with hw
  have hr0 : ∀ j, (0 : ℝ) < rr j := fun j => (rr j).property
  have hwx' : ∀ j ≤ J, dist (P (t j)) (w j) < (rr j : ℝ) / 25 := by
    intro j hj
    have := hwx j hj
    rw [mem_ball, dist_comm] at this
    exact this
  have hw3 : ∀ j ≤ J, w j ∈ ball (0 : ℂ) (3 * (b : ℝ)) := by
    intro j hj
    rw [mem_ball_zero_iff]
    have h1 := hin3 j hj
    have h2 := hwx' j hj
    have h3 := hrhi j hj
    have : ‖w j‖ ≤ ‖P (t j)‖ + dist (P (t j)) (w j) := by
      rw [dist_eq_norm]
      have := norm_le_norm_add_norm_sub' (w j) (P (t j))
      linarith [norm_sub_rev (P (t j)) (w j)]
    nlinarith
  
  have hsz : ∀ j, j ≤ J → ∃ c : ℝ, IsCircleAverage (h ω) (rr j) (w j) c ∧
      EndSaving.InterfaceV2.PrintedSizeWindow ξ Q ⟨ε, hε⟩ b (rr j) hbr c := by
    intro j hj
    obtain ⟨c, hc, hwin⟩ := hsize (rr j) (hrr j hj) (hrlo j hj) (hrhi j hj) (w j) (hw3 j hj)
    exact ⟨c, hc, hwin⟩
  choose! hrz hrzc hwin using hsz
  set B₀ := scaleB ξ Q b oneIoi hbr with hB₀
  have hB₀pos : 0 < B₀ := scaleB_pos ξ Q b oneIoi hbr
  have hbin : ∀ j, j ≤ J → ∃ ℓ : ℤ, (2 : ℝ) ^ ℓ * B₀ ≤ scaleN ξ Q (rr j) (hrz j) ∧
      scaleN ξ Q (rr j) (hrz j) ≤ 2 * (2 : ℝ) ^ ℓ * B₀ := by
    intro j _
    obtain ⟨ℓ, h1, h2, _⟩ := exists_dyadic_bin (div_pos (scaleN_pos ξ Q (rr j) (hrz j)) hB₀pos)
    refine ⟨ℓ, ?_, ?_⟩
    · rwa [le_div_iff₀ hB₀pos] at h1
    · rwa [div_le_iff₀ hB₀pos] at h2
  choose! ℓ hℓ1 hℓ2 using hbin
  have hB₀eq : B₀ = (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) := by
    simp only [hB₀, scaleB, oneIoi, one_mul]
  refine ⟨t, rr, ii, hrz, ℓ, ?_⟩
  intro j hj
  have hεb : (0 : ℝ) < ε * b := by positivity
  refine ⟨(ht j hj).1, hrr j hj, hrlo j hj, hrhi j hj, mem_ball.mpr (hwx' j hj),
    ⟨hrr j hj, hEw j hj⟩, hrzc j hj,
    hℓ1 j hj, hℓ2 j hj, ?_, ?_, ?_, ?_⟩
  · 
    have hw1 := (hwin j hj).1
    have h2 := hℓ2 j hj
    simp only [scaleN] at h2
    rw [hB₀eq] at h2
    have hpos : 0 < (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) := by
      have := Real.rpow_pos_of_pos hb ((ξ : ℝ) * Q); positivity
    have : ε ^ (2 * (ξ : ℝ) * (Q + 3)) * ((b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) ≤
        2 * (2 : ℝ) ^ (ℓ j) * ((b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) := by
      have := hw1.trans h2
      simpa only [mul_assoc] using this
    have := le_of_mul_le_mul_right this hpos
    linarith
  · 
    have hw2 := (hwin j hj).2
    have h1 := hℓ1 j hj
    simp only [scaleN] at h1
    rw [hB₀eq] at h1
    have hpos : 0 < (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) := by
      have := Real.rpow_pos_of_pos hb ((ξ : ℝ) * Q); positivity
    have : (2 : ℝ) ^ (ℓ j) * ((b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) ≤
        ε ^ ((ξ : ℝ) * (Q - 3)) * ((b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) := by
      have := h1.trans hw2
      simpa only [mul_assoc] using this
    exact le_of_mul_le_mul_right this hpos
  · 
    rw [Set.disjoint_left]
    intro y hy hyK
    rw [mem_ball] at hy
    have hd := hwx' j hj
    have hr := hrhi j hj
    have htri : dist (P (t j)) y ≤ dist (P (t j)) (w j) + dist (w j) y := dist_triangle _ _ _
    rcases hyK with (hy1 | hy2) | hyb
    · have hlow : lev j ≤ dist (P (t j)) y := by
        rw [← (ht j hj).2]; exact Metric.infDist_le_dist_of_mem hy1
      have : 8 * ε * b ≤ lev j := by
        show 8 * ε * b ≤ 8 * ε * b + (j : ℝ) * (11 * ε * b)
        have : (0 : ℝ) ≤ (j : ℝ) * (11 * ε * b) := by positivity
        linarith
      rw [dist_comm] at hy
      linarith
    · have hfar := far_of_near hK₁ hne₁ hsep₁₂ (hnear j hj) hy2
      rw [dist_comm] at hy
      nlinarith
    · have hfar := far_of_near hK₁ hne₁ hsep₁b (hnear j hj) hyb
      rw [dist_comm] at hy
      nlinarith
  · 
    intro j' hj' hjj'
    apply Metric.ball_disjoint_ball
    have hsep : 11 * ε * b ≤ dist (P (t j)) (P (t j')) := by
      have h := level_points_sep (K := K₁) (x := P (t j)) (y := P (t j'))
      rw [(ht j hj).2, (ht j' hj').2] at h
      have hdiff : 11 * ε * b ≤ |lev j - lev j'| := by
        simp only [hlev]
        have hne : (j : ℝ) ≠ (j' : ℝ) := by exact_mod_cast hjj'
        have h1 : (1 : ℝ) ≤ |(j : ℝ) - (j' : ℝ)| := by
          rcases lt_or_gt_of_ne hjj' with hlt | hgt
          · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hlt
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast hgt
            rw [abs_of_nonneg (by linarith)]; linarith
        have heq : 8 * ε * b + (j : ℝ) * (11 * ε * b) - (8 * ε * b + (j' : ℝ) * (11 * ε * b)) =
            ((j : ℝ) - j') * (11 * ε * b) := by ring
        rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 11 * ε * b)]
        nlinarith
      linarith
    have htri : dist (P (t j)) (P (t j')) ≤
        dist (P (t j)) (w j) + dist (w j) (w j') + dist (w j') (P (t j')) := by
      have := dist_triangle4 (P (t j)) (w j) (w j') (P (t j'))
      linarith
    have h1 := hwx' j hj
    have h2 := hwx' j' hj'
    rw [dist_comm] at h2
    have h3 := hrhi j hj
    have h4 := hrhi j' hj'
    nlinarith


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
