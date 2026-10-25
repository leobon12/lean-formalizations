import SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls.FiniteAnnularNetwork

 




















set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 
theorem separators_intersect {K K' : Set ℂ} {z z' : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd₁ : ρ ≤ ‖z' - z‖) (hd₂ : ‖z' - z‖ ≤ 2 * ρ)
    (hK : LQGMetric.Disconnects K (sphere z ρ) (sphere z (2 * ρ)))
    (hK' : LQGMetric.Disconnects K' (sphere z' ρ) (sphere z' (2 * ρ)))
    (hpc : IsPathConnected K') : (K ∩ K').Nonempty := by
  obtain ⟨d, hd⟩ : ∃ d, d = ‖z' - z‖ := ⟨_, rfl⟩
  rw [← hd] at hd₁ hd₂
  have hd0 : 0 < d := lt_of_lt_of_le hρ hd₁
  obtain ⟨u, hu_def⟩ : ∃ u : ℂ, u = (d⁻¹ : ℝ) • (z' - z) := ⟨_, rfl⟩
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd0), ← hd,
      inv_mul_cancel₀ hd0.ne']
  have hz' : z' = z + d • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hd0.ne', one_smul]
    abel
  have hρ2 : ρ ≤ 2 * ρ := by linarith
  obtain ⟨tL, htL⟩ := Uniqueness.Toolkit.PlanarSeparation.disconnects_meets_radial_segment
    hρ.le hρ2 (u := -u) (by rw [norm_neg, hu]) hK'
  obtain ⟨tR, htR⟩ := Uniqueness.Toolkit.PlanarSeparation.disconnects_meets_radial_segment
    hρ.le hρ2 (u := u) hu hK'
  rw [Uniqueness.Toolkit.PlanarSeparation.radial_segment_formula] at htL htR
  have htL1 : (0 : ℝ) ≤ tL := tL.2.1
  have htL2 : (tL : ℝ) ≤ 1 := tL.2.2
  have htR1 : (0 : ℝ) ≤ tR := tR.2.1
  have htR2 : (tR : ℝ) ≤ 1 := tR.2.2
  refine Uniqueness.Toolkit.PlanarSeparation.disconnects_meets_pathConnected_crossing hρ2 hK hpc
    ⟨_, htL, ?_⟩ ⟨_, htR, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, hz']
    have e : z + d • u + (ρ + (tL : ℝ) * (2 * ρ - ρ)) • -u - z =
        (d - (ρ + (tL : ℝ) * (2 * ρ - ρ))) • u := by module
    rw [e, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  · rw [mem_compl_iff, mem_ball, dist_eq_norm, hz', not_lt]
    have e : z + d • u + (ρ + (tR : ℝ) * (2 * ρ - ρ)) • u - z =
        (d + (ρ + (tR : ℝ) * (2 * ρ - ρ))) • u := by module
    rw [e, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith

 

theorem preconnected_meets_separator {K L : Set ℂ} {c x y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hK : IsPreconnected K) (hx : x ∈ K) (hy : y ∈ K) (hxc : ‖x - c‖ ≤ ρ)
    (hyc : 2 * ρ ≤ ‖y - c‖) (hL : Disconnects L (sphere c ρ) (sphere c (2 * ρ))) :
    (K ∩ L).Nonempty := by
  by_contra hne
  apply hL
  have hcont : ContinuousOn (fun w : ℂ => ‖w - c‖) K :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hivt := hK.intermediate_value hx hy hcont
  obtain ⟨w₁, hw₁K, hw₁⟩ := hivt ⟨hxc, by linarith⟩
  obtain ⟨w₂, hw₂K, hw₂⟩ := hivt ⟨by linarith, hyc⟩
  refine ⟨K, hK, fun w hw hwL => hne ⟨w, hw, hwL⟩, ⟨w₁, hw₁K, ?_⟩, ⟨w₂, hw₂K, ?_⟩⟩
  · rw [mem_sphere, dist_eq_norm]; exact hw₁
  · rw [mem_sphere, dist_eq_norm]; exact hw₂

 
theorem exists_annular_chain {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    {x₁ y₁ x₂ y₂ : ℂ} (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U) (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) :
    ∃ (n : ℕ) (c : ℕ → ℂ) (ρ : ℝ), 0 < ρ ∧ (∀ i, closedBall (c i) (2 * ρ) ⊆ U) ∧
      (∀ i < n, ρ ≤ ‖c (i + 1) - c i‖ ∧ ‖c (i + 1) - c i‖ ≤ 2 * ρ) ∧
      ‖x₁ - c 0‖ ≤ ρ ∧ 3 * ρ < ‖y₁ - x₁‖ ∧ ‖x₂ - c n‖ ≤ ρ ∧ 3 * ρ < ‖y₂ - x₂‖ := by
  have hpc : IsPathConnected U := hU.isConnected_iff_isPathConnected.1 hUc
  have hJ := hpc.joinedIn x₁ hx₁ x₂ hx₂
  set γ := hJ.somePath
  have hΓ : IsCompact (range γ) := isCompact_range γ.continuous
  have hΓU : range γ ⊆ U := range_subset_iff.2 hJ.somePath_mem
  obtain ⟨δ, hδ, hδU⟩ := hΓ.exists_cthickening_subset_open hU hΓU
  have hd₁ : 0 < ‖y₁ - x₁‖ := norm_pos_iff.2 (sub_ne_zero.2 h₁.symm)
  have hd₂ : 0 < ‖y₂ - x₂‖ := norm_pos_iff.2 (sub_ne_zero.2 h₂.symm)
  set ρ : ℝ := min (δ / 2) (min (‖y₁ - x₁‖ / 4) (‖y₂ - x₂‖ / 4)) with hρ_def
  have hρ : 0 < ρ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρδ : 2 * ρ ≤ δ := by have := min_le_left (δ / 2) (min (‖y₁ - x₁‖ / 4) (‖y₂ - x₂‖ / 4)); linarith
  have hρ₁ : ρ ≤ ‖y₁ - x₁‖ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₂ : ρ ≤ ‖y₂ - x₂‖ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hball : ∀ w ∈ range γ, closedBall w (2 * ρ) ⊆ U := fun w hw =>
    (closedBall_subset_cthickening hw _).trans ((cthickening_mono hρδ _).trans hδU)
  
  obtain ⟨η, hη, hηγ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ρ hρ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  set p : ℕ → ℂ := fun j => γ (projIcc 0 1 zero_le_one ((j : ℝ) / N)) with hp_def
  have hpΓ : ∀ j, p j ∈ range γ := fun j => mem_range_self _
  have hp_step : ∀ j, ‖p (j + 1) - p j‖ < ρ := by
    intro j
    rw [← dist_eq_norm]
    apply hηγ
    calc dist (projIcc 0 1 zero_le_one (((j + 1 : ℕ) : ℝ) / N))
          (projIcc 0 1 zero_le_one ((j : ℝ) / N))
        ≤ 1 * dist (((j + 1 : ℕ) : ℝ) / N) ((j : ℝ) / N) :=
          (LipschitzWith.projIcc zero_le_one).dist_le_mul _ _
      _ = 1 / N := by
          rw [one_mul, Real.dist_eq, Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left,
            abs_of_pos (by positivity)]
      _ < η := by rwa [div_lt_iff₀ hNpos, mul_comm, ← div_lt_iff₀ hη]
  have hp0 : p 0 = x₁ := by
    simp only [hp_def, Nat.cast_zero, zero_div, projIcc_left]
    exact γ.source
  have hpN : p N = x₂ := by
    simp only [hp_def, div_self hNpos.ne', projIcc_right]
    exact γ.target
  
  have claim : ∀ j : ℕ, ∃ (m : ℕ) (c : ℕ → ℂ), c 0 = p 0 ∧ (∀ i, c i ∈ range γ) ∧
      (∀ i < m, ρ ≤ ‖c (i + 1) - c i‖ ∧ ‖c (i + 1) - c i‖ ≤ 2 * ρ) ∧ ‖c m - p j‖ < ρ := by
    intro j
    induction j with
    | zero => exact ⟨0, fun _ => p 0, rfl, fun _ => hpΓ 0, fun i hi => absurd hi (by omega),
        by simpa using hρ⟩
    | succ j ih =>
      obtain ⟨m, c, h0, hcΓ, hstep, hlast⟩ := ih
      by_cases hcl : ‖c m - p (j + 1)‖ < ρ
      · exact ⟨m, c, h0, hcΓ, hstep, hcl⟩
      · refine ⟨m + 1, fun i => if i ≤ m then c i else p (j + 1), ?_, ?_, ?_, ?_⟩
        · simp only [Nat.zero_le, ite_true]; exact h0
        · intro i; dsimp only; split_ifs
          · exact hcΓ i
          · exact hpΓ _
        · intro i hi
          by_cases him : i < m
          · have e1 : i + 1 ≤ m := him
            have e2 : i ≤ m := him.le
            simp only [e1, e2, ite_true]
            exact hstep i him
          · have him' : i = m := by omega
            subst him'
            simp only [le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false]
            have hge : ρ ≤ ‖p (j + 1) - c i‖ := by rw [norm_sub_rev]; exact le_of_not_gt hcl
            refine ⟨hge, ?_⟩
            calc ‖p (j + 1) - c i‖ ≤ ‖p (j + 1) - p j‖ + ‖p j - c i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ ρ + ρ := by
                  have := hp_step j
                  rw [norm_sub_rev] at hlast
                  linarith
              _ = 2 * ρ := by ring
        · simp only [show ¬ (m + 1 ≤ m) by omega, ite_false, sub_self, norm_zero]
          exact hρ
  obtain ⟨m, c, h0, hcΓ, hstep, hlast⟩ := claim N
  refine ⟨m, c, ρ, hρ, fun i => hball _ (hcΓ i), hstep, ?_, by linarith, ?_, by linarith⟩
  · rw [h0, hp0, sub_self, norm_zero]; exact hρ.le
  · rw [← hpN, norm_sub_rev]; exact hlast.le

end SupercriticalLQGUniqueness.B2.WeakStrong
