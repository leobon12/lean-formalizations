import HigherDimLQGMetric.ConvField.Affine
import HigherDimLQGMetric.Field.TestIntegral

/-!
# Test-function regularization for radial pairings

Packet L2b. This ports the continuous-translation ingredient of the two-dimensional
radial-pairing proof to `Rd d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology TopologicalSpace MeasureTheory Filter
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Continuous radial projection onto the closed unit ball. -/
def l2b_unitProj (t : Rd d) : Rd d := (max 1 ‖t‖)⁻¹ • t

theorem l2b_continuous_unitProj : Continuous (l2b_unitProj (d := d)) := by
  unfold l2b_unitProj
  have hc : Continuous fun t : Rd d => max 1 ‖t‖ := continuous_const.max continuous_norm
  have hn : ∀ t : Rd d, max 1 ‖t‖ ≠ 0 :=
    fun t => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left 1 ‖t‖))
  exact (hc.inv₀ hn).smul continuous_id

theorem l2b_norm_unitProj_le_one (t : Rd d) : ‖l2b_unitProj t‖ ≤ 1 := by
  unfold l2b_unitProj
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (lt_of_lt_of_le one_pos (le_max_left 1 ‖t‖))),
    ← div_eq_inv_mul]
  exact (div_le_one (lt_of_lt_of_le one_pos (le_max_left 1 ‖t‖))).2 (le_max_right 1 ‖t‖)

theorem l2b_unitProj_eq_self {t : Rd d} (ht : ‖t‖ ≤ 1) : l2b_unitProj t = t := by
  rw [l2b_unitProj, max_eq_left ht, inv_one, one_smul]

theorem l2b_continuous_translated_test (φ : TestRd d) (R : ℝ)
    (hφ : ∀ y : Rd d, R < ‖y‖ → φ y = 0) :
    Continuous fun t : closedBall (0 : Rd d) 1 => testAffinePull 1 (t : Rd d) φ := by
  let S := closedBall (0 : Rd d) 1
  let K : Compacts (Rd d) := ⟨closedBall 0 (R + 1), isCompact_closedBall _ _⟩
  have hs : ∀ t : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Rd d => φ (y - (t : Rd d))) := by
    intro t
    exact φ.contDiff.comp (contDiff_id.sub contDiff_const)
  have hK : ∀ t : S, ∀ y ∉ (K : Set (Rd d)), φ (y - (t : Rd d)) = 0 := by
    intro t y hy
    apply hφ
    have hyt : ‖(t : Rd d)‖ ≤ 1 := by
      simpa only [S, mem_closedBall, dist_zero_right] using t.2
    have hyR : R + 1 < ‖y‖ := by
      simpa [K, mem_closedBall, dist_zero_right] using hy
    have htri : ‖y‖ ≤ ‖y - (t : Rd d)‖ + ‖(t : Rd d)‖ := by
      calc
        ‖y‖ = ‖(y - (t : Rd d)) + t‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × Rd d =>
      iteratedFDeriv ℝ i (fun y : Rd d => φ (y - (p.1 : Rd d))) p.2 := by
    intro i
    change Continuous fun p : S × Rd d =>
      iteratedFDeriv ℝ i (fun y : Rd d => φ (y + -(p.1 : Rd d))) p.2
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K
    (fun (t : S) (y : Rd d) => φ (y - (t : Rd d))) hs hK hD
  have he : (fun t : S => testAffinePull 1 (t : Rd d) φ) =
      ofSuppRd K ∘ testFamK K
        (fun (t : S) (y : Rd d) => φ (y - (t : Rd d))) hs hK := by
    funext t
    ext y
    rw [testAffinePull_one_apply]
    rfl
  rw [he]
  exact (ofSuppRd K).continuous.comp hc

theorem l2b_continuous_projected_translate (φ : TestRd d) (R : ℝ)
    (hφ : ∀ y : Rd d, R < ‖y‖ → φ y = 0) :
    Continuous fun t : Rd d => testAffinePull 1 (l2b_unitProj t) φ := by
  let K : Compacts (Rd d) := ⟨closedBall 0 (R + 1), isCompact_closedBall _ _⟩
  have hs : ∀ t : Rd d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Rd d => φ (y - l2b_unitProj t)) := by
    intro t
    exact φ.contDiff.comp (contDiff_id.sub contDiff_const)
  have hK : ∀ t : Rd d, ∀ y ∉ (K : Set (Rd d)), φ (y - l2b_unitProj t) = 0 := by
    intro t y hy
    apply hφ
    have hyR : R + 1 < ‖y‖ := by
      simpa [K, mem_closedBall, dist_zero_right] using hy
    have htri : ‖y‖ ≤ ‖y - l2b_unitProj t‖ + ‖l2b_unitProj t‖ := by
      calc
        ‖y‖ = ‖(y - l2b_unitProj t) + l2b_unitProj t‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith [l2b_norm_unitProj_le_one t]
  have hD : ∀ i : ℕ, Continuous fun p : Rd d × Rd d =>
      iteratedFDeriv ℝ i (fun y : Rd d => φ (y - l2b_unitProj p.1)) p.2 := by
    intro i
    change Continuous fun p : Rd d × Rd d =>
      iteratedFDeriv ℝ i (fun y : Rd d => φ (y + -l2b_unitProj p.1)) p.2
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (l2b_continuous_unitProj.comp continuous_fst).neg)
  have hc := continuous_testFamK K
    (fun (t y : Rd d) => φ (y - l2b_unitProj t)) hs hK hD
  have he : (fun t : Rd d => testAffinePull 1 (l2b_unitProj t) φ) =
      ofSuppRd K ∘ testFamK K
        (fun (t y : Rd d) => φ (y - l2b_unitProj t)) hs hK := by
    funext t
    ext y
    rw [testAffinePull_one_apply]
    rfl
  rw [he]
  exact (ofSuppRd K).continuous.comp hc

theorem l2b_integral_closedBall_comap (R : ℝ) (f : Rd d → ℝ) :
    (∫ y : closedBall (0 : Rd d) R, f y ∂
      ((volume : Measure (Rd d)).restrict (closedBall 0 R)).comap Subtype.val) =
    ∫ y in closedBall (0 : Rd d) R, f y := by
  rw [integral_subtype_comap measurableSet_closedBall]
  change (∫ y, f y ∂(((volume : Measure (Rd d)).restrict (closedBall 0 R)).restrict
    (closedBall 0 R))) =
    (∫ y, f y ∂((volume : Measure (Rd d)).restrict (closedBall 0 R)))
  rw [Measure.restrict_restrict_of_subset (Subset.rfl)]

set_option linter.style.haveILetI false in
/-- Integrate a compactly supported continuous family of translated test functions, and
commute the resulting test-function integral with every distribution. -/
theorem l2b_exists_conv_pairing_on {K' : Compacts (Rd d)} (ρ φ : TestRd d)
    {R : ℝ} (hφR : ∀ y : Rd d, R < ‖y‖ → φ y = 0)
    (hK : ∀ y x : Rd d, φ y * ρ (x - y) ≠ 0 → x ∈ (K' : Set (Rd d))) :
    ∃ I : 𝓓^{⊤}_{K'}(Rd d, ℝ),
      (∀ x, I x = ∫ y : Rd d, φ y * ρ (x - y)) ∧
      ∀ T : DistRd d,
        T (ofSuppRd K' I) = ∫ y : Rd d, φ y * T (testAffinePull 1 y ρ) := by
  let S := closedBall (0 : Rd d) R
  let μ : Measure S := ((volume : Measure (Rd d)).restrict S).comap Subtype.val
  have hSc : IsCompact S := isCompact_closedBall _ _
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  haveI : IsFiniteMeasure ((volume : Measure (Rd d)).restrict S) :=
    isFiniteMeasure_restrict.2 (measure_closedBall_lt_top).ne
  haveI : IsFiniteMeasure μ := inferInstance
  let Ψ : S → Rd d → ℝ := fun y x => φ (y : Rd d) * ρ (x - (y : Rd d))
  have hs : ∀ y : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ y) := by
    intro y
    exact contDiff_const.mul (ρ.contDiff.comp (contDiff_id.sub contDiff_const))
  have hK' : ∀ y : S, ∀ x ∉ (K' : Set (Rd d)), Ψ y x = 0 := by
    intro y x hx
    by_contra hn
    exact hx (hK y x hn)
  have hD : ∀ i : ℕ, Continuous fun p : S × Rd d =>
      iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hpt (p : S × Rd d) :
        iteratedFDeriv ℝ i (Ψ p.1) p.2 =
          φ (p.1 : Rd d) • iteratedFDeriv ℝ i ρ (p.2 - (p.1 : Rd d)) := by
      dsimp only [Ψ]
      have hρt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Rd d => ρ (x - (p.1 : Rd d))) :=
        ρ.contDiff.comp (contDiff_id.sub contDiff_const)
      have hsm := iteratedFDeriv_const_smul_apply'
        (a := φ (p.1 : Rd d)) (hρt.contDiffAt.of_le (by
          exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))) (x := p.2)
      change iteratedFDeriv ℝ i (fun x : Rd d => φ (p.1 : Rd d) •
        ρ (x - (p.1 : Rd d))) p.2 = _
      rw [hsm]
      change φ (p.1 : Rd d) •
        iteratedFDeriv ℝ i (fun x : Rd d => ρ (x + -(p.1 : Rd d))) p.2 =
        φ (p.1 : Rd d) •
          iteratedFDeriv ℝ i ρ (p.2 + -(p.1 : Rd d))
      rw [iteratedFDeriv_comp_add_right]
    simp_rw [hpt]
    exact (φ.continuous.comp (continuous_subtype_val.comp continuous_fst)).smul
      ((ρ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        (continuous_snd.sub (continuous_subtype_val.comp continuous_fst)))
  have hFc := continuous_testFamK K' Ψ hs hK' hD
  obtain ⟨I, hI, hT⟩ := TestIntegral.exists_testIntegral μ hFc
  refine ⟨I, ?_, ?_⟩
  · intro x
    calc
      I x = ∫ y : S, (testFamK K' Ψ hs hK' y) x ∂μ := hI x
      _ = ∫ y : S, φ (y : Rd d) * ρ (x - (y : Rd d)) ∂μ := rfl
      _ = ∫ y in S, φ y * ρ (x - y) := by
        change (∫ y : closedBall (0 : Rd d) R,
          φ (y : Rd d) * ρ (x - (y : Rd d)) ∂
          ((volume : Measure (Rd d)).restrict (closedBall 0 R)).comap Subtype.val) = _
        exact l2b_integral_closedBall_comap (d := d) R
          (fun y : Rd d => φ y * ρ (x - y))
      _ = ∫ y : Rd d, φ y * ρ (x - y) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hyR : R < ‖y‖ := by simpa [S, mem_closedBall, dist_zero_right] using hy
        rw [hφR y hyR, zero_mul]

  · intro T
    have hEq : ∀ y : S,
        (T.comp (ofSuppRd K')) (testFamK K' Ψ hs hK' y) =
          φ (y : Rd d) * T (testAffinePull 1 (y : Rd d) ρ) := by
      intro y
      have he : ofSuppRd K' (testFamK K' Ψ hs hK' y) =
          φ (y : Rd d) • testAffinePull 1 (y : Rd d) ρ := by
        ext x
        change φ (y : Rd d) * ρ (x - (y : Rd d)) =
          φ (y : Rd d) * testAffinePull 1 (y : Rd d) ρ x
        rw [testAffinePull_one_apply]
      change T (ofSuppRd K' (testFamK K' Ψ hs hK' y)) = _
      rw [he, map_smul, smul_eq_mul]
    calc
      T (ofSuppRd K' I) = (T.comp (ofSuppRd K')) I := rfl
      _ = ∫ y : S, (T.comp (ofSuppRd K')) (testFamK K' Ψ hs hK' y) ∂μ :=
        hT (T.comp (ofSuppRd K'))
      _ = ∫ y : S, φ (y : Rd d) * T (testAffinePull 1 (y : Rd d) ρ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact hEq y
      _ = ∫ y in S, φ y * T (testAffinePull 1 y ρ) := by
        change (∫ y : closedBall (0 : Rd d) R,
          φ (y : Rd d) * T (testAffinePull 1 (y : Rd d) ρ) ∂
          ((volume : Measure (Rd d)).restrict (closedBall 0 R)).comap Subtype.val) = _
        exact l2b_integral_closedBall_comap (d := d) R
          (fun y : Rd d => φ y * T (testAffinePull 1 y ρ))
      _ = ∫ y : Rd d, φ y * T (testAffinePull 1 y ρ) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hyR : R < ‖y‖ := by simpa [S, mem_closedBall, dist_zero_right] using hy
        rw [hφR y hyR, zero_mul]


theorem l2b_exists_test_support_radius (φ : TestRd d) :
    ∃ R : ℝ, ∀ y : Rd d, R < ‖y‖ → φ y = 0 := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun y hy => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hy'
  have := hR hy'
  rw [mem_closedBall, dist_zero_right] at this
  linarith

/-- A distribution paired with an approximate identity, weighted by a test function,
recovers the original pairing. -/
theorem l2b_tendsto_integral_mul_pair_bumpTest (T : DistRd d) (φ : TestRd d) :
    Tendsto (fun n : ℕ => ∫ y : Rd d, φ y * T (bumpTest n y))
      atTop (𝓝 (T φ)) := by
  obtain ⟨R, hφR⟩ := l2b_exists_test_support_radius φ
  let K' : Compacts (Rd d) := ⟨closedBall 0 (R + 1), isCompact_closedBall _ _⟩
  let L : 𝓓^{⊤}_{K'}(Rd d, ℝ) →L[ℝ] ℝ := T.comp (ofSuppRd K')
  let c : C(Rd d, ℝ) :=
    ⟨fun t => T (testAffinePull 1 (l2b_unitProj t) φ),
      T.continuous.comp (l2b_continuous_projected_translate φ R hφR)⟩
  have hc0 : c 0 = T φ := by
    change T (testAffinePull 1 (l2b_unitProj (0 : Rd d)) φ) = T φ
    rw [l2b_unitProj_eq_self (by simp), testAffinePull_one_zero,
      ContinuousLinearMap.id_apply]
  have hlim := tendsto_ofCont_bumpTest c (0 : Rd d)
  rw [hc0] at hlim
  refine hlim.congr fun n => ?_
  symm
  have hK1 : ∀ y x : Rd d, φ y * bumpTest n 0 (x - y) ≠ 0 → x ∈ (K' : Set (Rd d)) := by
    intro y x hxy
    have hyR : ‖y‖ ≤ R := not_lt.1 fun h => left_ne_zero_of_mul hxy (hφR y h)
    have hxy1 : ‖x - y‖ < 1 := lt_of_not_ge fun h =>
      right_ne_zero_of_mul hxy (bumpTest_zero_eq_zero n h)
    change x ∈ closedBall (0 : Rd d) (R + 1)
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have hK2 : ∀ t x : Rd d, bumpTest n 0 t * φ (x - t) ≠ 0 → x ∈ (K' : Set (Rd d)) := by
    intro t x htx
    have ht1 : ‖t‖ < 1 := lt_of_not_ge fun h =>
      left_ne_zero_of_mul htx (bumpTest_zero_eq_zero n h)
    have hxtR : ‖x - t‖ ≤ R := not_lt.1 fun h =>
      right_ne_zero_of_mul htx (hφR (x - t) h)
    change x ∈ closedBall (0 : Rd d) (R + 1)
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖x‖ = ‖(x - t) + t‖ := by congr 1; abel
      _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  obtain ⟨I₁, hI₁, hT₁⟩ := l2b_exists_conv_pairing_on (K' := K') (bumpTest n 0) φ hφR hK1
  have hρR : ∀ t : Rd d, 1 < ‖t‖ → bumpTest n 0 t = 0 :=
    fun t ht => bumpTest_zero_eq_zero n ht.le
  obtain ⟨I₂, hI₂, hT₂⟩ := l2b_exists_conv_pairing_on (K' := K') φ (bumpTest n 0) hρR hK2
  have hIeq : I₁ = I₂ := by
    ext x
    rw [hI₁ x, hI₂ x]
    have hshift := integral_sub_left_eq_self
      (fun t : Rd d => bumpTest n 0 t * φ (x - t)) (volume : Measure (Rd d)) x
    simp only [sub_sub_cancel] at hshift
    calc
      (∫ y : Rd d, φ y * bumpTest n 0 (x - y)) =
          ∫ y : Rd d, bumpTest n 0 (x - y) * φ y := by
            apply integral_congr_ae
            filter_upwards [] with y
            ring
      _ = ∫ t : Rd d, bumpTest n 0 t * φ (x - t) := hshift
  have htest (y : Rd d) : testAffinePull 1 y (bumpTest n 0) = bumpTest n y := by
    ext x
    rw [testAffinePull_one_apply]
    exact (bumpTest_apply_sub n y x).symm
  calc
    (∫ y : Rd d, φ y * T (bumpTest n y)) =
        ∫ y : Rd d, φ y * T (testAffinePull 1 y (bumpTest n 0)) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [htest y]
    _ = T (ofSuppRd K' I₁) := (hT₁ T).symm
    _ = T (ofSuppRd K' I₂) := by rw [hIeq]
    _ = ∫ t : Rd d, bumpTest n 0 t * T (testAffinePull 1 t φ) := hT₂ T
    _ = ofCont c (bumpTest n 0) := by
          rw [ofCont_apply]
          apply integral_congr_ae
          filter_upwards [] with t
          by_cases ht : ‖t‖ ≤ 1
          · rw [show c t = T (testAffinePull 1 t φ) from by
              change T (testAffinePull 1 (l2b_unitProj t) φ) = _
              rw [l2b_unitProj_eq_self ht]]
          · have hzero := bumpTest_zero_eq_zero n (le_of_lt (not_le.1 ht))
            rw [hzero, zero_mul, zero_mul]

end HigherDimLQGMetric
