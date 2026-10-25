import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.PlanarTransfer
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapSequences.Gapc1Sequence




 






set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 
def annulusAt (x : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    EuclideanAnnulus := ⟨(x, r, R), hr, hrR⟩

 

theorem ratio_of_nearby_scale
    (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {δ l R β : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hl1 : δ ≤ l) (hl2 : l < 2 * δ) (hR : 0 < R) (hβ : 0 < β)
    (x : ℂ) :
    let big := annulusAt x (δ * R) (δ ^ ((1 : ℝ) / 2) * R)
      (mul_pos hδ hR)
      (mul_lt_mul_of_pos_right
        (Real.self_lt_rpow_of_lt_one hδ (by linarith : δ < 1) (by norm_num)) hR)
    let small := annulusAt x (l * R) (l ^ ((3 : ℝ) / 4) * R)
      (mul_pos (lt_of_lt_of_le hδ hl1) hR)
      (mul_lt_mul_of_pos_right
        (Real.self_lt_rpow_of_lt_one (lt_of_lt_of_le hδ hl1)
          (by linarith : l < 1) (by norm_num)) hR)
    aroundDist D small ≤ ENNReal.ofReal (l ^ β) * acrossDist D small →
      aroundDist D big ≤ ENNReal.ofReal (δ ^ (β / 2)) * acrossDist D big := by
  dsimp only
  let big := annulusAt x (δ * R) (δ ^ ((1 : ℝ) / 2) * R)
    (mul_pos hδ hR)
    (mul_lt_mul_of_pos_right
      (Real.self_lt_rpow_of_lt_one hδ (by linarith : δ < 1) (by norm_num)) hR)
  let small := annulusAt x (l * R) (l ^ ((3 : ℝ) / 4) * R)
    (mul_pos (lt_of_lt_of_le hδ hl1) hR)
    (mul_lt_mul_of_pos_right
      (Real.self_lt_rpow_of_lt_one (lt_of_lt_of_le hδ hl1)
        (by linarith : l < 1) (by norm_num)) hR)
  have hscale := TwoScale.GapSequences.scale_fact_one δ l hδ hδ8 hl1 hl2
  have hfactor := TwoScale.GapSequences.scale_fact_two δ l β hδ (by linarith) hl1 hl2 hβ
  have hinner : big.innerRadius + dist big.center small.center ≤ small.innerRadius := by
    change δ * R + dist x x ≤ l * R
    simpa only [dist_self, add_zero] using mul_le_mul_of_nonneg_right hl1 hR.le
  have houter : small.outerRadius + dist big.center small.center ≤ big.outerRadius := by
    change l ^ ((3 : ℝ) / 4) * R + dist x x ≤ δ ^ ((1 : ℝ) / 2) * R
    simpa only [dist_self, add_zero] using mul_le_mul_of_nonneg_right hscale hR.le
  obtain ⟨haround, hacross⟩ := shifted_annulus_comparisons D hB hL big small hinner houter
  intro hratio
  calc
    aroundDist D big ≤ aroundDist D small := haround
    _ ≤ ENNReal.ofReal (l ^ β) * acrossDist D small := hratio
    _ ≤ ENNReal.ofReal (δ ^ (β / 2)) * acrossDist D big := by
      gcongr

 

theorem exists_dyadic_near {q δ : ℝ} (hq : 0 < q)
    (hδ : 0 < δ) (hδq : δ ≤ q) :
    ∃ n : ℕ, δ ≤ q * (1 / 2 : ℝ) ^ n ∧
      q * (1 / 2 : ℝ) ^ n < 2 * δ ∧
      0 < q * (1 / 2 : ℝ) ^ n ∧
      q * (1 / 2 : ℝ) ^ n ≤ q := by
  have hdiv0 : 0 < δ / q := div_pos hδ hq
  have hdiv1 : δ / q ≤ 1 := (div_le_iff₀ hq).2 (by simpa using hδq)
  obtain ⟨n, hlo, hhi⟩ :=
    exists_nat_pow_near_of_lt_one hdiv0 hdiv1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hlow : δ ≤ q * (1 / 2 : ℝ) ^ n := by
    simpa only [mul_comm] using (div_le_iff₀ hq).mp hhi
  have hhigh : q * (1 / 2 : ℝ) ^ (n + 1) < δ := by
    apply (lt_div_iff₀ hq).mp at hlo
    nlinarith [hlo]
  have hstep : q * (1 / 2 : ℝ) ^ n =
      2 * (q * (1 / 2 : ℝ) ^ (n + 1)) := by
    rw [pow_succ]
    ring
  refine ⟨n, hlow, ?_, mul_pos hq (pow_pos (by norm_num) n), ?_⟩
  · rw [hstep]
    linarith
  · have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hp hq.le]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
