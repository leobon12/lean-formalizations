import HigherDimLQGMetric.Sec8b.Prop86Union
import HigherDimLQGMetric.Sec8b.Lemma85GridBound

/-! A uniform polynomial bound on the candidates in one scale/color/bin class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical
open HigherDimLFPP (Rd)

def s7b_candidateConst (d J k : ℕ) : ℝ :=
  (k + 1) * (J * (1000 * d + 5 : ℝ) ^ d + 1) ^ k

theorem s7b_candidateConst_pos (d J k : ℕ) :
    0 < s7b_candidateConst d J k := by
  unfold s7b_candidateConst
  positivity

theorem s7b_candidate_power_bound (d J k : ℕ) (hd : 1 ≤ d)
    {ε R r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (hrlo : ε ^ 2 * R ≤ r)
    (x y : Rd d) (colour : Fin d → ℤ) :
    ((s7b_candidateFamily d J r R x y colour k).card : ℝ) ≤
      s7b_candidateConst d J k * (ε⁻¹) ^ (2 * d * k) := by
  let s : ℝ := ε⁻¹
  let A : ℝ := (1000 * d + 5 : ℝ)
  have hs : 1 ≤ s := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
  have hs0 : 0 ≤ s := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (pow_pos hε _) hR) hrlo
  have hgrid := s7b_scale_grid_bound d hd hε hε1 hR hrlo
  have hu : ((s7b_siteUniverse d J r R).card : ℝ) ≤
      J * (A * s ^ 2) ^ d := by
    have hc' : ((s7b_siteUniverse d J r R).card : ℝ) ≤
        ((shellGridBox d (⌈5 * R / (r / (100 * d))⌉₊ + 1)
          (r / (100 * d))).card : ℝ) * J := by
      unfold s7b_siteUniverse
      change (((shellGridBox d (⌈5 * R / (r / (100 * d))⌉₊ + 1)
        (r / (100 * d))) ×ˢ Finset.range J).card : ℝ) ≤ _
      rw [Finset.card_product, Finset.card_range]
      norm_cast
    exact hc'.trans (by simpa only [A, s, mul_comm] using
      mul_le_mul_of_nonneg_right hgrid (by positivity : (0 : ℝ) ≤ J))
  have hspow : 1 ≤ s ^ (2 * d) := one_le_pow₀ hs
  have hbase : ((s7b_siteUniverse d J r R).card : ℝ) + 1 ≤
      (J * A ^ d + 1) * s ^ (2 * d) := by
    calc
      ((s7b_siteUniverse d J r R).card : ℝ) + 1 ≤
          J * (A * s ^ 2) ^ d + 1 := by linarith only [hu]
      _ = J * A ^ d * s ^ (2 * d) + 1 := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ (J * A ^ d + 1) * s ^ (2 * d) := by
        nlinarith only [hspow]
  have hfamily := s7b_candidate_card_le d J hd hr hR x y colour k
  have hfamily' : ((s7b_candidateFamily d J r R x y colour k).card : ℝ) ≤
      (k + 1) * (((s7b_siteUniverse d J r R).card : ℝ) + 1) ^ k := by
    exact_mod_cast hfamily
  calc
    ((s7b_candidateFamily d J r R x y colour k).card : ℝ) ≤
      (k + 1) * (((s7b_siteUniverse d J r R).card : ℝ) + 1) ^ k := hfamily'
    _ ≤ (k + 1) * ((J * A ^ d + 1) * s ^ (2 * d)) ^ k := by
      gcongr
    _ = s7b_candidateConst d J k * (ε⁻¹) ^ (2 * d * k) := by
      simp only [s7b_candidateConst, A, s, mul_pow, ← pow_mul]
      ring

end HigherDimLQGMetric
