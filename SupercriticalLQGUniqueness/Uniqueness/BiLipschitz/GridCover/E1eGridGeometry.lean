import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover.E1eIteration
import LQGMetric.Papers.GM.S3.GoodAnnulus




 




set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover

def meshPower (n : ℕ) : ℕ := 10 ^ (2 * n)
def meshStep (n : ℕ) : ℝ := 1 / (4 * (meshPower n : ℝ))
def meshBound (m n : ℕ) : ℕ := 4 * (m + 1) * meshPower n + 2
def meshBox (m n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(meshBound m n : ℤ)) (meshBound m n : ℤ) ×ˢ
  Finset.Icc (-(meshBound m n : ℤ)) (meshBound m n : ℤ)

private theorem meshPower_pos (n : ℕ) : 0 < meshPower n := by
  unfold meshPower
  positivity

private theorem meshStep_pos (n : ℕ) : 0 < meshStep n := by
  unfold meshStep
  have hL : 0 < (meshPower n : ℝ) := by exact_mod_cast meshPower_pos n
  positivity

 
theorem e1e_mesh_cover (m n : ℕ) (y : ℂ) (hy : y ∈ closedBall (0 : ℂ) m) :
    ∃ q ∈ meshBox m n,
      dist y (LQGMetric.GM.gridPt (meshStep n) q) ≤ meshStep n := by
  have hL : 0 < (meshPower n : ℝ) := by exact_mod_cast meshPower_pos n
  have hδ := meshStep_pos n
  have hy_norm : ‖y‖ ≤ (m : ℝ) := by simpa using hy
  have hcoord : ∀ t : ℝ, |t| ≤ ‖y‖ →
      |t| / meshStep n + 1 ≤ (meshBound m n : ℝ) := by
    intro t ht
    have ht' : |t| ≤ (m : ℝ) := ht.trans hy_norm
    have heq : |t| / meshStep n = 4 * (meshPower n : ℝ) * |t| := by
      unfold meshStep
      field_simp
    rw [heq]
    have hm : (meshBound m n : ℝ) =
        4 * ((m : ℝ) + 1) * (meshPower n : ℝ) + 2 := by
      simp only [meshBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hm]
    nlinarith [mul_nonneg (show 0 ≤ 4 * (meshPower n : ℝ) by positivity)
      (sub_nonneg.mpr ht')]
  obtain ⟨hre, hrem⟩ := LQGMetric.GM.round_grid hδ
    (hcoord y.re (Complex.abs_re_le_norm y))
  obtain ⟨him, himm⟩ := LQGMetric.GM.round_grid hδ
    (hcoord y.im (Complex.abs_im_le_norm y))
  let q : ℤ × ℤ := (round (y.re / meshStep n), round (y.im / meshStep n))
  have hq : q ∈ meshBox m n := by
    exact Finset.mem_product.mpr ⟨hrem, himm⟩
  refine ⟨q, hq, ?_⟩
  rw [dist_eq_norm]
  calc
    ‖y - LQGMetric.GM.gridPt (meshStep n) q‖
        ≤ |(y - LQGMetric.GM.gridPt (meshStep n) q).re| +
          |(y - LQGMetric.GM.gridPt (meshStep n) q).im| :=
          Complex.norm_le_abs_re_add_abs_im _
    _ = |y.re - meshStep n * (q.1 : ℝ)| +
        |y.im - meshStep n * (q.2 : ℝ)| := by
          rw [Complex.sub_re, Complex.sub_im,
            LQGMetric.GM.gridPt_re, LQGMetric.GM.gridPt_im]
    _ ≤ meshStep n := by dsimp [q] at *; linarith

 
theorem e1e_mesh_card_le (m n : ℕ) :
    ((meshBox m n).card : ℝ) ≤
      (8 * ((m : ℝ) + 1) + 5) ^ 2 * (10 : ℝ) ^ (4 * n) := by
  have hL : (1 : ℝ) ≤ meshPower n := by
    exact_mod_cast Nat.succ_le_iff.mpr (meshPower_pos n)
  have hcard : ((meshBox m n).card : ℝ) = (2 * meshBound m n + 1 : ℝ) ^ 2 := by
    unfold meshBox
    rw [Finset.card_product, Int.card_Icc]
    have h : ((meshBound m n : ℤ) + 1 - -(meshBound m n : ℤ)).toNat =
        2 * meshBound m n + 1 := by omega
    rw [h]
    push_cast
    ring
  rw [hcard]
  have hM : (2 * meshBound m n + 1 : ℝ) ≤
      (8 * ((m : ℝ) + 1) + 5) * meshPower n := by
    have hM_eq : (2 * meshBound m n + 1 : ℝ) =
        8 * ((m : ℝ) + 1) * meshPower n + 5 := by
      simp only [meshBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hM_eq]
    have h5 : (5 : ℝ) ≤ 5 * meshPower n := by nlinarith
    calc
      8 * ((m : ℝ) + 1) * meshPower n + 5
          ≤ 8 * ((m : ℝ) + 1) * meshPower n + 5 * meshPower n :=
            add_le_add_right h5 _
      _ = (8 * ((m : ℝ) + 1) + 5) * meshPower n := by ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 * meshBound m n + 1 : ℝ)) hM 2
  have heq : ((8 * ((m : ℝ) + 1) + 5) * meshPower n) ^ 2 =
      (8 * ((m : ℝ) + 1) + 5) ^ 2 * (10 : ℝ) ^ (4 * n) := by
    unfold meshPower
    norm_cast
    rw [mul_pow, ← pow_mul]
    ring
  exact hsq.trans_eq heq

 
theorem e1e_mesh_inside {n : ℕ} {r : ℝ}
    (hr : (10 : ℝ) ^ (-(2 * (n : ℤ))) ≤ r) :
    meshStep n < r / 2 := by
  have hL : 0 < (meshPower n : ℝ) := by exact_mod_cast meshPower_pos n
  have heq : (10 : ℝ) ^ (-(2 * (n : ℤ))) = 1 / (meshPower n : ℝ) := by
    unfold meshPower
    rw [zpow_neg]
    simp only [one_div]
    congr 1
    norm_cast
  rw [heq] at hr
  have hinv : 0 < 1 / (meshPower n : ℝ) := by positivity
  have hstep : meshStep n = (1 / (meshPower n : ℝ)) / 4 := by
    unfold meshStep
    field_simp
  rw [hstep]
  linarith

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
