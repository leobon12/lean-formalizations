import HigherDimLQGContinuity.Continuum.Escape
import HigherDimLQGMetric.Modulus.Grid
import HigherDimLQGMetric.Sec4.Lemma45Geom

/-! Deterministic dyadic-grid lower bound from annular crossings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

def l2_lowerRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 3)

theorem l2_lowerRadius_pos (k : ℕ) : 0 < l2_lowerRadius k := by
  dsimp [l2_lowerRadius]
  positivity

theorem l2_lowerRadius_le_one (k : ℕ) : l2_lowerRadius k ≤ 1 := by
  dsimp [l2_lowerRadius]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem l2_lowerRadius_zero : l2_lowerRadius 0 = 1 / 8 := by
  norm_num [l2_lowerRadius]

/-- For each pair in the radius-`R` ball, a dyadic shell has radius between
`t/(16R)` and `t/8`, where `t` is the Euclidean separation. -/
theorem l2_choose_lowerRadius {R t : ℝ} (hR : 1 ≤ R) (ht : 0 < t)
    (htR : t ≤ 2 * R) :
    ∃ k : ℕ, l2_lowerRadius k ≤ t / 8 ∧ t ≤ 16 * R * l2_lowerRadius k := by
  by_cases ht1 : t ≤ 1
  · obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
      (show 0 < t / 8 by positivity) (by linarith : t / 8 ≤ 1)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have hn3 : 3 ≤ n := by
      by_contra hbad
      have hn2 : n ≤ 2 := by omega
      interval_cases n <;> norm_num at hnlo <;> linarith
    let k : ℕ := n - 2
    have hnk : k + 3 = n + 1 := by dsimp [k]; omega
    refine ⟨k, ?_, ?_⟩
    · dsimp [l2_lowerRadius]
      rw [hnk]
      exact hnlo.le
    · have hpow : (1 / 2 : ℝ) ^ n = 2 * l2_lowerRadius k := by
        dsimp [l2_lowerRadius]
        rw [hnk, pow_succ]
        ring
      have ht16 : t ≤ 16 * l2_lowerRadius k := by
        rw [hpow] at hnhi
        linarith
      have hrpos := l2_lowerRadius_pos k
      nlinarith
  · have ht1' : 1 < t := lt_of_not_ge ht1
    refine ⟨0, ?_, ?_⟩
    · rw [l2_lowerRadius_zero]
      linarith
    · rw [l2_lowerRadius_zero]
      nlinarith

/-- A uniform dyadic shell barrier implies the lower Hölder bound on a closed ball. -/
theorem l2_lower_of_grid {d : ℕ} (hd : 1 ≤ d) (D : ContMetric d)
    (hD : D.IsLength) {R β H : ℝ} (hR : 1 ≤ R) (hβ : 0 < β) (hH : 0 < H)
    (hgrid : ∀ k : ℕ, ∀ z ∈ w3bGrid d (R + 1) 1 (l2_lowerRadius k),
      ENNReal.ofReal ((l2_lowerRadius k) ^ β / H) ≤
        acrossDist D z (l2_lowerRadius k) (2 * l2_lowerRadius k))
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) R)
    (hy : y ∈ closedBall (0 : Rd d) R) :
    ENNReal.ofReal (‖x - y‖ ^ β / ((16 * R) ^ β * H)) ≤
      ENNReal.ofReal (D.1 (x, y)) := by
  by_cases hxy : x = y
  · subst y
    have hz : (0 : ℝ) ^ β = 0 := Real.zero_rpow hβ.ne'
    simp [hz, D.apply_self]
  let t : ℝ := ‖x - y‖
  have ht : 0 < t := by dsimp [t]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have htR : t ≤ 2 * R := by
    have htri := norm_sub_le x y
    dsimp [t]
    linarith
  obtain ⟨k, hklo, hkhi⟩ := l2_choose_lowerRadius hR ht htR
  let r : ℝ := l2_lowerRadius k
  have hr : 0 < r := l2_lowerRadius_pos k
  have hr1 : r ≤ 1 := l2_lowerRadius_le_one k
  have hxL : ‖x‖ < (R + 1) * 1 := by nlinarith
  obtain ⟨z, hz, hxz⟩ := w3b_exists_grid_near hd
    (show 0 < R + 1 by linarith) one_pos hr hr1 hxL
  have hxz' : ‖x - z‖ < r := by
    have hh : ‖x - z‖ ≤ r / 8 := by simpa only [mul_one] using hxz
    linarith
  have hyz : 2 * r ≤ ‖y - z‖ := by
    have htri : ‖x - y‖ ≤ ‖x - z‖ + ‖y - z‖ := by
      calc
        ‖x - y‖ = ‖(x - z) - (y - z)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have hnear : ‖x - z‖ ≤ r / 8 := by simpa only [mul_one] using hxz
    linarith
  have hcross : acrossDist D z r (2 * r) ≤ ENNReal.ofReal (D.1 (x, y)) := by
    have hh := l9b_acrossDist_le_internal D univ
      (u := z) (x := x) (y := y) (r := 2 * r)
      (by simpa only [show (2 * r) / 2 = r by ring] using hxz') hyz
    rw [D.internal_univ_of_isLength hD] at hh
    simpa only [show (2 * r) / 2 = r by ring] using hh
  have hscale : t / (16 * R) ≤ r := by
    have hR0 : 0 < 16 * R := by positivity
    exact (div_le_iff₀ hR0).2 (by nlinarith [hkhi])
  have hpow : t ^ β / ((16 * R) ^ β * H) ≤ r ^ β / H := by
    have hR16 : 0 < 16 * R := by positivity
    have hrpow : (t / (16 * R)) ^ β ≤ r ^ β :=
      Real.rpow_le_rpow (div_nonneg ht.le hR16.le) hscale hβ.le
    rw [Real.div_rpow ht.le hR16.le] at hrpow
    have hden : 0 < (16 * R) ^ β * H := mul_pos (Real.rpow_pos_of_pos hR16 β) hH
    have hden' : 0 < H := hH
    have hbase : t ^ β ≤ r ^ β * (16 * R) ^ β :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hR16 β)).1 hrpow
    have hbaseH := mul_le_mul_of_nonneg_right hbase hH.le
    rw [div_le_div_iff₀ hden hden']
    nlinarith
  calc
    ENNReal.ofReal (t ^ β / ((16 * R) ^ β * H)) ≤
        ENNReal.ofReal (r ^ β / H) := ENNReal.ofReal_le_ofReal hpow
    _ ≤ acrossDist D z r (2 * r) := hgrid k z hz
    _ ≤ ENNReal.ofReal (D.1 (x, y)) := hcross

end HigherDimLQGContinuity
