import HigherDimLQGMetric.Shell.Defs
import HigherDimLFPP.Field.OscBlock

/-!
# Finite boxes for shell grids

The centred lattice in a bounded ball is covered by an explicit finite integer box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The finite grid box with integer coordinates between `-N` and `N`. -/
def shellGridBox (d N : ℕ) (s : ℝ) : Finset (Rd d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(N : ℤ)) N).image
    (fun m => WithLp.toLp 2 (fun i => s * (m i : ℝ)))

theorem card_shellGridBox_le (d N : ℕ) (s : ℝ) :
    (shellGridBox d N s).card ≤ (2 * N + 1) ^ d := by
  classical
  unfold shellGridBox
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Fintype.card_piFinset_const, Int.card_Icc]
  have h : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [h]

theorem grid_ball_subset_shellGridBox {s B : ℝ} (hs : 0 < s) (_hB : 0 ≤ B) :
    gridPts s ∩ Metric.ball (0 : Rd d) B ⊆
      (shellGridBox d (⌈B / s⌉₊ + 1) s : Set (Rd d)) := by
  classical
  intro w hw
  obtain ⟨m, rfl⟩ := hw.1
  let N : ℕ := ⌈B / s⌉₊ + 1
  have hBN : B < (N : ℝ) * s := by
    have hceil : B / s ≤ (⌈B / s⌉₊ : ℝ) := Nat.le_ceil (B / s)
    have hdiv : B / s < (N : ℝ) := by
      dsimp [N]
      push_cast
      linarith
    exact (div_lt_iff₀ hs).mp hdiv
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨m, ?_, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  have hcoord : ‖(WithLp.toLp 2 (fun j : Fin d => s * (m j : ℝ)) : Rd d) i‖ ≤
      ‖(WithLp.toLp 2 (fun j : Fin d => s * (m j : ℝ)) : Rd d)‖ :=
    PiLp.norm_apply_le _ i
  have hnorm : ‖(WithLp.toLp 2 (fun j : Fin d => s * (m j : ℝ)) : Rd d)‖ < B := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw.2
  have hm : |s * (m i : ℝ)| < (N : ℝ) * s := by
    simpa only [Real.norm_eq_abs] using lt_of_le_of_lt hcoord (hnorm.trans hBN)
  have hm' : |(m i : ℝ)| < N := by
    rw [abs_mul, abs_of_pos hs, mul_comm] at hm
    exact lt_of_mul_lt_mul_right hm hs.le
  rw [Finset.mem_Icc]
  have hleft : -(N : ℤ) < m i := by exact_mod_cast (abs_lt.mp hm').1
  have hright : m i < (N : ℤ) := by exact_mod_cast (abs_lt.mp hm').2
  exact ⟨hleft.le, hright.le⟩

/-- A coarse count sufficient for every polynomial good-scale union bound. -/
theorem card_shellGridBox_scaled (hd : 3 ≤ d) {𝕣 ε : ℝ} (h𝕣 : 0 < 𝕣)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((shellGridBox d (⌈(𝕣 / ε) / (ε ^ 2 * 𝕣 / (10 * d))⌉₊ + 1)
      (ε ^ 2 * 𝕣 / (10 * d))).card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d := by
  let s : ℝ := ε ^ 2 * 𝕣 / (10 * d)
  let B : ℝ := 𝕣 / ε
  let N : ℕ := ⌈B / s⌉₊ + 1
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < s := by dsimp [s]; positivity
  have hε3 : 0 < ε ^ 3 := pow_pos hε0 _
  have hε3le : ε ^ 3 ≤ 1 := pow_le_one₀ hε0.le hε1.le
  have hquot : B / s = 10 * (d : ℝ) / ε ^ 3 := by
    dsimp [B, s]
    field_simp
  have hN : (N : ℝ) < B / s + 2 := by
    dsimp [N]
    push_cast
    linarith [Nat.ceil_lt_add_one (le_of_lt (div_pos (div_pos h𝕣 hε0) hs))]
  have hNε : (N : ℝ) * ε ^ 3 < 10 * d + 2 := by
    rw [hquot] at hN
    have hm := mul_lt_mul_of_pos_right hN hε3
    have hcancel : (10 * (d : ℝ) / ε ^ 3 + 2) * ε ^ 3 = 10 * d + 2 * ε ^ 3 := by
      field_simp
    rw [hcancel] at hm
    linarith
  have hN₁ : (2 * (N : ℝ) + 1) * ε ^ 3 ≤ 25 * d := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith
  have hcard := card_shellGridBox_le d N s
  have hcardR : ((shellGridBox d N s).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ d := by
    exact_mod_cast hcard
  have hpow : ((2 * (N : ℝ) + 1) * ε ^ 3) ^ d ≤ (25 * d : ℝ) ^ d :=
    pow_le_pow_left₀ (by positivity) hN₁ d
  have heq : (2 * (N : ℝ) + 1) ^ d * ε ^ (3 * d) =
      ((2 * (N : ℝ) + 1) * ε ^ 3) ^ d := by rw [pow_mul, mul_pow]
  change ((shellGridBox d N s).card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d
  calc
    ((shellGridBox d N s).card : ℝ) * ε ^ (3 * d) ≤
        (2 * (N : ℝ) + 1) ^ d * ε ^ (3 * d) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = ((2 * (N : ℝ) + 1) * ε ^ 3) ^ d := heq
    _ ≤ (25 * d : ℝ) ^ d := hpow

end HigherDimLQGMetric
