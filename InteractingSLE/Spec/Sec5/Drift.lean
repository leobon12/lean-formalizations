/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Heights
import Mathlib.Algebra.Order.Chebyshev

/-!
# The additional force drift in the alternating construction (proof of Proposition 5.9)

Packet PROVE-SEC5-A (specification §5.2, proof of Proposition 5.9, `source/spec/p145-192.md` L37–L50, pp. 146–147).

At the start of an even stage `j ≥ 4` the driver is in `I₋`; all left force points are `≤ −7/4` and, except for the
new first right force point, all right force points are `≥ 7/4`. While `W ∈ [−1, 1]` every other force point is at
distance at least `3/4` from the driver. The weights produced by the angle changes satisfy
`ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`, `ρ^{i,L} = −ρ^{i,R}` (`Sec5.angleChangeWeight`), and their partial sums are
bounded by `M = πχ/λ` (`Sec5.abs_sum_angleChangeWeight_le`). Abel's inequality
(`Finset.abs_sum_mul_le_mul_of_abs_sum_range_le`, Mathlib), "with the decreasing reciprocal force-point gaps", gives:

* `abs_sum_div_le_of_gap_mono`: if the gaps `g_i ≥ δ > 0` are nondecreasing in the index and every partial sum of
  the weights is at most `M` in absolute value, then `|∑ ρ_i / g_i| ≤ M/δ`;
* `abs_angleChangeDrift_le`: "the total drift from all the angle-change marks other than the first right mark is
  bounded in absolute value by `8M/3`";
* `abs_sum_div_le_of_gap`: the finitely many inherited marks add at most `(4/3) ∑ |ρ_i^{initial}|`
  (`δ = 3/4`).

Together these are the drift bound `C` of Lemma 5.10, independent of the stage.
-/

set_option autoImplicit false

noncomputable section

open Real Finset

namespace InteractingSLE

namespace Sec5

variable {κ : ℝ}

/-- **Abel summation with gaps.** If `δ ≤ g_0 ≤ g_1 ≤ ⋯ ≤ g_{n−1}` with `δ > 0` and every partial sum of `ρ` up to
`n` has absolute value at most `M`, then `|∑_{i<n} ρ_i / g_i| ≤ M / δ`. -/
theorem abs_sum_div_le_of_gap_mono {n : ℕ} {ρ g : ℕ → ℝ} {M δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ i < n, δ ≤ g i) (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j)
    (hρ : ∀ k ≤ n, |∑ i ∈ range k, ρ i| ≤ M) :
    |∑ i ∈ range n, ρ i / g i| ≤ M / δ := by
  have hM : 0 ≤ M := by simpa using hρ 0 n.zero_le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [range_zero, sum_empty, abs_zero]; exact div_nonneg hM hδ.le
  set a : ℕ → ℝ := fun i => if i < n then (g i)⁻¹ else 0 with ha
  have ha0 : 0 ≤ a := fun i => by
    simp only [ha]; split_ifs with h
    · exact inv_nonneg.2 (hδ.le.trans (hg i h))
    · exact le_rfl
  have hanti : AntitoneOn a (Set.Iio n) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [ha, hi, hj, ↓reduceIte]
    exact inv_anti₀ (hδ.trans_le (hg i hi)) (hmono i j hij hj)
  have hsum : ∑ i ∈ range n, ρ i / g i = ∑ i ∈ range n, ρ i * a i :=
    sum_congr rfl fun i hi => by simp [ha, mem_range.1 hi, div_eq_mul_inv]
  rw [hsum]
  refine (abs_sum_mul_le_mul_of_abs_sum_range_le hρ ha0 hanti).trans ?_
  have : a 0 ≤ δ⁻¹ := by
    simp only [ha, hn, ↓reduceIte]; exact inv_anti₀ hδ (hg 0 hn)
  calc M * a 0 ≤ M * δ⁻¹ := mul_le_mul_of_nonneg_left this hM
    _ = M / δ := (div_eq_mul_inv M δ).symm

/-- The crude bound for marks at distance at least `δ`: `|∑ ρ_i / (W − V_i)| ≤ (∑ |ρ_i|) / δ`. -/
theorem abs_sum_div_le_of_gap {ι : Type*} (s : Finset ι) {ρ V : ι → ℝ} {W δ : ℝ} (hδ : 0 < δ)
    (hV : ∀ i ∈ s, δ ≤ |W - V i|) :
    |∑ i ∈ s, ρ i / (W - V i)| ≤ (∑ i ∈ s, |ρ i|) / δ := by
  rw [sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ (hV i hi)

/-- **The angle-change drift bound** (proof of Proposition 5.9): let the angles `φ i = θ_{j−i}` lie in
`[−π/2, π/2]`, the driver `W ∈ [−1, 1]`, the left angle-change marks `VL 0 ≥ VL 1 ≥ ⋯` be `≤ −7/4`, and the right
angle-change marks other than the first, `VR 0 ≤ VR 1 ≤ ⋯`, be `≥ 7/4`. With the weights `ρ^{i+1,L} = −ρ^{i+1,R}` on
the left and `ρ^{i+2,R}` on the right, the total drift is at most `8M/3` in absolute value. -/
theorem abs_angleChangeDrift_le (hκ : 0 < κ) (hκ4 : κ < 4) {φ : ℕ → ℝ}
    (hφ : ∀ i, φ i ∈ Set.Icc (-(π / 2)) (π / 2)) {W : ℝ} (hW : W ∈ Set.Icc (-1 : ℝ) 1) {nL nR : ℕ}
    {VL VR : ℕ → ℝ} (hVL : ∀ i < nL, VL i ≤ -7 / 4) (hVLm : ∀ i j, i ≤ j → j < nL → VL j ≤ VL i)
    (hVR : ∀ i < nR, 7 / 4 ≤ VR i) (hVRm : ∀ i j, i ≤ j → j < nR → VR i ≤ VR j) :
    |∑ i ∈ range nL, -angleChangeWeight κ φ i / (W - VL i) +
        ∑ i ∈ range nR, angleChangeWeight κ φ (i + 1) / (W - VR i)| ≤
      8 * angleWeightBound κ / 3 := by
  obtain ⟨hW1, hW2⟩ := hW
  have hδ : (0 : ℝ) < 3 / 4 := by norm_num
  have hL : |∑ i ∈ range nL, -angleChangeWeight κ φ i / (W - VL i)| ≤ angleWeightBound κ / (3 / 4) := by
    refine abs_sum_div_le_of_gap_mono (g := fun i => W - VL i) hδ (fun i hi => ?_)
      (fun i j hij hj => ?_) (fun k _ => ?_)
    · have := hVL i hi; linarith
    · have := hVLm i j hij hj; linarith
    · rw [sum_neg_distrib, abs_neg]
      simpa using abs_sum_angleChangeWeight_le hκ hκ4 hφ 0 k
  have hR : |∑ i ∈ range nR, angleChangeWeight κ φ (i + 1) / (W - VR i)| ≤
      angleWeightBound κ / (3 / 4) := by
    have : ∑ i ∈ range nR, angleChangeWeight κ φ (i + 1) / (W - VR i) =
        -∑ i ∈ range nR, angleChangeWeight κ φ (i + 1) / (VR i - W) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun i _ => by rw [← div_neg, neg_sub]
    rw [this, abs_neg]
    refine abs_sum_div_le_of_gap_mono (g := fun i => VR i - W) hδ (fun i hi => ?_)
      (fun i j hij hj => ?_) (fun k _ => ?_)
    · have := hVR i hi; linarith
    · have := hVRm i j hij hj; linarith
    · have h := abs_sum_angleChangeWeight_le hκ hκ4 hφ 1 k
      have e : ∀ i, angleChangeWeight κ (fun i => φ (1 + i)) i = angleChangeWeight κ φ (i + 1) := by
        intro i; simp only [angleChangeWeight]; ring_nf
      simpa only [e] using h
  calc _ ≤ |∑ i ∈ range nL, -angleChangeWeight κ φ i / (W - VL i)| +
        |∑ i ∈ range nR, angleChangeWeight κ φ (i + 1) / (W - VR i)| := abs_add_le _ _
    _ ≤ angleWeightBound κ / (3 / 4) + angleWeightBound κ / (3 / 4) := add_le_add hL hR
    _ = 8 * angleWeightBound κ / 3 := by ring

end Sec5

end InteractingSLE
