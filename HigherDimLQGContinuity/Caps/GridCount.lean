import HigherDimLQGContinuity.Caps.Grid
import HigherDimLQGMetric.Sharp.GridCount

/-!
# Finite enumeration of inspected grid pairs (packet P4)

The Gaussian union bound uses a finite superset of `gridPairs`, indexed by
radius exponents and by one integer box containing every inspected centre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem p4_radius_index_lt {lam : ℝ} (hlam : 1 < lam) {n k : ℕ}
    (hr : Real.exp (-(n : ℝ)) ≤ lam ^ (-(k : ℝ))) :
    k < ⌈(n : ℝ) / Real.log lam⌉₊ + 1 := by
  have hlog : 0 < Real.log lam := Real.log_pos hlam
  have hpow : lam ^ (-(k : ℝ)) = Real.exp (-(k : ℝ) * Real.log lam) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < lam)]
    ring_nf
  rw [hpow] at hr
  have hkn : (k : ℝ) ≤ (n : ℝ) / Real.log lam := by
    have hneg := (Real.exp_le_exp).mp hr
    apply (le_div_iff₀ hlog).2
    nlinarith
  have hceil : (k : ℝ) < (⌈(n : ℝ) / Real.log lam⌉₊ : ℝ) + 1 :=
    lt_of_le_of_lt (hkn.trans (Nat.le_ceil _)) (by linarith)
  exact_mod_cast hceil

/-- The radius-index bound used to turn the inspected set into a finite union. -/
theorem gridPairs_radius_index_lt {d : ℕ} {lam κ W : ℝ} {n : ℕ}
    (hlam : 1 < lam) {p : ℝ × Rd d} (hp : p ∈ gridPairs d lam κ n W) :
    ∃ k < ⌈(n : ℝ) / Real.log lam⌉₊ + 1, p.1 = lam ^ (-(k : ℝ)) := by
  obtain ⟨k, hk, hr, -⟩ := hp
  exact ⟨k, p4_radius_index_lt hlam (hk ▸ hr), hk⟩

private theorem p4_shellGridBox_mono {d N₁ N₂ : ℕ} {s : ℝ} (hN : N₁ ≤ N₂) :
    shellGridBox d N₁ s ⊆ shellGridBox d N₂ s := by
  classical
  intro z hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  apply Finset.mem_image.mpr
  refine ⟨j, ?_, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := (Fintype.mem_piFinset.mp hj) i
  simp only [Finset.mem_Icc] at hi ⊢
  constructor <;> omega

/-- A finite superset of the inspected pairs. -/
def p4_gridPairsFinset (d : ℕ) (lam κ : ℝ) (n : ℕ) (W : ℝ) : Finset (ℝ × Rd d) :=
  let M := ⌈(n : ℝ) / Real.log lam⌉₊ + 1
  let N := ⌈(W + 1) / (κ * Real.exp (-(n : ℝ)))⌉₊ + 1
  (Finset.range M).biUnion fun k =>
    (shellGridBox d N (κ * lam ^ (-(k : ℝ)))).image
      (fun z => (lam ^ (-(k : ℝ)), z))

/-- Every inspected pair belongs to the finite enumeration. -/
theorem gridPairs_subset_finset {d : ℕ} {lam κ W : ℝ} {n : ℕ}
    (hlam : 1 < lam) (hκ : 0 < κ) (hW : 0 ≤ W) :
    gridPairs d lam κ n W ⊆ (p4_gridPairsFinset d lam κ n W : Set (ℝ × Rd d)) := by
  classical
  intro p hp
  obtain ⟨k, hk, hr, j, hz, hWz⟩ := hp
  let r : ℝ := lam ^ (-(k : ℝ))
  let B : ℝ := W + 1
  let s : ℝ := κ * r
  let smin : ℝ := κ * Real.exp (-(n : ℝ))
  let N : ℕ := ⌈B / smin⌉₊ + 1
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hs : 0 < s := mul_pos hκ hrpos
  have hsmin : 0 < smin := mul_pos hκ (Real.exp_pos _)
  have hrr : Real.exp (-(n : ℝ)) ≤ r := by simpa only [r, hk] using hr
  have hsminle : smin ≤ s := mul_le_mul_of_nonneg_left hrr hκ.le
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hdiv : B / s ≤ B / smin := div_le_div_of_nonneg_left hB hsmin hsminle
  have hN : ⌈B / s⌉₊ + 1 ≤ N := Nat.add_le_add_right (Nat.ceil_mono hdiv) 1
  have hzgrid : p.2 ∈ gridPts s ∩ Metric.ball (0 : Rd d) B := by
    constructor
    · refine ⟨j, ?_⟩
      rw [hz, hk]
      rfl
    · rw [Metric.mem_ball, dist_zero_right]
      dsimp [B]
      linarith
  have hzbox : p.2 ∈ shellGridBox d N s :=
    p4_shellGridBox_mono hN (grid_ball_subset_shellGridBox hs hB hzgrid)
  have hkM : k < ⌈(n : ℝ) / Real.log lam⌉₊ + 1 :=
    p4_radius_index_lt hlam (hk ▸ hr)
  apply Finset.mem_coe.mpr
  unfold p4_gridPairsFinset
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_range.mpr hkM, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨p.2, by simpa only [N, s, r, B, smin] using hzbox, Prod.ext hk.symm rfl⟩

/-- A direct cardinal bound before replacing the ceiling parameters by an exponential. -/
theorem card_p4_gridPairsFinset_le (d : ℕ) (lam κ : ℝ) (n : ℕ) (W : ℝ) :
    (p4_gridPairsFinset d lam κ n W).card ≤
      (⌈(n : ℝ) / Real.log lam⌉₊ + 1) *
        (2 * (⌈(W + 1) / (κ * Real.exp (-(n : ℝ)))⌉₊ + 1) + 1) ^ d := by
  classical
  let M := ⌈(n : ℝ) / Real.log lam⌉₊ + 1
  let N := ⌈(W + 1) / (κ * Real.exp (-(n : ℝ)))⌉₊ + 1
  have h := Finset.card_biUnion_le_card_mul (Finset.range M)
    (fun k => (shellGridBox d N (κ * lam ^ (-(k : ℝ)))).image
      (fun z => (lam ^ (-(k : ℝ)), z))) ((2 * N + 1) ^ d)
      (by
        intro k hk
        exact (Finset.card_image_le).trans (card_shellGridBox_le d N _))
  simpa only [p4_gridPairsFinset, Finset.card_range, M, N] using h

end HigherDimLQGContinuity
