import QuantumZipper.Proofs.Thm18.G2DisintXGeom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: the bump in region 2 and its geometry

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66, and of Thm. 1.8, p. 71): the bump `φ₂` sits
in `U₂` between `0` and the root `y`. With `m' = min m r₂`, `p = t₂ − r₂ + m'/2`, `R = m'/4`:
the bump lies in `B(t₂, r₂) ⊆ B(0, 1)`, right of `0` (`g2r_bump_pos`), and a root `y` with margin
`m` satisfies `p + R < y − R` (`g2r_margin_right`). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

def g2rM' (i : G3Idx) (m : ℝ) : ℝ := min m i.r₂
def g2rP (i : G3Idx) (m : ℝ) : ℝ := i.t₂ - i.r₂ + g2rM' i m / 2
def g2rR (i : G3Idx) (m : ℝ) : ℝ := g2rM' i m / 4

theorem g2rM'_pos (i : G3Idx) {m : ℝ} (hm : 0 < m) : 0 < g2rM' i m := lt_min hm i.r₂_pos

theorem g2rR_pos (i : G3Idx) {m : ℝ} (hm : 0 < m) : 0 < g2rR i m := by
  unfold g2rR; linarith [g2rM'_pos i hm]

theorem g2r_t₂r₂ (i : G3Idx) : i.t₂ - i.r₂ = (3 / 4) * i.η := by
  unfold G3Idx.t₂ G3Idx.r₂; ring

theorem g2r_bump_pos (i : G3Idx) {m : ℝ} (hm : 0 < m) : 0 < g2rP i m - g2rR i m := by
  have := g2rM'_pos i hm; have := i.hη
  unfold g2rP g2rR; rw [g2r_t₂r₂]; linarith

theorem g2r_bump_sub (i : G3Idx) {m : ℝ} (hm : 0 < m) :
    closedBall (g2rP i m : ℂ) (g2rR i m) ⊆ ball (i.t₂ : ℂ) i.r₂ := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  rw [mem_ball, Complex.dist_eq]
  have h1 : g2rM' i m ≤ i.r₂ := min_le_right _ _
  have h2 := g2rM'_pos i hm
  calc ‖z - i.t₂‖ ≤ ‖z - g2rP i m‖ + ‖((g2rP i m : ℂ) - i.t₂)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < i.r₂ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (by unfold g2rP; linarith)]
        unfold g2rP g2rR at *; linarith

theorem g2r_ball_sub_unit (i : G3Idx) : ball (i.t₂ : ℂ) i.r₂ ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  rw [mem_ball, Complex.dist_eq] at hz
  rw [mem_ball, dist_zero_right]
  have h2 : |i.t₂| + i.r₂ < 1 := by
    have := i.hη; have := i.hηδ; have := i.hδ
    rw [abs_of_pos (by unfold G3Idx.t₂; linarith)]; unfold G3Idx.t₂ G3Idx.r₂; linarith
  calc ‖z‖ ≤ ‖z - i.t₂‖ + ‖(i.t₂ : ℂ)‖ := norm_le_norm_sub_add _ _
    _ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

/-- The bump of the `R` side. -/
def g2rφ (i : G3Idx) (m : ℝ) : ℂ → ℝ := g2Phi (g2rP i m) (g2rR i m)

theorem g2rφ_bump_hyps (i : G3Idx) {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g2rφ i m) ∧ HasCompactSupport (g2rφ i m) ∧
      tsupport (g2rφ i m) ⊆ ball (0 : ℂ) 1 ∧
      (∀ z, g2rφ i m (starRingEnd ℂ z) = g2rφ i m z) ∧ (∃ z, g2rφ i m z ≠ 0) :=
  ⟨contDiff_g2Phi _ _, hasCompactSupport_g2Phi (g2rR_pos i hm).le,
    ((tsupport_g2Phi_subset (g2rR_pos i hm).le).trans (g2r_bump_sub i hm)).trans
      (g2r_ball_sub_unit i),
    g2Phi_conj _ _, ⟨_, g2Phi_center_ne_zero (g2rR_pos i hm)⟩⟩

theorem g2rφ_zero_off (i : G3Idx) {m : ℝ} (hm : 0 < m) {z : ℂ}
    (hz : z ∉ ball (i.t₂ : ℂ) i.r₂) : g2rφ i m z = 0 := by
  by_contra h
  exact hz (g2r_bump_sub i hm (tsupport_g2Phi_subset (g2rR_pos i hm).le
    (subset_tsupport _ (Function.mem_support.2 h))))

theorem g2r_margin_right (i : G3Idx) {m y : ℝ} (hm : 0 < m) (hy : |y - i.t₂| + m < i.r₂) :
    g2rP i m + g2rR i m < y - g2rR i m := by
  have h1 : g2rM' i m ≤ m := min_le_left _ _
  have h2 := g2rM'_pos i hm
  have h3 := neg_abs_le (y - i.t₂)
  unfold g2rP g2rR; linarith

theorem g2rφ_real_right (i : G3Idx) {m t : ℝ} (hm : 0 < m) (ht : g2rP i m + g2rR i m ≤ t) :
    g2rφ i m (t : ℂ) = 0 := by
  refine g2Phi_eq_zero (g2rR_pos i hm).le ?_
  have hR := g2rR_pos i hm
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem g2rφ_ball_root (i : G3Idx) {m y : ℝ} (hm : 0 < m) (hy : |y - i.t₂| + m < i.r₂) :
    ∀ z ∈ ball (y : ℂ) (g2rR i m), g2rφ i m z = 0 := by
  intro z hz
  refine g2Phi_eq_zero (g2rR_pos i hm).le ?_
  rw [mem_ball, Complex.dist_eq] at hz
  have hl := g2r_margin_right i hm hy
  have hR := g2rR_pos i hm
  have : ‖((y : ℂ) - g2rP i m)‖ = y - g2rP i m := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have ht := norm_sub_le_norm_sub_add_norm_sub (y : ℂ) z (g2rP i m : ℂ)
  rw [norm_sub_rev (y : ℂ) z] at ht
  linarith

/-- `φ₂` does not see region 1 or the outside of region 2. -/
theorem g2rφ_zero_region1 (i : G3Idx) {m : ℝ} (hm : 0 < m) {z : ℂ}
    (hz : z ∈ closedBall (i.t₁ : ℂ) i.r₁) : g2rφ i m z = 0 := by
  refine g2rφ_zero_off i hm fun hz2 => ?_
  rw [mem_closedBall, Complex.dist_eq] at hz
  rw [mem_ball, Complex.dist_eq] at hz2
  have h := i.dist_le
  rw [Complex.dist_eq] at h
  have := norm_sub_le_norm_sub_add_norm_sub (i.t₁ : ℂ) z i.t₂
  rw [norm_sub_rev (i.t₁ : ℂ) z] at this
  linarith

end Thm18Asm
end QuantumZipper
