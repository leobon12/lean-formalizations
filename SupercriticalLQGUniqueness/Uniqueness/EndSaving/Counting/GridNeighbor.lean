import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.OldGeoLength
import Mathlib.Data.Int.Interval




 
set_option autoImplicit false
noncomputable section
open Set Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting

def neighbors (i : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc (i.1 - 800) (i.1 + 800) ×ˢ Finset.Icc (i.2 - 800) (i.2 + 800)

theorem self_mem_neighbors (i : ℤ × ℤ) : i ∈ neighbors i := by
  simp [neighbors]

theorem neighbors_symm (i j : ℤ × ℤ) : i ∈ neighbors j ↔ j ∈ neighbors i := by
  simp only [neighbors, Finset.mem_product, Finset.mem_Icc]
  omega

theorem neighbors_card (i : ℤ × ℤ) : (neighbors i).card = 1601 ^ 2 := by
  have h1 : (Finset.Icc (i.1 - 800) (i.1 + 800)).card = 1601 := by
    rw [Int.card_Icc]
    omega
  have h2 : (Finset.Icc (i.2 - 800) (i.2 + 800)).card = 1601 := by
    rw [Int.card_Icc]
    omega
  simp [neighbors, h1, h2, pow_two]

theorem coordinate_bound
    {δ r : ℝ} (hδ : δ = r / 100) (hr : 0 < r)
    (a b : ℤ) (h : |δ * (a : ℝ) - δ * (b : ℝ)| < 8 * r) :
    b - 800 ≤ a ∧ a ≤ b + 800 := by
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hratio : |((a - b : ℤ) : ℝ)| < 800 := by
    have heq : |δ * (a : ℝ) - δ * (b : ℝ)| = δ * |((a - b : ℤ) : ℝ)| := by
      rw [← mul_sub, ← Int.cast_sub, abs_mul, abs_of_pos hδpos]
    rw [heq] at h
    have heq8 : 8 * r = δ * 800 := by rw [hδ]; ring
    rw [heq8] at h
    by_contra hn
    have hle : (800 : ℝ) ≤ |((a - b : ℤ) : ℝ)| := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hδpos)
    linarith
  have hparts := abs_lt.mp hratio
  constructor
  · exact_mod_cast (show (b : ℝ) - 800 ≤ a from by push_cast at hparts ⊢; linarith)
  · exact_mod_cast (show (a : ℝ) ≤ b + 800 from by push_cast at hparts ⊢; linarith)

theorem ball_overlap_mem_neighbors
    (r : Set.Ioi (0 : ℝ)) (i j : ℤ × ℤ)
    (h : ¬ Disjoint
      (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
      (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)))) :
    i ∈ neighbors j := by
  obtain ⟨x, hxi, hxj⟩ := Set.not_disjoint_iff.mp h
  have hdist : dist (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) < 8 * (r : ℝ) := by
    calc
      _ ≤ dist (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) x +
          dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) := dist_triangle _ _ _
      _ < 8 * (r : ℝ) := by
        have hi := Metric.mem_ball.mp hxi
        have hj := Metric.mem_ball.mp hxj
        rw [dist_comm] at hi
        nlinarith
  have hre : |(((LQGMetric.GM.gridPt ((r : ℝ) / 100) i) -
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) j)).re)| < 8 * (r : ℝ) := by
    exact (Complex.abs_re_le_norm _).trans_lt (by simpa [dist_eq_norm] using hdist)
  have him : |(((LQGMetric.GM.gridPt ((r : ℝ) / 100) i) -
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) j)).im)| < 8 * (r : ℝ) := by
    exact (Complex.abs_im_le_norm _).trans_lt (by simpa [dist_eq_norm] using hdist)
  simp only [Complex.sub_re, LQGMetric.GM.gridPt_re] at hre
  simp only [Complex.sub_im, LQGMetric.GM.gridPt_im] at him
  have h1 := coordinate_bound rfl r.property i.1 j.1 hre
  have h2 := coordinate_bound rfl r.property i.2 j.2 him
  simp only [neighbors, Finset.mem_product, Finset.mem_Icc]
  exact ⟨h1, h2⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
