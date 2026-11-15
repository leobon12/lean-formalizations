/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow20Rational

/-! # Arbitrarily small rational landing intervals

Refining the center and radius preserves every rational test. In
particular a nonzero landing admits an interval separated from the seed.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61SlitW Aux61GWindow17 Aux61GInst Aux61Cpt LawUnique
universe u

/-- Any admitted landing interval can be refined about an interior point
to an arbitrarily small rational interval, with the same bound and margin. -/
theorem exists_landRecords_refinement (S : SourceSetting.{u}) (t : GoodTime S)
    {r : SourceRecord S.nL S.nR} {L : LandParam} (hr : r ∈ landRecords S t L)
    {y η : ℝ} (hy : |y - L.1.1| < L.1.2.1) (hη : 0 < η) :
    ∃ L' : LandParam, |y - L'.1.1| < L'.1.2.1 ∧
      |(L'.1.1 : ℝ) - y| + L'.1.2.1 < η ∧ r ∈ landRecords S t L' := by
  let δ : ℝ := min η ((L.1.2.1 : ℝ) - |y - L.1.1|)
  have hδ : 0 < δ := lt_min hη (sub_pos.2 hy)
  obtain ⟨v, hv₁, hv₂⟩ := exists_rat_btwn (show y - δ / 8 < y + δ / 8 by linarith)
  obtain ⟨e, he₁, he₂⟩ := exists_rat_btwn (show δ / 4 < δ / 2 by linarith)
  have he : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℝ) < e by linarith)
  let L' : LandParam := ⟨(v, e, L.1.2.2.1, L.1.2.2.2), he, L.2.2⟩
  have hv : |(v : ℝ) - y| < δ / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hsmall : |(v : ℝ) - y| + e < δ := by linarith
  have hgap : |(v : ℝ) - y| + e + |y - L.1.1| < L.1.2.1 := by
    have := min_le_right η ((L.1.2.1 : ℝ) - |y - L.1.1|)
    linarith
  refine ⟨L', ?_, hsmall.trans_le (min_le_left _ _), hr.1, ?_, ?_⟩
  · change |y - (v : ℝ)| < (e : ℝ)
    rw [abs_sub_comm]
    linarith
  · intro a b hb hz
    apply hr.2.1 a b hb
    have htri := dist_triangle (ratPt a b) ((v : ℝ) : ℂ) ((L.1.1 : ℝ) : ℂ)
    have hvdist : dist ((v : ℝ) : ℂ) ((L.1.1 : ℝ) : ℂ) ≤
        |(v : ℝ) - y| + |y - L.1.1| := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_sub_le _ _ _
    exact mem_ball.2 (by have := mem_ball.1 hz; change dist (ratPt a b) ((v : ℝ) : ℂ) < (e : ℝ) at this; linarith)
  · intro a ha
    apply hr.2.2 a
    have htri := abs_sub_le (a : ℝ) (v : ℝ) (L.1.1 : ℝ)
    have htri' := abs_sub_le (v : ℝ) y (L.1.1 : ℝ)
    change |(a : ℝ) - (v : ℝ)| ≤ (e : ℝ) at ha
    linarith

/-- A nonzero admitted landing has a rational test interval separated
from some positive seed radius on one of the two sides. -/
theorem exists_separated_landRecords (S : SourceSetting.{u}) (t : GoodTime S)
    {r : SourceRecord S.nL S.nR} {L : LandParam} (hr : r ∈ landRecords S t L)
    {y : ℝ} (hy : |y - L.1.1| < L.1.2.1) (hy0 : y ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L' : LandParam, |y - L'.1.1| < L'.1.2.1 ∧
      r ∈ landRecords S t L' ∧
      (ε ≤ (L'.1.1 : ℝ) - L'.1.2.1 ∨ (L'.1.1 : ℝ) + L'.1.2.1 ≤ -ε) := by
  have he : 0 < |y| / 2 := half_pos (abs_pos.2 hy0)
  obtain ⟨L', hy', hs, hr'⟩ := exists_landRecords_refinement S t hr hy he
  refine ⟨|y| / 2, he, L', hy', hr', ?_⟩
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · right
    rw [abs_of_neg hneg] at hs ⊢
    have h := le_abs_self ((L'.1.1 : ℝ) - y)
    linarith
  · left
    rw [abs_of_pos hpos] at hs ⊢
    have h := neg_le_abs ((L'.1.1 : ℝ) - y)
    linarith

end InteractingSLE.Sec5.Aux61GWindow20
