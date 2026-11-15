/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaSeedCover
import InteractingSLE.Spec.Supplement.GW4SafeRKappaChart
import InteractingSLE.Spec.Supplement.GW4SafeRKappaClock
import InteractingSLE.Spec.Sec7.PocketSideInActCollar

/-! # GW4: late seed references avoiding a terminal trace segment -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PocketStopSide MartChar.RealFlow

/-- The countable interior visits can satisfy an arbitrary earlier
physical-time lower bound as well as the recent-capacity condition. -/
theorem Frame.exists_rat_interior_visit_recent_capacity_after {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {a t : ℝ≥0} (ha : F.ent w ≤ a) (hat : a < t)
    (ht : (t : ℝ≥0∞) < F.exit w) (hq : 0 < F.rcap w t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℚ, (a : ℝ) < s ∧ (s : ℝ) < t ∧ trc w (s : ℝ).toNNReal ≠ 0 ∧
      -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      F.rcap w t - δ < F.rcap w (s : ℝ).toNNReal ∧ F.rcap w (s : ℝ).toNNReal < F.rcap w t := by
  obtain ⟨T, htT, hLoc⟩ := Frame.exists_isLoc_gt hF hw ht
  have hgap := Frame.rcap_strictMono hF hLoc ha hat htT
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsCap, hsCapLt⟩ :=
    Frame.exists_rat_interior_visit_recent_capacity hF hw ht hq
      (lt_min hδ (sub_pos.2 hgap))
  have hsNonneg : 0 ≤ (s : ℝ) := (F.ent w).coe_nonneg.trans hsEnt.le
  have hsExit : ((s : ℝ).toNNReal : ℝ≥0∞) < F.exit w :=
    (ENNReal.coe_lt_coe.2 (Real.toNNReal_lt_iff_lt_coe hsNonneg |>.2 hst)).trans ht
  have has : a < (s : ℝ).toNNReal := Frame.lt_of_rcap_lt hF hw
    ((ENNReal.coe_lt_coe.2 hat).trans ht) hsExit (by
      linarith only [hsCap, min_le_right δ (F.rcap w t - F.rcap w a)])
  exact ⟨s, by simpa only [Real.coe_toNNReal _ hsNonneg] using NNReal.coe_lt_coe.2 has,
    hst, hs0, hsC, (sub_le_sub_left (min_le_left _ _) _).trans_lt hsCap, hsCapLt⟩

/-- An exposed nonzero coordinate has a late rational interior reference
with an old exposed coordinate, a physical collar, zero own lift, and a
terminal trace segment avoiding its finite landing. -/
theorem Frame.exists_seed_reference_avoiding_tail {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {B : Chart} (hB : B.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < F.exit w) (hq : 0 < F.rcap w t) {ξ : ℝ} (hξ : ξ ≠ 0)
    (hξSeed : ξ ∈ Ioo
      (-rightImg (fun r => -W r) 0 (F.rcap w t) - W (F.rcap w t))
      (rightImg W 0 (F.rcap w t) - W (F.rcap w t)))
    {p : ℂ} (hp : p ≠ trc w t) :
    ∃ s : ℚ, (F.ent w : ℝ) < s ∧ (s : ℝ) < t ∧ trc w (s : ℝ).toNNReal ≠ 0 ∧
      -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      0 < F.rcap w (s : ℝ).toNNReal ∧ F.rcap w (s : ℝ).toNNReal < F.rcap w t ∧
      (∃ ρ > 0, Disjoint ((fun u : ℝ => trc w u.toNNReal) '' Icc (s : ℝ) (t : ℝ)) (closedBall p ρ)) ∧
      ∃ x r : ℝ, x ∈ Ioo
        (-rightImg (fun u => -W u) 0 (F.rcap w (s : ℝ).toNNReal) - W (F.rcap w (s : ℝ).toNNReal))
        (rightImg W 0 (F.rcap w (s : ℝ).toNNReal) - W (F.rcap w (s : ℝ).toNNReal)) ∧ 0 < r ∧
        (B.loewner W (F.rcap w (s : ℝ).toNNReal)).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
          ((B.loewner W (F.rcap w t)).dom : Set ℂ) ∧
        Tendsto (fun z => (B.loewner W (F.rcap w (s : ℝ).toNNReal)).1
          ((B.loewner W (F.rcap w t)).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun z => (B.loewner W (F.rcap w t)).2.2 ((B.loewner W (F.rcap w t)).2.1 z) -
          (B.loewner W (F.rcap w (s : ℝ).toNNReal)).2.2
            ((B.loewner W (F.rcap w t)).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hη : Continuous (fun u : ℝ => trc w u.toNNReal) :=
    (Frame.continuous_trc hw).comp continuous_real_toNNReal
  have het := Frame.ent_lt_of_rcap_pos hF hw hq
  obtain ⟨u, heu, hut, ρ, hρ, hTail⟩ := exists_rat_terminal_trace_avoids hη.continuousOn
    (F.ent w).coe_nonneg (NNReal.coe_lt_coe.2 het)
    (show p ≠ trc w (t : ℝ).toNNReal by simpa only [Real.toNNReal_coe] using hp)
  have hu0 : 0 ≤ (u : ℝ) := (F.ent w).coe_nonneg.trans heu.le
  have heu' : F.ent w ≤ (u : ℝ).toNNReal := (Real.le_toNNReal_iff_coe_le hu0).2 heu.le
  have hut' : (u : ℝ).toNNReal < t := Real.toNNReal_lt_iff_lt_coe hu0 |>.2 hut
  obtain ⟨δ, hδ, hδq, hCol⟩ := exists_recent_own_seed_collars hW hW0 hq hξ hξSeed
  obtain ⟨s, hus, hst, hs0, hsC, hsCap, hsLt⟩ :=
    Frame.exists_rat_interior_visit_recent_capacity_after hF hw heu' hut' ht hq hδ
  have hs0' : 0 < F.rcap w (s : ℝ).toNNReal := by linarith only [hsCap, hδq]
  obtain ⟨x, r, hx, hr, hcol, htr, -⟩ := hCol _ ⟨hsCap, hsLt⟩
  refine ⟨s, heu.trans_le ?_, hst, hs0, hsC, hs0', hsLt, ?_, x, r, hx, hr,
    own_collar_pullback hB hW hW0 hs0'.le hsLt.le hr hcol htr⟩
  · simpa only [Real.coe_toNNReal _ hu0] using hus.le
  · refine ⟨ρ, hρ, hTail.mono_left (image_mono (Icc_subset_Icc_left ?_))⟩
    simpa only [Real.coe_toNNReal _ hu0] using hus.le

end InteractingSLE.Theorem14.GW4Fix
