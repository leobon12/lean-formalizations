/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaCollar
import InteractingSLE.Spec.Supplement.GW4FixPhysRead

/-!
# GW4: rational interior visits arbitrarily close in relative capacity

The actual traversal visits the open component in every interval before
exit. Continuity makes such a visit persist on an open physical interval,
which contains a rational time. The relative capacities of these visits
approach every positive live capacity from below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

/-- The own reference cover can be chosen from a fixed countable family. -/
theorem exists_rat_own_collar {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t ξ : ℝ} (ht : 0 < t) (hξ : ξ ≠ 0) :
    ∃ s : ℚ, 0 < (s : ℝ) ∧ (s : ℝ) < t ∧ ∃ x r : ℝ, 0 < r ∧
      (Chart.id.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((Chart.id.loewner W t).dom : Set ℂ) ∧
      Tendsto (fun z => (Chart.id.loewner W s).1 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (fun z => (Chart.id.loewner W t).2.2 ((Chart.id.loewner W t).2.1 z) -
          (Chart.id.loewner W s).2.2 ((Chart.id.loewner W t).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hδt, hCol⟩ := exists_recent_own_collars hW hW0 ht hξ
  obtain ⟨s, hs, hst⟩ := exists_rat_btwn (show t - δ < t by linarith only [hδ])
  exact ⟨s, by linarith only [hs, hδt], hst, hCol s ⟨hs, hst⟩⟩

namespace Frame

/-- Every open physical interval of a traversal contains a rational
interior visit, with the literal inverted counterflow trace in the component. -/
theorem exists_rat_interior_visit {F : Frame} (hF : F.IsOk) {w : ℝ≥0 → ℝ}
    (hw : F.IsPathOk w) {a b : ℝ≥0} (ha : F.ent w ≤ a) (hab : a < b)
    (hb : (b : ℝ≥0∞) < F.exit w) :
    ∃ s : ℚ, (a : ℝ) < s ∧ (s : ℝ) < b ∧
      trc w (s : ℝ).toNNReal ≠ 0 ∧ -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C := by
  obtain ⟨v, hv, hv0, hvC⟩ := clause_density hF hw a b ha hab hb
  have htr : Continuous (fun s : ℝ => trc w s.toNNReal) :=
    (continuous_trc hw).comp continuous_real_toNNReal
  have hv0' : trc w (v : ℝ).toNNReal ≠ 0 := by
    simpa only [Real.toNNReal_coe] using hv0
  have hNear0 : ∀ᶠ s : ℝ in 𝓝 (v : ℝ), trc w s.toNNReal ≠ 0 :=
    htr.continuousAt.eventually_ne hv0'
  have hInv : ContinuousAt (fun s : ℝ => -(trc w s.toNNReal)⁻¹) (v : ℝ) :=
    (htr.continuousAt.inv₀ hv0').neg
  have hNearC : ∀ᶠ s : ℝ in 𝓝 (v : ℝ), -(trc w s.toNNReal)⁻¹ ∈ F.C := by
    apply hInv.eventually
    apply (isOpen_C hF hw).mem_nhds
    simpa only [Real.toNNReal_coe] using hvC
  have hNearI : ∀ᶠ s : ℝ in 𝓝 (v : ℝ), s ∈ Ioo (a : ℝ) (b : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨NNReal.coe_lt_coe.2 hv.1, NNReal.coe_lt_coe.2 hv.2⟩
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.1 (hNearI.and (hNear0.and hNearC))
  obtain ⟨s, hs⟩ := Rat.denseRange_cast.exists_mem_open
    (show IsOpen (ball (v : ℝ) ε) from isOpen_ball) (nonempty_ball.2 hε)
  exact ⟨s, (hBall hs).1.1, (hBall hs).1.2, (hBall hs).2⟩

/-- Rational interior visits occur arbitrarily close to a positive live
relative capacity, strictly before its physical time. -/
theorem exists_rat_interior_visit_recent_capacity {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < F.exit w) (hq : 0 < F.rcap w t)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℚ, (F.ent w : ℝ) < s ∧ (s : ℝ) < t ∧
      trc w (s : ℝ).toNNReal ≠ 0 ∧ -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
      F.rcap w t - δ < F.rcap w (s : ℝ).toNNReal ∧
      F.rcap w (s : ℝ).toNNReal < F.rcap w t := by
  have het : F.ent w < t := lt_of_not_ge fun h => by
    rw [rcap_eq_zero_of_le hF hw h] at hq
    exact (lt_irrefl _) hq
  have hc := continuousOn_rcap hF hw t ht
  have hLower : ENNReal.ofReal (F.rcap w t - δ) < ENNReal.ofReal (F.rcap w t) :=
    (ENNReal.ofReal_lt_ofReal_iff hq).2 (sub_lt_self _ hδ)
  have hNear : ∀ᶠ v : ℝ≥0 in 𝓝[{v | (v : ℝ≥0∞) < F.exit w}] t,
      ENNReal.ofReal (F.rcap w t - δ) < ENNReal.ofReal (F.rcap w v) :=
    hc.eventually (Ioi_mem_nhds hLower)
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhdsWithin_iff.1 hNear
  let a : ℝ≥0 := max (F.ent w) ((t : ℝ) - ε / 2).toNNReal
  have hat : a < t := max_lt het (by
    by_cases hpos : 0 ≤ (t : ℝ) - ε / 2
    · rw [Real.toNNReal_lt_iff_lt_coe hpos]
      linarith only [hε]
    · rw [Real.toNNReal_eq_zero.2 (le_of_not_ge hpos)]
      exact (show (0 : ℝ≥0) ≤ F.ent w from bot_le).trans_lt het)
  obtain ⟨s, has, hst, hs0, hsC⟩ := exists_rat_interior_visit hF hw
    (le_max_left _ _) hat ht
  have hsNonneg : 0 ≤ (s : ℝ) := (a.coe_nonneg.trans has.le)
  have hsn : (s : ℝ).toNNReal < t := by
    exact_mod_cast (show ((s : ℝ).toNNReal : ℝ) < t by rw [Real.coe_toNNReal _ hsNonneg]; exact hst)
  have hsExit : ((s : ℝ).toNNReal : ℝ≥0∞) < F.exit w :=
    (ENNReal.coe_lt_coe.2 hsn).trans ht
  have hsBall : (s : ℝ).toNNReal ∈ ball t ε := by
    rw [mem_ball, NNReal.dist_eq, Real.coe_toNNReal _ hsNonneg,
      abs_of_neg (sub_neg.2 hst)]
    have hLowerTime : (t : ℝ) - ε / 2 ≤ a :=
      (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.2 (le_max_right _ _))
    linarith only [has, hLowerTime, hε]
  have hCap := hBall ⟨hsBall, hsExit⟩
  have hsEnt : F.ent w < (s : ℝ).toNNReal := by
    apply NNReal.coe_lt_coe.1
    rw [Real.coe_toNNReal _ hsNonneg]
    exact (NNReal.coe_le_coe.2 (le_max_left _ _)).trans_lt has
  obtain ⟨T, htT, hloc⟩ := exists_isLoc_gt hF hw ht
  exact ⟨s, by simpa only [Real.coe_toNNReal _ hsNonneg] using NNReal.coe_lt_coe.2 hsEnt,
    hst, hs0, hsC, ENNReal.ofReal_lt_ofReal_iff'.1 hCap |>.1,
    rcap_strictMono hF hloc hsEnt.le hsn htT⟩

end Frame

end InteractingSLE.Theorem14.GW4Fix
