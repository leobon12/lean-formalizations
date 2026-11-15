/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkRegular5Close

/-!
# Finite force-coordinate limits for a local solution with a completed trace

The inverse-gap estimate of `Sec2.IsForcePath.vL_sub_ge_of_gap` uses only local
force equations. Its local adapter below supplies boundedness without maximality.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Regular5

variable {a : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
  {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- The standard inverse-gap rate bound, adapted to a local solution. -/
theorem vL_sub_ge_of_gap (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    {i : Fin nL} {p q : ℝ≥0} (hpq : p ≤ q) (hq : (q : ℝ≥0∞) < τ)
    (hgap : ∀ s : ℝ≥0, p ≤ s → s ≤ q → 1 ≤ w s - vL i s) :
    vL i p - 2 * ((q : ℝ) - p) ≤ vL i q := by
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume p q :=
    (h.intervalIntegrable_forceL hq i).mono_set (by
      rw [uIcc_of_le hpq', uIcc_of_le (NNReal.coe_nonneg q)]
      exact Icc_subset_Icc (NNReal.coe_nonneg p) le_rfl)
  have hle : (∫ _ in (p : ℝ)..q, (-2 : ℝ)) ≤
      ∫ r in (p : ℝ)..q, 2 / (vL i r.toNNReal - w r.toNNReal) := by
    refine intervalIntegral.integral_mono_on hpq' intervalIntegrable_const hint fun r hr => ?_
    have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg p).trans hr.1
    have hg := hgap _ ((Real.le_toNNReal_iff_coe_le hr0).2 hr.1)
      (Real.toNNReal_le_iff_le_coe.2 hr.2)
    rw [← neg_sub, div_neg]
    have : 2 / (w r.toNNReal - vL i r.toNNReal) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul, ← h.vL_sub hpq hq i] at hle
  linarith

/-- A bounded driver prevents a left force coordinate from escaping in finite time. -/
theorem bddBelow_vL_of_le_w (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) = τ) {m : ℝ}
    (hm : ∀ s : ℝ≥0, s < T → m ≤ w s) (i : Fin nL) :
    BddBelow (vL i '' Iio T) := by
  by_cases hbound : ∀ s : ℝ≥0, s < T → m - 1 ≤ vL i s
  · exact ⟨m - 1, by rintro _ ⟨s, hs, rfl⟩; exact hbound s hs⟩
  push Not at hbound
  obtain ⟨p, hp, hpm⟩ := hbound
  refine ⟨vL i p - 2 * (T : ℝ), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hsτ : (s : ℝ≥0∞) < τ := (ENNReal.coe_lt_coe.2 hs).trans_eq hT
  rcases le_total s p with hsp | hps
  · have hv := h.vL_le_of_le hsp ((ENNReal.coe_lt_coe.2 hp).trans_eq hT) i
    linarith [T.coe_nonneg]
  · have hv := vL_sub_ge_of_gap h hps hsτ (fun r hpr hrs => by
      have hrT := hrs.trans_lt hs
      have hvr := h.vL_le_of_le hpr ((ENNReal.coe_lt_coe.2 hrT).trans_eq hT) i
      linarith [hm r hrT])
    have hsT : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 hs.le
    linarith [p.coe_nonneg]

/-- A bounded driver gives finite left and right force-coordinate limits. -/
theorem exists_force_limits_of_driver_limit
    (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = τ) (hw : ∃ c : ℝ, Tendsto w (𝓝[<] T) (𝓝 c)) :
    (∀ i, ∃ c : ℝ, Tendsto (vL i) (𝓝[<] T) (𝓝 c)) ∧
      ∀ j, ∃ c : ℝ, Tendsto (vR j) (𝓝[<] T) (𝓝 c) := by
  have hc := continuousOn_endpointClose h.continuousOn_w hT (fun _ => hw)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (show Icc 0 T ⊆ Iic T from fun _ ht => ht.2))
  have hb : ∀ s : ℝ≥0, s < T → |w s| ≤ B := by
    intro s hs
    have := hB s ⟨zero_le, hs.le⟩
    rw [endpointClose_of_lt ((ENNReal.coe_lt_coe.2 hs).trans_eq hT), Real.norm_eq_abs] at this
    exact this
  constructor
  · intro i
    refine ⟨sInf (vL i '' Iio T), AntitoneOn.tendsto_nhdsLT ?_ ?_⟩
    · exact fun s _ t ht hst => h.vL_le_of_le hst ((ENNReal.coe_lt_coe.2 ht).trans_eq hT) i
    · exact bddBelow_vL_of_le_w h hT (fun s hs => (abs_le.1 (hb s hs)).1) i
  · intro j
    have hneg := bddBelow_vL_of_le_w h.reflect hT
      (m := -B) (fun s hs => by simpa using neg_le_neg (abs_le.1 (hb s hs)).2) j
    refine ⟨sSup (vR j '' Iio T), MonotoneOn.tendsto_nhdsLT ?_ ?_⟩
    · exact fun s _ t ht hst => h.le_vR_of_le hst ((ENNReal.coe_lt_coe.2 ht).trans_eq hT) j
    · obtain ⟨M, hM⟩ := hneg
      refine ⟨-M, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have := hM (mem_image_of_mem (fun s => -vR j s) hs)
      change M ≤ -vR j s at this
      linarith

/-- A completed generating trace gives finite limits for every local force coordinate. -/
theorem exists_force_limits_of_isGeneratingTrace
    (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = τ) (hpos : 0 < T) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w τ η) :
    (∀ i, ∃ c : ℝ, Tendsto (vL i) (𝓝[<] T) (𝓝 c)) ∧
      ∀ j, ∃ c : ℝ, Tendsto (vR j) (𝓝[<] T) (𝓝 c) := by
  have hη' : IsGeneratingTrace w (T : ℝ≥0∞) η := hT.symm ▸ hη
  have hw := Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace hη'
    (hT.symm ▸ h.continuousOn_w) h.w_zero hpos
  exact exists_force_limits_of_driver_limit h hT hw

end InteractingSLE.Sec5.TwoMark.Regular5
