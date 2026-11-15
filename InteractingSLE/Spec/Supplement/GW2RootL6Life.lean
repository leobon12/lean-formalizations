/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageUnit

/-!
# Lifetime control for GW2's varying-angle words

Continuation of PROVE-T14-GW2ROOT2. These lemmas extend the spatial part of
the Proposition 5.9 unit argument to arbitrary force weights. The sole
weight condition is that the first right weight exceeds `-2`; all other
marks are kept separated from the driver. No alternating-word identity is
used. The terminal-state input is supplied for evolutions by the existing
almost-sure limit-at-threshold theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootL6

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-- Only the first right mark may meet the driver, and its weight is
admissible. Thus neither side can trigger the continuation threshold. -/
theorem not_threshold_of_only_first_right {w : ℝ}
    {vL : Fin nL → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hρ : -2 < ρR 0) (hL : ∀ i, vL i ≠ w)
    (hR : ∀ i : Fin nR, vR i.succ ≠ w) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  have eL : (univ.filter fun i => vL i = w) = ∅ :=
    filter_eq_empty_iff.2 fun i _ => hL i
  have hsub : (univ.filter fun i => vR i = w) ⊆ {0} := by
    intro i hi
    have hvi := (mem_filter.1 hi).2
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
    · exact Finset.mem_singleton.mpr h0
    · exact False.elim (hR j hvi)
  have hsum : -2 < ∑ i ∈ univ.filter (fun i => vR i = w), ρR i := by
    rcases subset_singleton_iff.1 hsub with he | he
    · rw [he, sum_empty]; norm_num
    · rw [he, sum_singleton]; exact hρ
  simp only [ForceWord.ThresholdCondition, eL, sum_empty, not_or, not_le]
  exact ⟨by norm_num, hsum⟩

variable {xL : Fin nL → ℝ} {xR : Fin (nR + 1) → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {a : ℝ}

/-- The old marks remain outside `[-7/4,7/4]` in absolute coordinates
whenever the driver is within one of its value at the zero restart. -/
theorem gaps_of_near_zero
    (hp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hy : (a, xL, xR) ∈ Sec5.Prop59Stage.startsU)
    {τ t : ℝ≥0} (hzero : a + w τ = 0) (ht : (t : ℝ≥0∞) < ζ)
    (hnear : |w t - w τ| ≤ 1) :
    (∀ i, 3 / 4 ≤ w t - vL i t) ∧
      ∀ i : Fin nR, 3 / 4 ≤ vR i.succ t - w t := by
  have hband : -1 ≤ a + w t ∧ a + w t ≤ 1 := by
    rw [abs_le] at hnear
    constructor <;> linarith only [hzero, hnear.1, hnear.2]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hpos := hy.2.2.1.2.1 i
    have hmark := hp.vL_le_xL ht i
    linarith only [hy.2.1, hband.1, hpos, hmark]
  · have hpos := hy.2.2.2 i.succ (by simp)
    have hmark := hp.xR_le_vR ht i.succ
    linarith only [hpos, hband.2, hmark]

/-- An arbitrary finite-force word cannot reach its continuation threshold
while the restarted driver stays within one of zero. Far bad weights do
not enter the proof, since their coordinates remain separated. -/
theorem lt_lifetime_of_near_zero
    (hp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hy : (a, xL, xR) ∈ Sec5.Prop59Stage.startsU) (hρ : -2 < ρR 0)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (nR + 1) → ℝ),
        Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {τ t : ℝ≥0} (hzero : a + w τ = 0) (hτζ : (τ : ℝ≥0∞) < ζ)
    (hnear : ∀ u < t, |w (τ + u) - w τ| < 1) :
    ((τ + t : ℝ≥0) : ℝ≥0∞) < ζ := by
  by_contra hnot
  have hge : ζ ≤ (τ + t : ℝ≥0) := le_of_not_gt hnot
  have hζtop : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hge
  let T : ℝ≥0 := ζ.toNNReal
  have hT : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζtop
  have hτT : τ < T := by rw [← ENNReal.coe_lt_coe, hT]; exact hτζ
  have hTt : T ≤ τ + t := by rw [← ENNReal.coe_le_coe, hT]; exact hge
  obtain ⟨w₀, vL₀, vR₀, htend, hthr⟩ := hlim T (zero_le.trans_lt hτT) hT
  have hev : ∀ᶠ u in 𝓝[<] T, τ < u ∧ u < T := by
    filter_upwards [Ioo_mem_nhdsLT hτT] with u hu using hu
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨τ, hτT⟩
  have hgap : ∀ᶠ u in 𝓝[<] T,
      (∀ i, 3 / 4 ≤ w u - vL i u) ∧
        ∀ i : Fin nR, 3 / 4 ≤ vR i.succ u - w u := by
    filter_upwards [hev] with u hu
    have huζ : (u : ℝ≥0∞) < ζ := by rw [← hT]; exact_mod_cast hu.2
    have hd : u - τ < t := (tsub_lt_iff_left hu.1.le).2 (hu.2.trans_le hTt)
    have h := hnear (u - τ) hd
    rw [add_tsub_cancel_of_le hu.1.le] at h
    exact gaps_of_near_zero hp hy hzero huζ h.le
  have hw₀ := (continuous_fst.tendsto _).comp htend
  have hvL₀ : ∀ i, Tendsto (fun u => vL i u) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp
      ((continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp htend))
  have hvR₀ : ∀ i, Tendsto (fun u => vR i u) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp
      ((continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp htend))
  have hL : ∀ i, 3 / 4 ≤ w₀ - vL₀ i := fun i =>
    ge_of_tendsto (hw₀.sub (hvL₀ i)) (hgap.mono fun _ hu => hu.1 i)
  have hR : ∀ i : Fin nR, 3 / 4 ≤ vR₀ i.succ - w₀ := fun i =>
    ge_of_tendsto ((hvR₀ i.succ).sub hw₀) (hgap.mono fun _ hu => hu.2 i)
  exact not_threshold_of_only_first_right hρ
    (fun i h => by have := hL i; rw [h] at this; linarith only [this])
    (fun i h => by have := hR i; rw [h] at this; linarith only [this]) hthr

/-- The open-interval control also gives the closed gap bound at the
endpoint. Lifetime control is proved first, so continuity there is justified. -/
theorem lifetime_and_gaps_of_near_zero
    (hp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hy : (a, xL, xR) ∈ Sec5.Prop59Stage.startsU) (hρ : -2 < ρR 0)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (nR + 1) → ℝ),
        Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {τ t : ℝ≥0} (hzero : a + w τ = 0) (hτζ : (τ : ℝ≥0∞) < ζ)
    (hnear : ∀ u < t, |w (τ + u) - w τ| < 1) :
    ((τ + t : ℝ≥0) : ℝ≥0∞) < ζ ∧
      (∀ i, 3 / 4 ≤ w (τ + t) - vL i (τ + t)) ∧
        ∀ i : Fin nR, 3 / 4 ≤ vR i.succ (τ + t) - w (τ + t) := by
  have hlife := lt_lifetime_of_near_zero hp hy hρ hlim hzero hτζ hnear
  refine ⟨hlife, gaps_of_near_zero hp hy hzero hlife ?_⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | ht
  · rw [← h0, add_zero, sub_self, abs_zero]
    norm_num
  · have hc : ContinuousAt (fun u : ℝ≥0 => |w (τ + u) - w τ|) t := by
      have hw := hp.continuousOn_w.continuousAt
        ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hlife)
      exact ((hw.comp (continuous_const.add continuous_id).continuousAt).sub
        continuousAt_const).abs
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t)))
      (eventually_nhdsWithin_of_forall (s := Iio t) fun u hu => (hnear u hu).le)

end InteractingSLE.Theorem14.GW2TipSystem.RootL6
