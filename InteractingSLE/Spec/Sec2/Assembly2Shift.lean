/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.PatchingConcat
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Theorem 2.2 assembly: restarting a solution at a time

Packet PROVE-SEC2-PATCH2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`
L490–L494, "one can use this other force point … and continue"): a solution of the integrated
equations of Definition 2.1, restarted at a time `σ` before its lifetime and seen from the driver,
is a solution of the force word given by its state at `σ`, driven by the increments of the driving
path after `σ`. This is the converse of the concatenation `Sec2.IsSLEPathUpTo.concat`.

* `shiftAt σ f c t = f (σ + t) − c`;
* `Sec2.IsSLEPathUpTo.shift`: local solutions;
* `IsIntegratedSLEPath.shift`: full solutions (the two maximality clauses included);
* `ForceWord.thresholdCondition_sub_iff`: the threshold condition is translation invariant.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

/-- The threshold condition is invariant under a common translation of the state. -/
theorem ForceWord.thresholdCondition_sub_iff {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w c : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR (w - c) (fun i => vL i - c) (fun j => vR j - c) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  simp only [sub_left_inj]

namespace Sec2

namespace Assembly2

/-- The path `f` restarted at time `σ` and recentred by `c`: `t ↦ f (σ + t) − c`. -/
def shiftAt (σ : ℝ≥0) (f : ℝ≥0 → ℝ) (c : ℝ) (t : ℝ≥0) : ℝ := f (σ + t) - c

theorem shiftAt_zero (σ : ℝ≥0) (f : ℝ≥0 → ℝ) (c : ℝ) : shiftAt σ f c 0 = f σ - c := by
  rw [shiftAt, add_zero]

theorem coe_lt_sub_iff {σ t : ℝ≥0} {τ : ℝ≥0∞} :
    (t : ℝ≥0∞) < τ - σ ↔ ((σ + t : ℝ≥0) : ℝ≥0∞) < τ := by
  rw [(ENNReal.cancel_of_ne ENNReal.coe_ne_top).lt_tsub_iff_right, ENNReal.coe_add, add_comm]

theorem toNNReal_add_coe {σ : ℝ≥0} {s : ℝ} (hs : 0 ≤ s) :
    (s + (σ : ℝ)).toNNReal = σ + s.toNNReal := by
  rw [Real.toNNReal_add hs (NNReal.coe_nonneg σ), Real.toNNReal_coe, add_comm]

/-- Interval integrability of a restarted function. -/
theorem intervalIntegrable_shiftAt {σ t : ℝ≥0} {G : ℝ≥0 → ℝ}
    (h : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((σ + t : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => G (σ + s.toNNReal)) volume 0 t := by
  have hσ0 : (0 : ℝ) ≤ σ := NNReal.coe_nonneg σ
  have hσt : (σ : ℝ) ≤ ((σ + t : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add]; linarith [NNReal.coe_nonneg t]
  have h1 : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume σ ((σ + t : ℝ≥0) : ℝ) :=
    h.mono_set (by
      rw [uIcc_of_le hσt, uIcc_of_le (hσ0.trans hσt)]
      exact Icc_subset_Icc_left hσ0)
  have h2 := h1.comp_add_right (σ : ℝ)
  have e1 : (σ : ℝ) - σ = 0 := sub_self _
  have e2 : ((σ + t : ℝ≥0) : ℝ) - σ = t := by rw [NNReal.coe_add]; ring
  rw [e1, e2] at h2
  refine h2.congr ?_
  rw [uIoc_of_le (NNReal.coe_nonneg t)]
  intro s hs
  show G (s + (σ : ℝ)).toNNReal = G (σ + s.toNNReal)
  rw [toNNReal_add_coe hs.1.le]

/-- The integral over `[0, σ + t]` splits as the integral over `[0, σ]` plus the integral of the
restarted function over `[0, t]`. -/
theorem integral_eq_add_shiftAt {σ t : ℝ≥0} {G : ℝ≥0 → ℝ}
    (h : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((σ + t : ℝ≥0) : ℝ)) :
    ∫ s in (0 : ℝ)..((σ + t : ℝ≥0) : ℝ), G s.toNNReal =
      (∫ s in (0 : ℝ)..σ, G s.toNNReal) + ∫ s in (0 : ℝ)..t, G (σ + s.toNNReal) := by
  have hσ0 : (0 : ℝ) ≤ σ := NNReal.coe_nonneg σ
  have hσt : (σ : ℝ) ≤ ((σ + t : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add]; linarith [NNReal.coe_nonneg t]
  have hA : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 σ :=
    h.mono_set (by
      rw [uIcc_of_le hσ0, uIcc_of_le (hσ0.trans hσt)]
      exact Icc_subset_Icc_right hσt)
  have hB : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume σ ((σ + t : ℝ≥0) : ℝ) :=
    h.mono_set (by
      rw [uIcc_of_le hσt, uIcc_of_le (hσ0.trans hσt)]
      exact Icc_subset_Icc_left hσ0)
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB]
  congr 1
  have hc := intervalIntegral.integral_comp_add_right (fun s : ℝ => G s.toNNReal) (σ : ℝ)
    (a := 0) (b := t)
  rw [zero_add, show (t : ℝ) + σ = ((σ + t : ℝ≥0) : ℝ) by rw [NNReal.coe_add]; ring] at hc
  rw [← hc]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
  show G (s + (σ : ℝ)).toNNReal = G (σ + s.toNNReal)
  rw [toNNReal_add_coe hs.1]

/-- Collision sets of a restarted path are null. -/
theorem volume_shift_eq_zero {σ : ℝ≥0} {τ : ℝ≥0∞} {f g : ℝ≥0 → ℝ}
    (h : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ f s.toNNReal = g s.toNNReal} = 0) :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ - σ ∧
      f (σ + s.toNNReal) = g (σ + s.toNNReal)} = 0 := by
  refine measure_mono_null ?_ ((measure_preimage_add_right volume (σ : ℝ) _).trans h)
  rintro s ⟨hs0, hs, he⟩
  have e := toNNReal_add_coe (σ := σ) hs0
  refine ⟨add_nonneg hs0 (NNReal.coe_nonneg σ), ?_, ?_⟩
  · show (((s + (σ : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) < τ
    rw [e]; exact coe_lt_sub_iff.1 hs
  · show f (s + (σ : ℝ)).toNNReal = g (s + (σ : ℝ)).toNNReal
    rw [e]; exact he

/-- Limits from the left of a restarted function. -/
theorem tendsto_of_tendsto_shift {E : Type*} [TopologicalSpace E] {σ T : ℝ≥0} (hT : 0 < T)
    {F : ℝ≥0 → E} {y : E} (h : Tendsto (fun t => F (σ + t)) (𝓝[<] T) (𝓝 y)) :
    Tendsto F (𝓝[<] (σ + T)) (𝓝 y) := by
  have hg : Tendsto (fun u : ℝ≥0 => u - σ) (𝓝[<] (σ + T)) (𝓝[<] T) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun u : ℝ≥0 => u - σ := continuous_id.sub continuous_const
      have := (hc.tendsto (σ + T)).mono_left (nhdsWithin_le_nhds (s := Iio (σ + T)))
      simpa only [add_tsub_cancel_left] using this
    · filter_upwards [self_mem_nhdsWithin] with u hu
      rcases le_total σ u with hσu | hσu
      · exact (tsub_lt_iff_left hσu).2 hu
      · rw [tsub_eq_zero_of_le hσu]; exact hT
  have hev : ∀ᶠ u in 𝓝[<] (σ + T), F u = F (σ + (u - σ)) := by
    have hlt : σ < σ + T := lt_add_of_pos_right σ hT
    filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
    rw [add_tsub_cancel_of_le hu.1.le]
  exact (h.comp hg).congr' (hev.mono fun u hu => hu.symm)

end Assembly2

open Assembly2

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **Restart of a local solution** at a time `σ < τ`: the restarted, recentred path is a local
solution of the word `(vL σ − w σ; vR σ − w σ)` before `τ − σ`, driven by `b (σ + ·) − b σ`. -/
theorem shift (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < τ) :
    IsSLEPathUpTo a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR (shiftAt σ w (w σ))
      (fun i => shiftAt σ (vL i) (w σ)) (fun j => shiftAt σ (vR j) (w σ))
      (shiftAt σ b (b σ)) (τ - σ) := by
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ - σ → ((σ + t : ℝ≥0) : ℝ≥0∞) < τ :=
    fun ht => coe_lt_sub_iff.1 ht
  have hcont : ∀ {f : ℝ≥0 → ℝ} (c : ℝ), ContinuousOn f {t | (t : ℝ≥0∞) < τ} →
      ContinuousOn (shiftAt σ f c) {t | (t : ℝ≥0∞) < τ - σ} := by
    intro f c hf
    refine (hf.comp (continuous_const.add continuous_id).continuousOn ?_).sub continuousOn_const
    exact fun t ht => hlt ht
  -- integrals of differences, restarted
  have hgap : ∀ (u v : ℝ≥0 → ℝ) {t : ℝ≥0},
      IntervalIntegrable (fun s : ℝ => (u s.toNNReal - v s.toNNReal)⁻¹) volume 0
        ((σ + t : ℝ≥0) : ℝ) →
      IntervalIntegrable (fun s : ℝ => (shiftAt σ u (w σ) s.toNNReal -
        shiftAt σ v (w σ) s.toNNReal)⁻¹) volume 0 t := by
    intro u v t hi
    refine (intervalIntegrable_shiftAt (G := fun s => (u s - v s)⁻¹) hi).congr fun s _ => ?_
    simp only [shiftAt, sub_sub_sub_cancel_right]
  have hint : ∀ (c : ℝ) (u v : ℝ≥0 → ℝ) {t : ℝ≥0},
      IntervalIntegrable (fun s : ℝ => c / (u s.toNNReal - v s.toNNReal)) volume 0
        ((σ + t : ℝ≥0) : ℝ) →
      ∫ s in (0 : ℝ)..((σ + t : ℝ≥0) : ℝ), c / (u s.toNNReal - v s.toNNReal) =
        (∫ s in (0 : ℝ)..σ, c / (u s.toNNReal - v s.toNNReal)) +
          ∫ s in (0 : ℝ)..t, c / (shiftAt σ u (w σ) s.toNNReal - shiftAt σ v (w σ) s.toNNReal) := by
    intro c u v t hi'
    rw [integral_eq_add_shiftAt (G := fun s => c / (u s - v s)) hi']
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [shiftAt, sub_sub_sub_cancel_right]
  have hσσ : ((σ + 0 : ℝ≥0) : ℝ≥0∞) < τ := by rwa [add_zero]
  refine
    { w_zero := by rw [shiftAt_zero, sub_self]
      vL_zero := fun i => shiftAt_zero σ (vL i) (w σ)
      vR_zero := fun j => shiftAt_zero σ (vR j) (w σ)
      continuousOn_w := hcont _ h.continuousOn_w
      continuousOn_vL := fun i => hcont _ (h.continuousOn_vL i)
      continuousOn_vR := fun j => hcont _ (h.continuousOn_vR j)
      antitone_vL := fun {t} ht i j hij => by
        simp only [shiftAt]; linarith [h.antitone_vL (hlt ht) hij]
      vL_le_w := fun {t} ht i => by simp only [shiftAt]; linarith [h.vL_le_w (hlt ht) i]
      w_le_vR := fun {t} ht j => by simp only [shiftAt]; linarith [h.w_le_vR (hlt ht) j]
      monotone_vR := fun {t} ht i j hij => by
        simp only [shiftAt]; linarith [h.monotone_vR (hlt ht) hij]
      integrable_gapL := fun {t} ht i => hgap w (vL i) (h.integrable_gapL (hlt ht) i)
      integrable_gapR := fun {t} ht j => hgap w (vR j) (h.integrable_gapR (hlt ht) j)
      w_eq := fun {t} ht => ?_
      vL_eq := fun {t} ht i => ?_
      vR_eq := fun {t} ht j => ?_
      volume_collisionL := fun i => ?_
      volume_collisionR := fun j => ?_
      not_threshold := fun {t} ht => ?_ }
  · have e1 := h.w_eq (hlt ht)
    have e0 := h.w_eq (t := σ) hσ
    have eL : ∀ i, ∫ s in (0 : ℝ)..((σ + t : ℝ≥0) : ℝ), ρL i / (w s.toNNReal - vL i s.toNNReal) =
        _ := fun i => hint (ρL i) w (vL i) (by
          simpa only [div_eq_mul_inv] using (h.integrable_gapL (hlt ht) i).const_mul (ρL i))
    have eR : ∀ j, ∫ s in (0 : ℝ)..((σ + t : ℝ≥0) : ℝ), ρR j / (w s.toNNReal - vR j s.toNNReal) =
        _ := fun j => hint (ρR j) w (vR j) (by
          simpa only [div_eq_mul_inv] using (h.integrable_gapR (hlt ht) j).const_mul (ρR j))
    simp only [eL, eR, Finset.sum_add_distrib] at e1
    simp only [shiftAt] at e1 ⊢
    linear_combination e1 - e0
  · have e1 := h.vL_eq (hlt ht) i
    have e0 := h.vL_eq (t := σ) hσ i
    have hi : IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0
        ((σ + t : ℝ≥0) : ℝ) := by
      simpa only [two_div_sub_eq] using (h.integrable_gapL (hlt ht) i).const_mul (-2)
    rw [hint 2 (vL i) w hi] at e1
    simp only [shiftAt] at e1 ⊢
    linear_combination e1 - e0
  · have e1 := h.vR_eq (hlt ht) j
    have e0 := h.vR_eq (t := σ) hσ j
    have hi : IntervalIntegrable (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) volume 0
        ((σ + t : ℝ≥0) : ℝ) := by
      simpa only [two_div_sub_eq] using (h.integrable_gapR (hlt ht) j).const_mul (-2)
    rw [hint 2 (vR j) w hi] at e1
    simp only [shiftAt] at e1 ⊢
    linear_combination e1 - e0
  · have := volume_shift_eq_zero (σ := σ) (h.volume_collisionL i)
    refine measure_mono_null ?_ this
    rintro s ⟨hs0, hs, he⟩
    exact ⟨hs0, hs, by simpa only [shiftAt, sub_left_inj] using he⟩
  · have := volume_shift_eq_zero (σ := σ) (h.volume_collisionR j)
    refine measure_mono_null ?_ this
    rintro s ⟨hs0, hs, he⟩
    exact ⟨hs0, hs, by simpa only [shiftAt, sub_left_inj] using he⟩
  · have := h.not_threshold (hlt ht)
    rwa [← ForceWord.thresholdCondition_sub_iff ρL ρR _ (w σ)] at this

end IsSLEPathUpTo

end Sec2

open Sec2 Sec2.Assembly2

namespace IsIntegratedSLEPath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Restart of a solution of Definition 2.1** at a time `σ < ζ` (maximality included): the
restarted, recentred path is a solution of the word `(vL σ − w σ; vR σ − w σ)` with lifetime
`ζ − σ`, driven by `b (σ + ·) − b σ`. -/
theorem shift (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {σ : ℝ≥0}
    (hσ : (σ : ℝ≥0∞) < ζ) :
    IsIntegratedSLEPath a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR
      (shiftAt σ w (w σ)) (fun i => shiftAt σ (vL i) (w σ)) (fun j => shiftAt σ (vR j) (w σ))
      (shiftAt σ b (b σ)) (ζ - σ) := by
  have hu := (h.isSLEPathUpTo le_rfl).shift hσ
  have hfp := h.isForcePath
  refine ⟨hu.w_zero, hu.vL_zero, hu.vR_zero, hu.continuousOn_w, hu.continuousOn_vL,
    hu.continuousOn_vR, fun t ht => hu.antitone_vL ht, fun t ht => hu.vL_le_w ht,
    fun t ht => hu.w_le_vR ht, fun t ht => hu.monotone_vR ht, fun t ht => hu.integrable_gapL ht,
    fun t ht => hu.integrable_gapR ht, fun t ht => hu.w_eq ht, fun t ht => hu.vL_eq ht,
    fun t ht => hu.vR_eq ht, hu.volume_collisionL, hu.volume_collisionR,
    fun t ht => hu.not_threshold ht, fun h0 => ?_, fun T hT hTζ w₀ vL₀ vR₀ hlim => ?_⟩
  · exact absurd (tsub_eq_zero_iff_le.1 h0) (not_le.2 hσ)
  · have hζ : ((σ + T : ℝ≥0) : ℝ≥0∞) = ζ := by
      rw [ENNReal.coe_add, hTζ, add_tsub_cancel_of_le hσ.le]
    have hlim' : Tendsto (fun t => (w (σ + t), fun i => vL i (σ + t), fun j => vR j (σ + t)))
        (𝓝[<] T) (𝓝 (w₀ + w σ, fun i => vL₀ i + w σ, fun j => vR₀ j + w σ)) := by
      have hc : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
          (p.1 + w σ, fun i => p.2.1 i + w σ, fun j => p.2.2 j + w σ) := by fun_prop
      have := (hc.tendsto _).comp hlim
      refine this.congr fun t => ?_
      simp only [Function.comp_apply, shiftAt, sub_add_cancel]
    have hthr := hfp.threshold_of_tendsto (hT.trans_le le_add_self) hζ
      (tendsto_of_tendsto_shift hT hlim')
    rw [← ForceWord.thresholdCondition_sub_iff ρL ρR _ (w σ)] at hthr
    simpa only [add_sub_cancel_right] using hthr

end IsIntegratedSLEPath

end InteractingSLE
