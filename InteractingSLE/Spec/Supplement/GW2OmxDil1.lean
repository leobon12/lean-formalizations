/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3KernelRelTrace
import InteractingSLE.Spec.Supplement.GW4IdentHull
import InteractingSLE.Spec.Sec5.MarkovFlow
import InteractingSLE.Spec.Supplement.GW2OlmDil

/-!
# GW2's open lines: the relative map near its two normalization points

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation, item 1). The centred relative map `relMap U σ` of a
counterflow at `σ` fixes `0` and sends the tip to `∞`. Set-level forms, used with point families that need not be
traces (traces may touch `ℝ`):

* **`relMap_small_near_zero`**: small sets near `0` off the retained hull are mapped near `0`;
* **`relMap_continuation_far`**: the continuation `invHull U (σ + v) ∖ invHull U σ` is mapped outside any ball for
  small `v` (its forward image is the hull of the shifted driver at `v`, of small diameter);
* **`dilation_of_shrinking`**: two conformal charts with the same domain that map common families of nonempty sets
  near `0` and near `∞` differ by a dilation (`GW2Olm.exists_dilation_of_tendsto`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open Supp8.GB6 (relMap)
open Supp8.Q3Rel (invHull)

/-- **The relative map sends small sets near `0` near `0`.** -/
theorem relMap_small_near_zero {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {σ : ℝ} (hσ : 0 ≤ σ) {ε : ℝ}
    (hε : 0 < ε) : ∃ η > 0, ∀ w ∈ H \ invHull U σ, ‖w‖ < η → ‖relMap U σ w‖ < ε := by
  have h := Supp8.Q3Kernel.tendsto_relMap_zero hU hU0 hσ
  obtain ⟨η, hη, hball⟩ := Metric.tendsto_nhdsWithin_nhds.1 h ε hε
  refine ⟨η, hη, fun w hw hwη => ?_⟩
  have := hball hw (by simpa [dist_zero_right] using hwη)
  simpa [dist_zero_right] using this

/-- **The relative map sends the continuation of the counterflow far away.** -/
theorem relMap_continuation_far {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {σ : ℝ} (hσ : 0 ≤ σ) {M : ℝ}
    (hM : 0 < M) : ∃ δ > 0, ∀ v : ℝ, 0 < v → v ≤ δ → ∀ w ∈ invHull U (σ + v) \ invHull U σ,
      M < ‖relMap U σ w‖ := by
  set Us : ℝ → ℝ := fun r => U (σ + r) - U σ with hUsdef
  have hUs : Continuous Us := (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  have hUs0 : Us 0 = 0 := by simp [hUsdef]
  obtain ⟨δ, hδ, hball⟩ := GW4Ident.eventually_fwdHull_subset_closedBall hUs hUs0 (ε := 1 / (2 * M))
    (by positivity)
  refine ⟨δ, hδ, fun v hv hvδ w hw => ?_⟩
  obtain ⟨⟨x, hx, rfl⟩, hwσ⟩ := hw
  have hxσ : x ∉ fwdHull U σ := fun h => hwσ ⟨x, h, rfl⟩
  have hxH : x ∈ H := hx.1
  set y := fwdMap U σ x with hydef
  have hyH : y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ ⟨hxH, hxσ⟩
  have hinv : fwdMapInv U σ y = x := QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hσ ⟨hxH, hxσ⟩
  have hy : y ∈ fwdHull Us v := by
    by_contra hyK
    have hx' : x ∈ H \ fwdHull U (σ + v) := by
      rw [← Sec5.Markov.image_fwdMapInv_diff_fwdHull hU hU0 hσ hv.le]
      exact ⟨y, ⟨hyH, hyK⟩, hinv⟩
    exact hx'.2 hx
  have hyb : ‖y‖ ≤ 1 / (2 * M) := by
    have := hball v hv hvδ hy
    simpa [mem_closedBall, dist_zero_right] using this
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 fun h => by
    rw [h] at hyH
    have h0 : (0 : ℂ).im > 0 := hyH
    simp at h0
  have hrel : relMap U σ (-x⁻¹) = -y⁻¹ := by
    simp [relMap, hydef]
  rw [hrel, norm_neg, norm_inv]
  have h2 : 2 * M ≤ ‖y‖⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hy0]
    simpa [one_div] using hyb
  linarith

/-- **Two charts with the same domain mapping common families near `0` and near `∞` differ by a dilation.** -/
theorem dilation_of_shrinking {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal)
    (hdom : (c.dom : Set ℂ) = d.dom) {S₀ S₁ : ℕ → Set ℂ}
    (hS₀ : ∀ᶠ n in atTop, (S₀ n ∩ c.dom).Nonempty) (hS₁ : ∀ᶠ n in atTop, (S₁ n ∩ c.dom).Nonempty)
    (hc₀ : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ S₀ n ∩ c.dom, ‖c.1 z‖ < ε)
    (hd₀ : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ S₀ n ∩ c.dom, ‖d.1 z‖ < ε)
    (hc₁ : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ S₁ n ∩ c.dom, M < ‖c.1 z‖)
    (hd₁ : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ S₁ n ∩ c.dom, M < ‖d.1 z‖) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ (c.dom : Set ℂ), d.1 x = (lam : ℂ) * c.1 x := by
  classical
  set z₀ : ℕ → ℂ := fun n => if h : (S₀ n ∩ c.dom).Nonempty then h.some else 0 with hz₀def
  set z₁ : ℕ → ℂ := fun n => if h : (S₁ n ∩ c.dom).Nonempty then h.some else 0 with hz₁def
  have hz₀ : ∀ᶠ n in atTop, z₀ n ∈ S₀ n ∩ c.dom := hS₀.mono fun n h => by
    simp only [hz₀def, h, ↓reduceDIte]
    exact h.some_mem
  have hz₁ : ∀ᶠ n in atTop, z₁ n ∈ S₁ n ∩ c.dom := hS₁.mono fun n h => by
    simp only [hz₁def, h, ↓reduceDIte]
    exact h.some_mem
  refine GW2Olm.exists_dilation_of_tendsto hc hd hdom (l₀ := atTop) (l₁ := atTop)
    (hz₀.mono fun n h => h.2) (hz₁.mono fun n h => h.2) ?_ ?_ ?_ ?_
  · refine tendsto_zero_iff_norm_tendsto_zero.2 (Metric.tendsto_atTop.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hc₀ ε hε).and hz₀)
    exact ⟨N, fun n hn => by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using (hN n hn).1 (z₀ n) (hN n hn).2⟩
  · refine tendsto_zero_iff_norm_tendsto_zero.2 (Metric.tendsto_atTop.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hd₀ ε hε).and hz₀)
    exact ⟨N, fun n hn => by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using (hN n hn).1 (z₀ n) (hN n hn).2⟩
  · refine tendsto_atTop.2 fun M => ?_
    filter_upwards [hc₁ M, hz₁] with n hn hzn
    exact (hn (z₁ n) hzn).le
  · refine tendsto_atTop.2 fun M => ?_
    filter_upwards [hd₁ M, hz₁] with n hn hzn
    exact (hn (z₁ n) hzn).le

end InteractingSLE.Theorem14.GW2Omx
