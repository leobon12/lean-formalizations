/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfSide
import InteractingSLE.Spec.Sec5.TimeDensity

/-!
# Lemma 4.7's direction, item (B): the transition map sends the new curve's tip to the image tip

Packet PROVE-CFRESTART2. In the reversed-slit chart of `CrossRestartKernelRev` (new curve: driver `Wα` at time `t`,
any continuous Loewner chain, **not simple**; obstacle `R(K^{Wβ}_s)`; image chain `W'` with
`K^{W′}_T = Ψ(K^{Wα}_t)`, `Ψ = revChart Wβ s`), the inverse transition map `Θ = f_t ∘ Ψ⁻¹ ∘ F′_T` has the cluster value
`0` (the new curve's tip in its own chart) at one image-chart point at most (`exists_eq_of_tendsto_imgTheta_zero`).
This file shows that this point is the **image tip `0`**, from the growth of both chains just after `t` (Lawler's
"the image of the driving point is the driving point of the image", read through hull increments):

* `exists_mem_H_norm_lt_imgTheta`: for every `ε > 0` there is `y ∈ ℍ` with `‖y‖ < ε` and `‖Θ y‖ < ε` — a point of the
  image chain's increment `f′_T(K′_{τ(r)} ∖ K′_T)` (small by `exists_fwdHull_subset_ball` for the restarted image
  driver) whose `Θ`-image is a point of the new curve's increment `f_t(K_r ∖ K_t)` (small likewise;
  `QuantumZipper.fwdHull_add_diff` identifies both increments with restarted hulls);
* **`eq_zero_of_tendsto_imgTheta_zero`**: if `Θ → 0` along an ultrafilter at `y₀`, then `y₀ = 0`.

No information on the fibre of the image hull's boundary map over the image tip is used (R41).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real

open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **Small points of the image increment with small `Θ`-images.** Suppose the image chain follows the new curve on
`[t, t + ε₀]` through a clock `τ` continuous from the right at `t` with `τ(t) = T` (`K^{W′}_{τ(r)} = Ψ(K^{Wα}_r)`, the
new hulls avoiding the obstacle). Then for every `ε > 0` there is `y ∈ ℍ` with `‖y‖ < ε` and `‖Θ y‖ < ε`. -/
theorem exists_mem_H_norm_lt_imgTheta (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    {τ : ℝ → ℝ} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hτc : ContinuousWithinAt τ (Ici t) t) (hτt : τ t = T)
    (hτle : ∀ r ∈ Icc t (t + ε₀), T ≤ τ r)
    (hdisjr : ∀ r ∈ Icc t (t + ε₀), Disjoint (fwdHull Wα r) (negInv '' fwdHull Wβ s))
    (hgrow : ∀ r ∈ Icc t (t + ε₀), fwdHull W' (τ r) = revChart Wβ s '' fwdHull Wα r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ H, ‖y‖ < ε ∧ ‖imgTheta Wα t Wβ s W' T y‖ < ε := by
  -- the restarted drivers
  set A : ℝ → ℝ := fun r => Wα (t + r) - Wα t with hAdef
  set B : ℝ → ℝ := fun r => W' (T + r) - W' T with hBdef
  have hAc : Continuous A := by fun_prop
  have hBc : Continuous B := by fun_prop
  have hA0 : A 0 = 0 := by simp [hAdef]
  have hB0 : B 0 = 0 := by simp [hBdef]
  obtain ⟨sA, hsA, hsAb⟩ := Sec5.exists_fwdHull_subset_ball hAc hA0 hε
  obtain ⟨sB, hsB, hsBb⟩ := Sec5.exists_fwdHull_subset_ball hBc hB0 hε
  -- the clock moves by less than `sB` just after `t`
  have hτc' : ∀ᶠ r in 𝓝[Ici t] t, τ r - T < sB := by
    have h : Tendsto (fun r => τ r - T) (𝓝[Ici t] t) (𝓝 (τ t - T)) :=
      hτc.tendsto.sub tendsto_const_nhds
    rw [hτt, sub_self] at h
    exact h.eventually (Iio_mem_nhds hsB)
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.1 hτc'
  set u : ℝ := min (min sA ε₀) (δ / 2) with hu
  have hu0 : 0 < u := lt_min (lt_min hsA hε₀) (by positivity)
  have hur : t + u ∈ Icc t (t + ε₀) :=
    ⟨by linarith, by linarith [min_le_left (min sA ε₀) (δ / 2), min_le_right sA ε₀]⟩
  have huA : u ≤ sA := (min_le_left _ _).trans (min_le_left _ _)
  have hτu : τ (t + u) - T < sB := by
    refine hδb ⟨?_, show t ≤ t + u by linarith⟩
    rw [mem_ball, Real.dist_eq, show t + u - t = u by ring, abs_of_pos hu0]
    linarith [min_le_right (min sA ε₀) (δ / 2)]
  -- a point of the new curve's increment
  obtain ⟨ξ, hξ⟩ := QuantumZipper.RS.fwdHull_nonempty_of_pos hAc hA0 hu0
  have hξH : ξ ∈ H := (QuantumZipper.fwdHull_mono (W := A)).2 u hξ
  have hξs : ‖ξ‖ < ε := hsAb ξ ((QuantumZipper.fwdHull_mono (W := A)).1 huA hξ)
  set z := fwdMapInv Wα t ξ with hz
  -- `z ∈ K_{t+u} ∖ K_t` with `f_t z = ξ`
  have hzK : z ∈ H \ fwdHull Wα t := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWα hWα0 ht hξH
  have hfz : fwdMap Wα t z = ξ := QuantumZipper.RS.fwdMap_fwdMapInv hWα hWα0 ht hξH
  have hzr : z ∈ fwdHull Wα (t + u) := by
    have h := QuantumZipper.fwdHull_add_diff hWα ht hu0.le
    have : z ∈ fwdHull Wα (t + u) \ fwdHull Wα t := by
      rw [h]
      exact ⟨hzK, by rw [hfz]; exact hξ⟩
    exact this.1
  have ht0 : t ∈ Icc t (t + ε₀) := ⟨le_rfl, by linarith⟩
  have hzG : z ∈ H \ negInv '' fwdHull Wβ s :=
    ⟨hzK.1, fun h => Set.disjoint_left.1 (hdisjr (t + u) hur) hzr h⟩
  -- its image in the image chart
  set w := revChart Wβ s z with hw
  have hwH : w ∈ H := revChart_mem_H hWβ hs hzG
  have hwT : w ∉ fwdHull W' T := by
    intro hwK
    rw [← hτt, hgrow t ht0] at hwK
    obtain ⟨k, hk, hkw⟩ := hwK
    have hkG : k ∈ H \ negInv '' fwdHull Wβ s :=
      ⟨(QuantumZipper.fwdHull_mono (W := Wα)).2 t hk, fun h => Set.disjoint_left.1 (hdisjr t ht0) hk h⟩
    have hkz : k = z := by
      have h1 := revChartInv_revChart hWβ hWβ0 hs hkG
      have h2 := revChartInv_revChart hWβ hWβ0 hs hzG
      rw [hkw] at h1
      rw [← h1, ← h2]
    exact hzK.2 (hkz ▸ hk)
  have hwr : w ∈ fwdHull W' (T + (τ (t + u) - T)) := by
    rw [add_sub_cancel, hgrow (t + u) hur]
    exact ⟨z, hzr, rfl⟩
  have hσ0 : 0 ≤ τ (t + u) - T := sub_nonneg.2 (hτle _ hur)
  have hy : fwdMap W' T w ∈ fwdHull B (τ (t + u) - T) := by
    have h := QuantumZipper.fwdHull_add_diff hW' hT hσ0
    have : w ∈ fwdHull W' (T + (τ (t + u) - T)) \ fwdHull W' T := ⟨hwr, hwT⟩
    rw [h] at this
    exact this.2
  have hyB : fwdMap W' T w ∈ fwdHull B sB := (QuantumZipper.fwdHull_mono (W := B)).1 hτu.le hy
  refine ⟨fwdMap W' T w, (QuantumZipper.fwdHull_mono (W := B)).2 _ hy, hsBb _ hyB, ?_⟩
  have hΘ : imgTheta Wα t Wβ s W' T (fwdMap W' T w) = ξ := by
    rw [imgTheta, QuantumZipper.RS.fwdMapInv_fwdMap hW' hW'0 hT ⟨hwH, hwT⟩, hw,
      revChartInv_revChart hWβ hWβ0 hs hzG, hfz]
  rw [hΘ]
  exact hξs

/-- **The cluster value `0` of `Θ` occurs only at the image tip `0`.** In the setting of
`exists_mem_H_norm_lt_imgTheta` (the image chain follows the new curve for a while after `t`), with the hull
hypotheses of `exists_eq_of_tendsto_imgTheta_zero`: if `Θ → 0` along an ultrafilter at `y₀`, then `y₀ = 0`. -/
theorem eq_zero_of_tendsto_imgTheta_zero (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    {τ : ℝ → ℝ} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hτc : ContinuousWithinAt τ (Ici t) t) (hτt : τ t = T)
    (hτle : ∀ r ∈ Icc t (t + ε₀), T ≤ τ r)
    (hdisjr : ∀ r ∈ Icc t (t + ε₀), Disjoint (fwdHull Wα r) (negInv '' fwdHull Wβ s))
    (hgrow : ∀ r ∈ Icc t (t + ε₀), fwdHull W' (τ r) = revChart Wβ s '' fwdHull Wα r)
    {y₀ : ℂ} {U : Ultrafilter ℂ} (hU : (U : Filter ℂ) ≤ 𝓝[H] y₀)
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 0)) : y₀ = 0 := by
  have ht0 : t ∈ Icc t (t + ε₀) := ⟨le_rfl, by linarith⟩
  have hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t := by
    rw [← hτt]
    exact hgrow t ht0
  obtain ⟨y₁, hy₁⟩ := exists_eq_of_tendsto_imgTheta_zero hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT (hdisjr t ht0)
    hdis hK'
  -- a sequence at `0` along which `Θ → 0`
  have hseq : ∀ n : ℕ, ∃ y ∈ H, ‖y‖ < 1 / ((n : ℝ) + 1) ∧
      ‖imgTheta Wα t Wβ s W' T y‖ < 1 / ((n : ℝ) + 1) := fun n =>
    exists_mem_H_norm_lt_imgTheta hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hε₀ hτc hτt hτle hdisjr hgrow
      (by positivity)
  choose y hyH hy hΘy using hseq
  have hlim0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hyt : Tendsto y atTop (𝓝[H] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨squeeze_zero_norm (fun n => (hy n).le) hlim0, Eventually.of_forall hyH⟩
  have hΘt : Tendsto (fun n => imgTheta Wα t Wβ s W' T (y n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hΘy n).le) hlim0
  have : (Filter.map y atTop).NeBot := Filter.map_neBot
  set V := Ultrafilter.of (Filter.map y atTop) with hV
  have hVF : (V : Filter ℂ) ≤ Filter.map y atTop := Ultrafilter.of_le _
  have hΘF : Tendsto (imgTheta Wα t Wβ s W' T) (Filter.map y atTop) (𝓝 0) := tendsto_map'_iff.2 hΘt
  have h0 := hy₁ 0 V (hVF.trans hyt) (hΘF.mono_left hVF)
  rw [hy₁ y₀ U hU hΘ, ← h0]

end InteractingSLE.Sec5.CrossRestart
