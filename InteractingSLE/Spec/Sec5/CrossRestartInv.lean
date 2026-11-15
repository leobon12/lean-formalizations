/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartTrace

/-!
# The inverse restart chart

Packet PROVE-SEC5-G (item (ii)(c) of `planning/handoffs/PROVE-SEC5-F.md`, "What remains" 1). Lemma 5.7's proof
(specification p. 138) applies "a conformal transformation `ψ : 𝒮 \ η([0, σ]) → 𝒮` which fixes `±∞` and sends
`η(σ)` to `0`". In the restart chart of `CrossRestartChart.lean`,

  `Φ = m₂ ∘ (· − x₁) ∘ g_A ∘ M_q⁻¹`,  `m₂(w) = −w/(w − P)`,  `P = U_σ − x₁`,

the counterflow starts at `0`, the tip prime end is at `∞` and the strip end `+∞` is at `−1`. The inverse chart from
the restart chart to the exponential chart `E` is `g_A⁻¹ ∘ (· + x₁) ∘ m₂⁻¹`; since `m₂⁻¹(w) = Pw/(w + 1)` and
`g_A⁻¹(v) = f_σ⁻¹(v − U_σ)` (`f_σ = QuantumZipper.fwdMap U σ` the centred map), it is

  `ψ(w) = f_σ⁻¹(−P/(w + 1))`  on `ℍ`.

`MarkovOther.IsCounterflowChartContinuation` asks for an inverse chart `ψ : ℂ → ℂ` with three properties: `ψ` maps
`ℍ` and the real points of `(−1, Q]` off `∂_L𝒮 ∪ A`, and `ψ(f) → η(σ)` along every path `f` in `ℍ̄` tending to `∞`.
On `ℍ` the inverse chart above has the first and the third (the tip property of the flow-line trace,
`IsGeneratingTrace.tendsto_fwdMapInv_tip`). On `ℝ` the chart path of the restart only takes the value `0` (its start,
mapped to the counterflow start `E(z₀) = −1 − q`), so `restartInv` is extended to `ℝ` by `−1 − q` on a bounded set
containing `(−1, Q]` and by the tip far out; these real values lie on `∂_U𝒮 ∪ {E(z₀)}` and at the tip, as the
definition requires.

## Main results

* `restartInv`: the inverse restart chart;
* `restartInv_zero`, `restartInv_of_mem_H`;
* **`restartInv_notMem_of_mem_H`**, **`restartInv_ofReal_notMem`**, **`tendsto_restartInv`**: the three properties
  of the inverse chart in `IsCounterflowChartContinuation`;
* **`restartMap_mem_H`**, **`restartInv_restartMap`**: `Φ` maps the counterflow points that have not met the
  segment into `ℍ`, and `ψ ∘ Φ = M_q⁻¹` there (the physical point of the counterflow).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull

/-- **The inverse restart chart** (restart chart → chart `E`): `w ↦ f_σ⁻¹(−P/(w + 1))` on `ℍ` (with
`P = U_σ − x₁`), the counterflow start `E(z₀) = −1 − q` at the real points of norm `≤ |Q| + 1`, and the tip `z`
at the other real points. -/
def restartInv (q P Q : ℝ) (U : ℝ → ℝ) (σ : ℝ) (z w : ℂ) : ℂ :=
  if 0 < w.im then QuantumZipper.fwdMapInv U σ (realMobius 0 (-P) 1 1 w)
  else if ‖w‖ ≤ |Q| + 1 then ((-1 - q : ℝ) : ℂ) else z

variable {q P Q : ℝ} {U : ℝ → ℝ} {σ : ℝ} {z : ℂ}

theorem restartInv_of_mem_H {w : ℂ} (hw : w ∈ H) :
    restartInv q P Q U σ z w = QuantumZipper.fwdMapInv U σ (realMobius 0 (-P) 1 1 w) :=
  ite_eq_left hw

/-- The inverse chart sends the start `0` of the restart chart to the counterflow start `E(z₀) = −1 − q`. -/
theorem restartInv_zero : restartInv q P Q U σ z 0 = ((-1 - q : ℝ) : ℂ) := by
  have h1 : ¬ (0 < (0 : ℂ).im) := by simp
  have h2 : ‖(0 : ℂ)‖ ≤ |Q| + 1 := by rw [norm_zero]; positivity
  rw [restartInv, ite_eq_right h1, ite_eq_left h2]

/-- `w ↦ −P/(w + 1)` maps `ℍ` into `ℍ` for `P > 0`. -/
theorem realMobius_neg_mem_H (hP : 0 < P) {w : ℂ} (hw : w ∈ H) : realMobius 0 (-P) 1 1 w ∈ H :=
  QuantumZipper.CA.realMobius_mem_H (by linarith) hw

/-- **First property of the inverse chart**: points of `ℍ` go to the remaining domain `ℍ \ A`, off `∂_L𝒮`. -/
theorem restartInv_notMem_of_mem_H (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) (hP : 0 < P)
    {A : Set ℂ} (hA : A ∩ H ⊆ QuantumZipper.fwdHull U σ) {w : ℂ} (hw : w ∈ H) :
    restartInv q P Q U σ z w ∉ Sec4.lowerLineH ∪ A := by
  rw [restartInv_of_mem_H hw]
  have hmem := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hσ (realMobius_neg_mem_H hP hw)
  rintro (h | h)
  · exact Set.disjoint_left.1 Sec4.disjoint_H_lowerLineH hmem.1 h
  · exact hmem.2 (hA ⟨h, hmem.1⟩)

/-- **Second property of the inverse chart**: the real points of `(−1, Q]` go to `E(z₀) = −1 − q`, which lies
neither on `∂_L𝒮 = (−1, ∞)` nor on the segment `A` (a set meeting `ℝ` at most at its seed). -/
theorem restartInv_ofReal_notMem (hq : 0 < q) {A : Set ℂ} (hA : ((-1 - q : ℝ) : ℂ) ∉ A) {x : ℝ}
    (hx : -1 < x) (hxQ : x ≤ Q) : restartInv q P Q U σ z x ∉ Sec4.lowerLineH ∪ A := by
  have h1 : ¬ (0 < (x : ℂ).im) := by simp
  have h2 : ‖(x : ℂ)‖ ≤ |Q| + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [abs_nonneg Q]
    · linarith [le_abs_self Q]
  rw [restartInv, ite_eq_right h1, ite_eq_left h2]
  rintro (⟨y, hy, hyx⟩ | h)
  · have : y = -1 - q := by exact_mod_cast hyx
    rw [mem_Ioi] at hy
    linarith
  · exact hA h

/-- `−P/(w + 1) → 0` as `w → ∞`. -/
theorem tendsto_realMobius_neg_cobounded (P : ℝ) :
    Tendsto (realMobius 0 (-P) 1 1) (Bornology.cobounded ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun w : ℂ => w + 1) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) :=
    tendsto_add_const_cobounded 1
  have h2 := (tendsto_inv₀_cobounded.comp h1).const_mul (-(P : ℂ))
  rw [mul_zero] at h2
  refine h2.congr fun w => ?_
  simp [realMobius, div_eq_mul_inv]

/-- **Third property of the inverse chart**: along every path `f` in `ℍ̄` tending to `∞`, `ψ(f) → z`, the tip,
provided `f_σ⁻¹(v) → z` as `v → 0` in `ℍ` (the tip property of the flow-line trace). -/
theorem tendsto_restartInv (hP : 0 < P)
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 z)) (f : ℝ≥0 → ℂ)
    (_hf : ∀ t, 0 ≤ (f t).im) (hfi : Tendsto (fun t => ‖f t‖) atTop atTop) :
    Tendsto (fun t => restartInv q P Q U σ z (f t)) atTop (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.mem_nhdsWithin_iff.1 (htip (Metric.ball_mem_nhds z hε))
  have hcob : Tendsto f atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]; exact hfi
  have hsmall : ∀ᶠ t in atTop, realMobius 0 (-P) 1 1 (f t) ∈ ball (0 : ℂ) δ :=
    ((tendsto_realMobius_neg_cobounded P).comp hcob) (Metric.ball_mem_nhds 0 hδ)
  have hbig : ∀ᶠ t in atTop, |Q| + 1 < ‖f t‖ := hfi.eventually_gt_atTop _
  filter_upwards [hsmall, hbig] with t ht hbt
  by_cases him : 0 < (f t).im
  · rw [restartInv_of_mem_H him]
    exact hδε ⟨ht, realMobius_neg_mem_H hP him⟩
  · rw [restartInv, ite_eq_right him, ite_eq_right (not_le.2 hbt), dist_self]
    exact hε

/-- `Φ` maps a point whose `E`-image avoids the segment hull into `ℍ`. -/
theorem restartMap_mem_H (hU : Continuous U) (hσ : 0 ≤ σ) {x₁ : ℝ} (hx₁ : x₁ < U σ) {w : ℂ}
    (hw : realMobius 0 (-(1 + q)) 1 1 w ∈ H \ QuantumZipper.fwdHull U σ) :
    restartMap q U σ x₁ w ∈ H := by
  have hf := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ hw
  refine QuantumZipper.CA.realMobius_mem_H (by linarith) ?_
  have : gmap U σ (realMobius 0 (-(1 + q)) 1 1 w) - x₁ =
      QuantumZipper.fwdMap U σ (realMobius 0 (-(1 + q)) 1 1 w) + ((U σ - x₁ : ℝ) : ℂ) := by
    rw [gmap]; push_cast; ring
  rw [this]
  show 0 < (QuantumZipper.fwdMap U σ _ + _ : ℂ).im
  rw [add_im, ofReal_im, add_zero]
  exact hf

/-- **`ψ ∘ Φ = M_q⁻¹`** on the counterflow points whose `E`-image avoids the segment hull: the inverse chart
returns the physical point. -/
theorem restartInv_restartMap (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {x₁ : ℝ}
    (hP : P = U σ - x₁) (hx₁ : x₁ < U σ) {w : ℂ}
    (hw : realMobius 0 (-(1 + q)) 1 1 w ∈ H \ QuantumZipper.fwdHull U σ) :
    restartInv q P Q U σ z (restartMap q U σ x₁ w) = realMobius 0 (-(1 + q)) 1 1 w := by
  rw [restartInv_of_mem_H (restartMap_mem_H hU hσ hx₁ hw)]
  set y := realMobius 0 (-(1 + q)) 1 1 w with hy
  set v := QuantumZipper.fwdMap U σ y with hv
  have hvH : v ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ hw
  have hPpos : (P : ℂ) ≠ 0 := by rw [hP]; exact_mod_cast (sub_pos.2 hx₁).ne'
  have hv0 : v ≠ 0 := fun h => by
    have hvi : 0 < v.im := hvH
    rw [h] at hvi; simp at hvi
  have hm : restartMap q U σ x₁ w = -(v + P) / v := by
    have h1 : gmap U σ y - x₁ = v + P := by rw [gmap, ← hv, hP]; push_cast; ring
    rw [restartMap, ← hy, h1, realMobius]
    have h2 : (((1 : ℝ) : ℂ) * (v + P) + ((-(U σ - x₁) : ℝ) : ℂ)) = v := by rw [hP]; push_cast; ring
    rw [h2]
    push_cast
    ring
  have hkey : realMobius 0 (-P) 1 1 (restartMap q U σ x₁ w) = v := by
    rw [hm, realMobius]
    push_cast
    have hden : (1 : ℂ) * (-(v + P) / v) + 1 = -P / v := by field_simp; ring
    rw [hden, zero_mul, zero_add, div_div_eq_mul_div, mul_div_assoc,
      mul_div_cancel₀ v (neg_ne_zero.2 hPpos)]
  rw [hkey]
  exact QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hσ hw

end CrossRestart

end Sec5

end InteractingSLE
