/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6HullIdRule

/-!
# The lossy part of the near facts: caps before the exit are rare (VNearImgL assembly, generic)

Packet PROVE-GW2-BUF (round 11). The near variable `m` reads instance `m` of the version family, capped at `V m`.
Its near stop is the exit rule on that capped driver. The lossy near facts (R114) allow a loss set `N_m`: there the
cap comes no later than the exit. This file proves the two generic steps.

* **`eventually_pathRule_lt_cap`** (pathwise): suppose a path rule `ρ` (e.g. the near exit rule,
  `GW2Bj.isPathRule_exitRule`) fires on the uncapped driver `W` strictly before the life `L`. Suppose the caps
  `T m` eventually pass every time before `L`, and the capped drivers agree with `W` before their caps. Then
  eventually the rule fires on the capped driver at the same time, strictly before its cap.
* **`tendsto_measure_of_ae_eventually_notMem`**, **`eventually_measure_le`**: if almost every sample is eventually
  outside the measurable sets `N m`, then `μ (N m) → 0`, so `μ (N m) ≤ ε` eventually, for every `ε > 0`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Supp8.GB6.HullId Exist.StagedLaw

/-- A path rule is unchanged by a path agreeing up to a time past the rule. -/
theorem pathRule_eq_of_agree {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) {r : RecData}
    {w w' : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hagree : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T → w' u = w u) (hlt : ρ (r, w) < T) :
    ρ (r, w') = ρ (r, w) :=
  hρ r w w' fun u hu => (hagree u (lt_of_le_of_lt hu hlt)).symm

/-- **A causal stop on capped versions eventually equals the stop on the uncapped driver, before the cap.** -/
theorem eventually_pathRule_lt_cap {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) {r : RecData}
    {W : ℝ≥0 → ℝ} {w : ℕ → ℝ≥0 → ℝ} {T : ℕ → ℝ≥0∞} {L : ℝ≥0∞} (hlt : ρ (r, W) < L)
    (hT : ∀ x < L, ∀ᶠ m in atTop, x < T m) (hagree : ∀ (m : ℕ) (u : ℝ≥0), (u : ℝ≥0∞) < T m → w m u = W u) :
    ∀ᶠ m in atTop, ρ (r, w m) = ρ (r, W) ∧ ρ (r, w m) < T m := by
  filter_upwards [hT _ hlt] with m hm
  have heq := pathRule_eq_of_agree hρ (hagree m) hm
  exact ⟨heq, heq ▸ hm⟩

/-- **Sets eventually avoided almost surely have vanishing measure.** -/
theorem tendsto_measure_of_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {N : ℕ → Set Ω} (hN : ∀ m, MeasurableSet (N m))
    (hev : ∀ᵐ ξ ∂μ, ∀ᶠ m in atTop, ξ ∉ N m) : Tendsto (fun m => μ (N m)) atTop (𝓝 0) := by
  have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := μ) atTop MeasurableSet.empty hN
    (by
      filter_upwards [hev] with ξ hξ
      filter_upwards [hξ] with m hm
      exact iff_of_false hm (notMem_empty ξ))
  rwa [measure_empty] at h

/-- **Eventually the loss set has measure at most `ε`.** -/
theorem eventually_measure_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {N : ℕ → Set Ω} (hN : ∀ m, MeasurableSet (N m)) (hev : ∀ᵐ ξ ∂μ, ∀ᶠ m in atTop, ξ ∉ N m) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∀ᶠ m in atTop, μ (N m) ≤ ε :=
  (tendsto_order.1 (tendsto_measure_of_ae_eventually_notMem hN hev)).2 ε hε |>.mono fun _ h => h.le

end InteractingSLE.Theorem14.GW2Bh
