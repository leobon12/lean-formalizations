/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgRule
import InteractingSLE.Spec.Supplement.RelSafeCore

/-!
# GW2's stage identity: reading the relative path at RANDOM relative times

Packet PROVE-GW2-RELDET, ruling R106. K2's lines assembly at a stage needs the stage's canonical relative filtration,
traced on `{q ≤ a_n(t)}`, to lie in the physical filtration at `T_n + t`. GB6 proves this at deterministic relative
levels (`RelSafeCore.measurableSet_le_inter_of_lt`, `measurableSet_inter_stop_le`). At a stage the levels are
`S + u` with a RANDOM start `S` (the relative clock at `T_n`). This file gives the two generic random-level readouts,
evaluating the readable process at random times through the causal jointly measurable `GW2Rd.evalDn`:

* **`measurableSet_inter_drv_rand`**: if `R` (continuous) agrees almost surely with a process `Y` with `m`-measurable
  values on `[0, c]`, and `τ ≤ c` on `L ∈ m`, then `L ∩ {R τ ∈ B} ∈ m` (`m ⊇ 𝒩_P`);
* **`measurableSet_inter_stop_le_rand`**: if `V = ρ(rec, R)` for a measurable path rule `ρ`, `rec` is `m`-measurable
  and `R = Y` almost surely on `L` up to `min(V, y)`, then `L ∩ {V ≤ y} ∈ m`, for a random `m`-measurable level `y`.

Generic measure theory; no SLE content.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8.RelSafe

variable {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Causal evaluation at a random time of a process with `m`-measurable values is `m`-measurable. -/
theorem measurable_evalDn_of {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u)) {τ : Ω → ℝ≥0}
    (hτ : Measurable[m] τ) : Measurable[m] fun ω => evalDn (fun u => Y u ω) (τ ω) :=
  @measurable_evalDn Ω m (fun ω u => Y u ω) hY τ hτ

/-- **The relative driver at a random time is readable** where the time is below the clock. -/
theorem measurableSet_inter_drv_rand (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {R : ℝ≥0 → Ω → ℝ}
    (hRm : ∀ u, Measurable (R u)) (hRc : ∀ ω, Continuous fun u => R u ω) {Y : ℝ≥0 → Ω → ℝ}
    (hY : ∀ u, Measurable[m] (Y u)) {τ : Ω → ℝ≥0} (hτ : Measurable[m] τ) {L : Set Ω} (hL : MeasurableSet[m] L)
    (hRY : ∀ᵐ ω ∂P, ω ∈ L → ∀ u : ℝ≥0, u ≤ τ ω → R u ω = Y u ω) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[m] (L ∩ {ω | R (τ ω) ω ∈ B}) := by
  have hj : Measurable fun p : ℝ≥0 × Ω => R p.1 p.2 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun t ω => R t ω) hRc hRm
  have hRτ : Measurable fun ω => R (τ ω) ω := hj.comp ((hτ.mono hm le_rfl).prodMk measurable_id)
  have hg := measurable_evalDn_of hY hτ
  refine measurableSet_of_ae_eq hm hnull ((hm _ hL).inter (hRτ hB)) (hL.inter (hg hB)) ?_
  filter_upwards [hRY] with ω hω
  by_cases hωL : ω ∈ L
  · have e : evalDn (fun u => Y u ω) (τ ω) = R (τ ω) ω := by
      rw [← evalDn_eq (hRc ω) (τ ω)]
      exact evalDn_congr fun u hu => (hω hωL u hu).symm
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hωL, true_and, e]
  · simp only [mem_inter_iff, hωL, false_and]

/-- **Stops given by path rules are readable at a random level** (`measurableSet_inter_stop_le` with the level `y`
random and `m`-measurable). -/
theorem measurableSet_inter_stop_le_rand (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {ε : Type*}
    [MeasurableSpace ε] {rec : Ω → ε} (hrec : Measurable[m] rec) {ρ : ε × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ)
    (hρ : ∀ (r : ε) (w w' : ℝ≥0 → ℝ), (∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (r, w) → w v = w' v) → ρ (r, w') = ρ (r, w))
    {R : ℝ≥0 → Ω → ℝ} (hRc : ∀ ω, Continuous fun u => R u ω) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun v => R v ω)) {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u))
    {L : Set Ω} (hL : MeasurableSet[m] L) {y : Ω → ℝ≥0} (hy : Measurable[m] y)
    (hRY : ∀ᵐ ω ∂P, ω ∈ L → ∀ v : ℝ≥0, v ≤ y ω → (v : ℝ≥0∞) ≤ V ω → R v ω = Y v ω) :
    MeasurableSet[m] (L ∩ {ω | V ω ≤ y ω}) := by
  -- the readable path frozen at the random level
  set F : Ω → ℝ≥0 → ℝ := fun ω v => evalDn (fun u => Y u ω) (min v (y ω)) with hFdef
  have hFm : Measurable[m] F :=
    @measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) m _ _ |>.2 fun v =>
      measurable_evalDn_of hY ((measurable_const.min hy))
  have hS : MeasurableSet[m] (L ∩ {ω | ρ (rec ω, F ω) ≤ y ω}) :=
    hL.inter (measurableSet_le (hρm.comp (hrec.prodMk hFm))
      (measurable_coe_nnreal_ennreal.comp hy))
  have hVm' : MeasurableSet (L ∩ {ω | V ω ≤ y ω}) :=
    (hm _ hL).inter (measurableSet_le hVm (measurable_coe_nnreal_ennreal.comp (hy.mono hm le_rfl)))
  refine measurableSet_of_ae_eq hm hnull hVm' hS ?_
  filter_upwards [hRY, hVρ] with ω hω hV
  by_cases hωL : ω ∈ L
  · -- on `L`: the frozen readable path is the frozen relative path up to `min (V, y)`
    have hFR : ∀ v : ℝ≥0, (min v (y ω) : ℝ≥0∞) ≤ V ω → F ω v = R (min v (y ω)) ω := fun v hv => by
      simp only [hFdef]
      rw [← evalDn_eq (hRc ω) (min v (y ω))]
      refine evalDn_congr fun u hu => (hω hωL u (hu.trans (min_le_right _ _)) ?_).symm
      exact (ENNReal.coe_le_coe.2 hu).trans hv
    have key : V ω ≤ y ω ↔ ρ (rec ω, F ω) ≤ y ω := by
      constructor
      · intro hVy
        -- `F` and `R` agree up to `V`
        have hag : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (rec ω, fun u => R u ω) → R v ω = F ω v := fun v hv => by
          rw [← hV] at hv
          have hvy : v ≤ y ω := ENNReal.coe_le_coe.1 (hv.trans hVy)
          rw [hFR v ((min_le_left _ _).trans hv), min_eq_left hvy]
        rw [hρ (rec ω) (fun u => R u ω) (F ω) hag, ← hV]
        exact hVy
      · intro hρy
        by_contra hVy
        have hyV : (y ω : ℝ≥0∞) < V ω := lt_of_not_ge hVy
        have hag : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (rec ω, F ω) → F ω v = R v ω := fun v hv => by
          have hvy : v ≤ y ω := ENNReal.coe_le_coe.1 (hv.trans hρy)
          rw [hFR v ((min_le_right _ _).trans hyV.le), min_eq_left hvy]
        have h1 := hρ (rec ω) (F ω) (fun u => R u ω) hag
        rw [← hV] at h1
        exact hVy (h1 ▸ hρy)
    simp only [mem_inter_iff, mem_ofPred_eq, hωL, true_and]
    exact propext key
  · simp only [mem_inter_iff, hωL, false_and]

end InteractingSLE.Theorem14.GW2Rd
