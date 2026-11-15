/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgRule

/-!
# GW2's stage identity: a GB6 version restricted to a stage

Packet PROVE-GW2-RELDET, ruling R106. Given an announced R-form version `(R, V)` of the WHOLE relative exploration
(a measurable continuous relative driver from `0`, its stop `V = ρ (rec, R)` for a measurable path rule `ρ`, announced
by measurable finite path rules `ρs n`), and a stage record `x` with measurable decoders `σ` (its counterflow record),
`A` (the relative start `a_n`) and `pre` (a continuous relative prefix agreeing with `R` up to `a_n`), this file
produces EXACTLY the version inputs of GB6's engine at the stage (`GW2Rd.ae_isStopDrvMatch_rec`) for the record `x`:

* the stage driver `stgDrv R (A x)` is measurable, continuous and starts at `0`;
* the stage stop `V − A x` is measurable, positive where the stage starts before the stop;
* `V − A x = stageRule ρ σ A pre (x, stgDrv R (A x))` (a measurable path rule);
* the stage rules `stageRule (ρs n) σ A pre` are finite, monotone, below the stage stop and exhaust it.

**`stgVersion_inputs`**. Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6.HullId

/-- **The engine's version inputs at a stage, from an announced version of the whole relative exploration.** -/
theorem stgVersion_inputs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {R : ℝ≥0 → Ω → ℝ}
    (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    {rec x : Ω → RecData} (hx : Measurable x) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω)) {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρsfin : ∀ n y, ρs n y ≠ ⊤) (hρsmono : ∀ y, Monotone fun n => ρs n y) {G : Set Ω}
    (hann : ∀ᵐ ω ∂P, ω ∈ G → (∀ n, ρs n (rec ω, fun u => R u ω) < V ω) ∧
      ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω)
    {σ : RecData → RecData} {A : RecData → ℝ≥0} (hA : Measurable A) {pre : RecData → ℝ≥0 → ℝ}
    (hprec : ∀ r, Continuous (pre r))
    (hdec : ∀ᵐ ω ∂P, σ (x ω) = rec ω ∧ ∀ t ≤ A (x ω), pre (x ω) t = R t ω)
    (hstart : ∀ᵐ ω ∂P, ω ∈ G → (A (x ω) : ℝ≥0∞) < V ω) :
    (∀ t, Measurable fun ω => stgDrv (fun u => R u ω) (A (x ω)) t) ∧
    (∀ ω, Continuous fun t => stgDrv (fun u => R u ω) (A (x ω)) t) ∧
    (∀ ω, stgDrv (fun u => R u ω) (A (x ω)) 0 = 0) ∧
    Measurable (fun ω => V ω - A (x ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ G → 0 < V ω - A (x ω)) ∧
    (∀ᵐ ω ∂P, V ω - A (x ω) = stageRule ρ σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t)) ∧
    (∀ n y, stageRule (ρs n) σ A pre y ≠ ⊤) ∧ (∀ y, Monotone fun n => stageRule (ρs n) σ A pre y) ∧
    (∀ᵐ ω ∂P, ω ∈ G → ∀ n,
      stageRule (ρs n) σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t) < V ω - A (x ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ G →
      ⨆ n, stageRule (ρs n) σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t) = V ω - A (x ω)) := by
  have hAm : Measurable fun ω => A (x ω) := hA.comp hx
  -- the stage rules at (stage record, stage path) are the whole rules minus the start
  have hstg : ∀ᵐ ω ∂P, ∀ (ρ' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞),
      stageRule ρ' σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t) =
        ρ' (rec ω, fun u => R u ω) - A (x ω) := by
    filter_upwards [hdec] with ω hω ρ'
    exact stageRule_stgDrv (hRc ω) (hprec _) hω.1 hω.2
  refine ⟨fun t => measurable_stgDrv hRm hRc hAm t, fun ω => continuous_stgDrv (hRc ω) _,
    fun ω => stgDrv_zero _ _, hVm.sub (measurable_coe_nnreal_ennreal.comp hAm), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hstart] with ω hω hG using tsub_pos_of_lt (hω hG)
  · filter_upwards [hstg, hVρ] with ω hω hV
    rw [hω ρ, hV]
  · intro n y
    exact ne_top_of_le_ne_top (hρsfin n _) tsub_le_self
  · intro y n m hnm
    exact tsub_le_tsub_right (hρsmono _ hnm) _
  · filter_upwards [hstg, hann, hstart] with ω hω ha hs hG n
    rw [hω]
    rcases le_or_gt (A (x ω) : ℝ≥0∞) (ρs n (rec ω, fun u => R u ω)) with hle | hlt
    · exact ((ENNReal.cancel_of_ne ENNReal.coe_ne_top).tsub_lt_tsub_iff_right hle).2 ((ha hG).1 n)
    · rw [tsub_eq_zero_of_le hlt.le]
      exact tsub_pos_of_lt (hs hG)
  · filter_upwards [hstg, hann] with ω hω ha hG
    simp only [hω]
    rw [← ENNReal.iSup_sub, (ha hG).2]

end InteractingSLE.Theorem14.GW2Rd
