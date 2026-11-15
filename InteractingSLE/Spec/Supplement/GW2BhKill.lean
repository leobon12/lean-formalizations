/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KM2PostStop
import InteractingSLE.Spec.Supplement.GW2BhRule

/-!
# Path rules as stopping rules of killed paths (S3)

Packet PROVE-GW2-BUF (S3). PROVE-GW2-SDE's `StageStop.Good` asks for a stopping rule of the record and the KILLED stage
path that is measurable for `GW2KM2.pathKilledSigma t` at every `t`. A path rule `ρ` of (record, path) becomes such a
rule when it reads the path killed at its cap (replaced by `0` from the cap on):

* `killPath e`: the path of `e = (w, V)` before `V`, and `0` from `V` on;
* **`measurableSet_killPath_le`**: for a measurable path rule `ρ` and every record `y`,
  `{e | ρ (y, killPath e) ≤ t}` is `pathKilledSigma t`-measurable;
* **`rule_killPath_eq`**: a path rule whose value is below the cap reads the same value on the killed path.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6.HullId GW2KM2

/-- The path of `e = (w, V)` killed at `V` (replaced by `0` from `V` on). -/
def killPath (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (r : ℝ≥0) : ℝ := if (r : ℝ≥0∞) < e.2 then e.1 r else 0

/-- The killed path up to `t`, extended by `0` after `t`. -/
def killPathUpTo (t : ℝ≥0) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (r : ℝ≥0) : ℝ := if r ≤ t then killPath e r else 0

theorem measurable_killPath_apply {t r : ℝ≥0} (hr : r ≤ t) :
    Measurable[pathKilledSigma t] fun e : (ℝ≥0 → ℝ) × ℝ≥0∞ => killPath e r := by
  intro B hB
  have hgen : MeasurableSet[pathKilledSigma t] {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (r : ℝ≥0∞) < e.2 ∧ e.1 r ∈ B} :=
    MeasurableSpace.measurableSet_generateFrom ⟨r, hr, B, hB, rfl⟩
  have hlt : MeasurableSet[pathKilledSigma t] {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (r : ℝ≥0∞) < e.2} := by
    have h := MeasurableSpace.measurableSet_generateFrom (s := {S | ∃ r ≤ t, ∃ A : Set ℝ, MeasurableSet A ∧
      S = {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (r : ℝ≥0∞) < e.2 ∧ e.1 r ∈ A}}) ⟨r, hr, univ, MeasurableSet.univ, rfl⟩
    simpa only [mem_univ, and_true] using h
  have he : (fun e : (ℝ≥0 → ℝ) × ℝ≥0∞ => killPath e r) ⁻¹' B =
      {e | (r : ℝ≥0∞) < e.2 ∧ e.1 r ∈ B} ∪ ({e | (r : ℝ≥0∞) < e.2}ᶜ ∩ {_e | (0 : ℝ) ∈ B}) := by
    ext e
    by_cases h : (r : ℝ≥0∞) < e.2 <;> simp [killPath, h]
  rw [he]
  exact hgen.union (hlt.compl.inter (MeasurableSet.const _))

theorem measurable_killPathUpTo (t : ℝ≥0) : Measurable[pathKilledSigma t] (killPathUpTo t) := by
  refine (@measurable_pi_iff ((ℝ≥0 → ℝ) × ℝ≥0∞) ℝ≥0 (fun _ => ℝ) (pathKilledSigma t) _ _).2 fun r => ?_
  by_cases hr : r ≤ t
  · have he : (fun e => killPathUpTo t e r) = fun e => killPath e r := by
      funext e; simp only [killPathUpTo, hr, ↓reduceIte]
    rw [he]
    exact measurable_killPath_apply hr
  · have he : (fun e => killPathUpTo t e r) = fun _ => (0 : ℝ) := by
      funext e; simp only [killPathUpTo, hr, ↓reduceIte]
    rw [he]
    exact measurable_const

/-- **A measurable path rule read on the killed path is a stopping rule of the killed path.** -/
theorem measurableSet_killPath_le {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (hρm : Measurable ρ)
    (y : RecData) (t : ℝ≥0) :
    MeasurableSet[pathKilledSigma t] {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | ρ (y, killPath e) ≤ (t : ℝ≥0∞)} := by
  have he : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | ρ (y, killPath e) ≤ (t : ℝ≥0∞)} =
      killPathUpTo t ⁻¹' {x | ρ (y, x) ≤ (t : ℝ≥0∞)} := by
    ext e
    simp only [mem_ofPred_eq, mem_preimage]
    exact pathRule_le_iff hρ fun u hu => by simp only [killPathUpTo, hu, ↓reduceIte]
  rw [he]
  have hmeas : MeasurableSet {x : ℝ≥0 → ℝ | ρ (y, x) ≤ (t : ℝ≥0∞)} :=
    measurableSet_le (hρm.comp (measurable_const.prodMk measurable_id)) measurable_const
  exact measurable_killPathUpTo t hmeas

/-- **Below the cap the killed path reads the same rule value.** -/
theorem rule_killPath_eq {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (y : RecData)
    (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (h : ρ (y, e.1) < e.2) : ρ (y, killPath e) = ρ (y, e.1) :=
  hρ y e.1 (killPath e) fun u hu => by
    simp only [killPath, ite_eq_left (hu.trans_lt h)]

end InteractingSLE.Theorem14.GW2Bh
