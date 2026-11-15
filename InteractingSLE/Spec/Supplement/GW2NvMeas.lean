/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuStage

/-!
# Measurability of a continuation threshold at a random time

Packet PROVE-GW2-NOTHR (round 4, D46: the kernel-to-`P` step for BUF's `DeathThrXStatement`). The threshold at the
death is read at a random time. This file proves the measurability facts needed to move it from the launch kernel to
`P`:

* **`measurable_rightImg_at`**: the right image of a random mark along a continuous, pointwise measurable path at a
  measurable random time is measurable (Carathéodory: continuous in time, measurable in `ω`);
* **`measurable_path_at`**: a continuous, pointwise measurable path at a measurable random time is measurable;
* **`measurableSet_thresholdCondition`**: the threshold condition of measurable states and fixed weights is a
  measurable event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Nv

open MartChar.RealFlow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **A continuous, pointwise measurable path at a measurable random time is measurable.** -/
theorem measurable_path_at {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, Measurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    {u : Ω → ℝ≥0} (hu : Measurable u) : Measurable fun ω => W (u ω) ω :=
  (measurable_uncurry_of_continuous_of_measurable hWc hWm).comp (hu.prodMk measurable_id)

/-- **The right image of a random mark at a measurable random time is measurable** (continuous, pointwise
measurable path). -/
theorem measurable_rightImg_at {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, Measurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    {x : Ω → ℝ} (hx : Measurable x) {u : Ω → ℝ≥0} (hu : Measurable u) :
    Measurable fun ω => rightImg (fun v : ℝ => W v.toNNReal ω) (x ω) (u ω) := by
  set g : ℝ≥0 → Ω → ℝ := fun t ω => rightImg (Bessel.realPath W ω) (x ω) t with hgdef
  have hgc : ∀ ω, Continuous fun t => g t ω := fun ω =>
    (MartChar.isForcePath_rightImg (Bessel.continuous_realPath hWc ω) (x ω)).1
  have hgm : ∀ t, Measurable (g t) := fun t =>
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable
      (𝓕 := Filtration.const (ι := ℝ≥0) mΩ le_rfl) hWm hWc hx t
  exact measurable_path_at hgm hgc hu

/-- **The threshold condition of measurable states is a measurable event** (fixed weights). -/
theorem measurableSet_thresholdCondition {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {w : Ω → ℝ}
    (hw : Measurable w) {vL : Fin nL → Ω → ℝ} (hvL : ∀ i, Measurable (vL i)) {vR : Fin nR → Ω → ℝ}
    (hvR : ∀ j, Measurable (vR j)) :
    MeasurableSet {ω | ForceWord.ThresholdCondition ρL ρR (w ω) (fun i => vL i ω) (fun j => vR j ω)} := by
  classical
  have key : ∀ {n : ℕ} (ρ : Fin n → ℝ) (v : Fin n → Ω → ℝ), (∀ i, Measurable (v i)) →
      MeasurableSet {ω | ∑ i ∈ univ.filter (fun i => v i ω = w ω), ρ i ≤ -2} := by
    intro n ρ v hv
    have heq : {ω | ∑ i ∈ univ.filter (fun i => v i ω = w ω), ρ i ≤ -2} =
        ⋃ A : Finset (Fin n), {ω | univ.filter (fun i => v i ω = w ω) = A} ∩ {_ω | ∑ i ∈ A, ρ i ≤ -2} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨A, hA, h⟩ => hA ▸ h⟩
    rw [heq]
    refine MeasurableSet.iUnion fun A => MeasurableSet.inter ?_ (MeasurableSet.const _)
    have hA : {ω | univ.filter (fun i => v i ω = w ω) = A} =
        ⋂ i : Fin n, {ω | (v i ω = w ω) ↔ i ∈ A} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hA]
    refine MeasurableSet.iInter fun i => ?_
    have hE : MeasurableSet {ω | v i ω = w ω} := measurableSet_eq_fun (hv i) hw
    by_cases hi : i ∈ A
    · simpa only [hi, iff_true] using hE
    · have e : {ω | (v i ω = w ω) ↔ i ∈ A} = {ω | v i ω = w ω}ᶜ := by
        ext ω; simp only [hi, iff_false, mem_ofPred_eq, mem_compl_iff]
      rw [e]; exact hE.compl
  exact (key ρL vL hvL).union (key ρR vR hvR)

end InteractingSLE.Theorem14.GW2Nv
