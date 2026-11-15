/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmShape

/-!
# GW2's open lines: before the version's cap, the explored curve has not touched the counterflow

Packet PROVE-GW2-STAGEMEAN, R121 round.

* **`ae_lt_contactX_all`**: almost surely on the good event, at every time whose root-`x` line clock is below the
  version's cap, the explored curve has not yet contacted the counterflow's trace up to `s` (the step of ROOTX's
  `GW2Rz.ae_compl_union_eq_relChartX`, with the time inside the event);
* **`mul_add_one_ne_zero_of_lt_contactX`**: at the root `0`, before the contact, no explored point is the
  counterflow's point (`α v · γ u + 1 ≠ 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.ReadD GW2TipSystem GW2Rz
open Supp8.RelSafe (supBelow)

section Live

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

include hGT hs₀ hx₀ in
/-- **Before the version's cap, the explored curve has not touched the counterflow** (every time, one event). -/
theorem ae_lt_contactX_all (hver : IsRelVersionX x₀ s P Wα ζα W γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ GT → ∀ t : ℝ≥0, min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω →
      (t : ℝ≥0∞) < contactX x₀ s γ α ω := by
  filter_upwards [hver.2.2.2.2.2.2] with ω hω hωG t hlt
  have hg := hGT ω hωG
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hWc, hW0, hζ⟩, harc, -, hgx⟩ := hg
  obtain ⟨-, hreachV, hhull⟩ := hω hgx
  by_contra hcon
  have hle : contactX x₀ s γ α ω ≤ t := le_of_not_gt hcon
  have hV : V ω ≤ physClockX x₀ s Wα ζα W GT t ω := by
    rw [physClockX_eq_iSup hGT hs₀ hx₀ hωG]
    refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
    obtain ⟨t', ht', hut'⟩ := hreachV u hu
    have ht't : t' < t := by
      have := lt_of_lt_of_le ht' hle
      exact_mod_cast this
    refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < contactX x₀ s γ α ω) =>
      ENNReal.ofReal (clockX x₀ s Wα ζα W t' ω)) t' ⟨ht't, ht'⟩)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hut'.le
  rw [min_eq_right hV] at hlt
  exact lt_irrefl _ hlt

end Live

/-- **Before the contact, no explored point is the counterflow's point** (root `0`). -/
theorem mul_add_one_ne_zero_of_lt_contactX {s : ℝ≥0} {γ α : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < firstContactTime (fun u => sphereInv ((((0 : ℝ) : ℂ) + γ u : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) :
    ∀ v ∈ Icc 0 s, ∀ u ≤ t, α v * γ u + 1 ≠ 0 := by
  intro v hv u hu h
  have hlt : (u : ℝ≥0∞) < firstContactTime (fun u => sphereInv ((((0 : ℝ) : ℂ) + γ u : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := (ENNReal.coe_le_coe.2 hu).trans_lt ht
  refine notMem_of_lt_firstContactTime hlt ⟨v, hv, ?_⟩
  have hγ0 : γ u ≠ 0 := fun h0 => by rw [h0, mul_zero, zero_add] at h; exact one_ne_zero h
  simp only [Complex.ofReal_zero, zero_add]
  rw [sphereInv_coe_of_ne hγ0]
  congr 1
  field_simp
  linear_combination h

end InteractingSLE.Theorem14.GW2Psm
