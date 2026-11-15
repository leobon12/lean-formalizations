/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil3
import InteractingSLE.Spec.Supplement.Aux10FullLocal

/-!
# GW2's open lines: the stage chart near its two normalization points

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation, stage side). Deterministic:

* `fwd_mem_of_shape`: where the stage shape `ℍ ∖ B_u = cs⁻¹(ℍ ∖ K)` holds, `cs` sends `B_u` (in its domain) into `K`;
* **`loewner_fwd_far`**: a chart followed by a Loewner map moves points by a bounded amount: on the domain,
  `‖c₀.1 z‖ − C ≤ ‖(c₀.loewner W a).1 z‖`;
* `loewner_dom_fwd`: on the domain of `c₀.loewner W a`, `c₀.1 z` is off the hull at `a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

/-- Where the stage shape holds, the stage chart sends the union into the hull. -/
theorem fwd_mem_of_shape {cs : Chart} (hcs : cs.IsConformal) {Bu K : Set ℂ} (hsh : H \ Bu = cs.2.1 '' (H \ K))
    {z : ℂ} (hz : z ∈ Bu) (hzd : z ∈ (cs.dom : Set ℂ)) : cs.1 z ∈ K := by
  by_contra hK
  have hmem : z ∈ cs.2.1 '' (H \ K) := ⟨cs.1 z, ⟨hcs.fwd_mem hzd, hK⟩, hcs.inv_fwd hzd⟩
  rw [← hsh] at hmem
  exact hmem.2 hz

/-- On the domain of `c₀.loewner W a`, the chart point is off the hull at `a`. -/
theorem loewner_dom_fwd {c₀ : Chart} (hc₀ : c₀.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z ∈ ((c₀.loewner W a).dom : Set ℂ)) :
    z ∈ (c₀.dom : Set ℂ) ∧ c₀.1 z ∈ H \ fwdHull W a := by
  have hcl : (c₀.loewner W a).IsConformal := hc₀.loewner hW hW0 ha
  rw [hcl.coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hv : fwdMapInv W a w ∈ H \ fwdHull W a := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 ha]
    exact ⟨w, hw, rfl⟩
  change c₀.2.1 (fwdMapInv W a w) ∈ (c₀.dom : Set ℂ) ∧ c₀.1 (c₀.2.1 (fwdMapInv W a w)) ∈ H \ fwdHull W a
  rw [hc₀.2.2 _ hv.1]
  exact ⟨hc₀.inv_mem_dom hv.1, hv⟩

/-- **A chart followed by a Loewner map moves points by a bounded amount.** -/
theorem loewner_fwd_far {c₀ : Chart} (hc₀ : c₀.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {a : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ z ∈ ((c₀.loewner W a).dom : Set ℂ),
      ‖c₀.1 z‖ - C ≤ ‖(c₀.loewner W a).1 z‖ := by
  obtain ⟨C, hC⟩ := Aux10.exists_norm_fwdMap_sub_le hW hW0 ha
  refine ⟨C, fun z hz => ?_⟩
  obtain ⟨-, hv⟩ := loewner_dom_fwd hc₀ hW hW0 ha hz
  have h := hC _ hv
  change ‖c₀.1 z‖ - C ≤ ‖fwdMap W a (c₀.1 z)‖
  have h2 := norm_sub_norm_le (c₀.1 z) (fwdMap W a (c₀.1 z))
  rw [norm_sub_rev] at h2
  linarith

end InteractingSLE.Theorem14.GW2Omx
