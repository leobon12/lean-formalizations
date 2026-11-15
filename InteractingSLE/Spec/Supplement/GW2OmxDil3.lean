/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxGeo
import InteractingSLE.Spec.Supplement.GW2OmxDil1

/-!
# GW2's open lines: where the launch chart sends the new explored hull and the counterflow's continuation

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation). Deterministic set lemmas for a conformal chart
`cL`, and the closure disjointness before the first tip at any retained time:

* `fwd_mem_diff_of_image_eq`: if `cL` carries `B₀` to `A` and `Bu` to `A ∪ K`, a point of `Bu ∖ B₀` in the domain is
  sent into `K ∖ A`;
* `fwd_mem_diff_of_inv_image_eq`: if `cL⁻¹` carries `A₀'` to `A₀` and `A₁'` to `A₁`, a point of `A₁ ∖ A₀` is sent
  into `A₁' ∖ A₀'`;
* **`disjoint_closure_of_lt_firstTipTime`**: `GW2Omx.disjoint_closure_of_mem_noContact` at any time `s'` before the
  counterflow's first tip in the explored trace image.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd Supp8.GB6 Exist.StagedLaw

/-- A point of `Bu ∖ B₀` in the domain is sent into `K ∖ A`. -/
theorem fwd_mem_diff_of_image_eq {cL : Chart} (hconf : cL.IsConformal) {B₀ Bu A K : Set ℂ}
    (h0 : cL.1 '' (B₀ ∩ (cL.dom : Set ℂ)) = A) (hu : cL.1 '' (Bu ∩ (cL.dom : Set ℂ)) = A ∪ K) {z : ℂ}
    (hz : z ∈ (Bu \ B₀) ∩ (cL.dom : Set ℂ)) : cL.1 z ∈ K \ A := by
  have h1 : cL.1 z ∈ A ∪ K := by
    rw [← hu]
    exact ⟨z, ⟨hz.1.1, hz.2⟩, rfl⟩
  have h2 : cL.1 z ∉ A := by
    rw [← h0]
    rintro ⟨z', hz', he⟩
    have : z' = z := by rw [← hconf.inv_fwd hz'.2, he, hconf.inv_fwd hz.2]
    exact hz.1.2 (this ▸ hz'.1)
  rcases h1 with h | h
  · exact absurd h h2
  · exact ⟨h, h2⟩

/-- A point of `A₁ ∖ A₀` is sent into `A₁' ∖ A₀'`. -/
theorem fwd_mem_diff_of_inv_image_eq {cL : Chart} (hconf : cL.IsConformal) {A₀ A₁ A₀' A₁' : Set ℂ}
    (h0 : cL.2.1 '' A₀' = A₀) (h1 : cL.2.1 '' A₁' = A₁) (hA₁' : A₁' ⊆ H) {z : ℂ} (hz : z ∈ A₁ \ A₀) :
    cL.1 z ∈ A₁' \ A₀' := by
  obtain ⟨w, hw, rfl⟩ := (h1 ▸ hz.1 : z ∈ cL.2.1 '' A₁')
  rw [hconf.2.2 w (hA₁' hw)]
  exact ⟨hw, fun hw0 => hz.2 (h0 ▸ ⟨w, hw0, rfl⟩)⟩

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **Before the first tip, the closures of the explored hull and of the retained hull are disjoint.** -/
theorem disjoint_closure_of_lt_firstTipTime {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe) (hce : Continuous fun u => schedW c r l a u ω)
    (h0e : schedW c r l a 0 ω = 0) {s' : ℝ≥0}
    (hs' : (s' : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω) (ηe '' Icc 0 (historyTime c r l))) :
    Disjoint (closure (fwdHull (fun u : ℝ => schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (s' : ℝ))) := by
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hηec : Continuous ηe := continuousOn_univ.1 (hηe.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hsep : ∀ t ∈ Icc 0 s', ∀ u ∈ Icc 0 (historyTime c r l), η t * ηe u + 1 ≠ 0 := by
    intro t ht u hu hzero
    have hγt : η t ≠ 0 := by
      intro h0'
      rw [h0', zero_mul, zero_add] at hzero
      exact one_ne_zero hzero
    refine noContact_of_lt_firstTipTime hη hc h0 hs' ht.2 hγt ⟨u, hu, ?_⟩
    have e : η t * ηe u = -1 := eq_neg_of_add_eq_zero_left hzero
    calc ηe u = (η t)⁻¹ * (η t * ηe u) := by field_simp
      _ = -(η t)⁻¹ := by rw [e]; ring
  have hTc := (Gm.lt_firstContactTime_iff_noncontact hηc hηec s' (historyTime c r l)).2 hsep
  exact disjoint_closure_fwdHull_of_lt_firstContactTime hηe hce.continuousOn h0e hη hc.continuousOn h0
    ENNReal.coe_lt_top ENNReal.coe_lt_top hTc

end InteractingSLE.Theorem14.GW2Omx
