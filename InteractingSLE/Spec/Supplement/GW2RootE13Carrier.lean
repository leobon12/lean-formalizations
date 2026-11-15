/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE13Trace

/-!
# Literal joint-chart carriers and their capacity

Packet PROVE-T14-GW2ROOT2. Restricting to the actual joint-chart domain
removes precisely the non-upper physical points before contact. The
relative generating trace then proves boundedness, attachment, filling
and the exact capacity of this image.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE13

open Supp8.GB6 Restart

/-- The physical domain of the joint chart lies in the upper half-plane. -/
theorem jointDomain_subset_H (U : ℝ → ℝ) (σ : ℝ) :
    (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ) ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  exact neg_inv_mem_H hz.1

/-- Before contact, the upper trace points are precisely those in the
physical joint-chart domain. -/
theorem prefix_inter_jointDomain_eq {γ : ℝ≥0 → ℂ} {v : ℝ≥0} {U : ℝ → ℝ} {σ : ℝ}
    (hγdom : ∀ r ∈ Icc 0 v, γ r ∈ H → -(γ r)⁻¹ ∉ QuantumZipper.fwdHull U σ) :
    γ '' Icc 0 v ∩ (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ) =
      γ '' Icc 0 v ∩ H := by
  apply Subset.antisymm
  · intro z hz
    exact ⟨hz.1, jointDomain_subset_H U σ hz.2⟩
  · rintro z ⟨⟨r, hr, rfl⟩, hzH⟩
    exact ⟨⟨r, hr, rfl⟩, ⟨-(γ r)⁻¹, ⟨neg_inv_mem_H hzH, hγdom r hr hzH⟩,
      neg_inv_neg_inv _⟩⟩

section Trace

variable {Wc W' : ℝ≥0 → ℝ} {U : ℝ → ℝ} {σ : ℝ} {Tc : ℝ≥0∞}
  {γ Γ : ℝ≥0 → ℂ}
  (hWc : Continuous Wc) (hWc0 : Wc 0 = 0)
  (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
  (hγ : IsGeneratingTrace Wc ⊤ γ)
  (hW' : Continuous W') (hW'0 : W' 0 = 0) (hΓ : IsGeneratingTrace W' ⊤ Γ)
  (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t)
    {t | (t : ℝ≥0∞) < Tc})
  (hac : ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t)
    {t | (t : ℝ≥0∞) < Tc})
  (hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ relClock U σ (fun r : ℝ => Wc r.toNNReal) t)
  (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
    QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal)
      (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
        relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t)
  (hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
    ∀ w ∈ QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t,
      -w⁻¹ ∉ QuantumZipper.fwdHull U σ)
  (hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → γ t ∈ H →
    -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U σ)
  (ha0 : relClock U σ (fun r : ℝ => Wc r.toNNReal) 0 = 0)

include hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ hsm hac hnn hK hdom hγdom ha0

/-- The literal joint-chart image of the physical prefix is the upper
part of the relative trace, with its exact relative capacity cutoff. -/
theorem jointChart_prefix_eq {v : ℝ≥0} (hv : (v : ℝ≥0∞) < Tc) :
    (GW2JointKernel.jointChart U σ).1 ''
        (γ '' Icc 0 v ∩ (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ)) =
      Γ '' Icc 0 (relClock U σ (fun r : ℝ => Wc r.toNNReal) v).toNNReal ∩ H := by
  rw [prefix_inter_jointDomain_eq (fun r hr => hγdom r
    ((ENNReal.coe_le_coe.mpr hr.2).trans_lt hv))]
  change relMap U σ '' (γ '' Icc 0 v ∩ H) = _
  exact relMap_upper_prefix_eq hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hv

/-- The joint-chart image is bounded and attached, and its filling has
the full relative trace prefix as a compact representative. -/
theorem jointChart_prefix_geometry {v : ℝ≥0} (hv : (v : ℝ≥0∞) < Tc) :
    let A := (GW2JointKernel.jointChart U σ).1 ''
      (γ '' Icc 0 v ∩ (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ))
    Bornology.IsBounded A ∧ IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) ∧
      fillH A = fillH (Γ '' Icc 0 (relClock U σ (fun r : ℝ => Wc r.toNNReal) v).toNNReal) := by
  dsimp only
  rw [jointChart_prefix_eq hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hv]
  exact (RootD12.upper_prefix_geometry
    (GW2Cone.continuous_of_isGeneratingTrace_top hΓ).continuousOn
    (by rw [hΓ.1]; exact le_rfl)).2

/-- GW2's literal half capacity of the joint-chart prefix equals the
relative clock. Its boundedness and attachment are conclusions, not inputs. -/
theorem capOf_jointChart_prefix {v : ℝ≥0} (hv : (v : ℝ≥0∞) < Tc) :
    capOf ((GW2JointKernel.jointChart U σ).1 ''
        (γ '' Icc 0 v ∩ (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ))) =
      relClock U σ (fun r : ℝ => Wc r.toNNReal) v := by
  obtain ⟨hb, ha, hf⟩ := jointChart_prefix_geometry hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hv
  rw [RootC11.capOf_eq_hcapSet hb ha, hf]
  have hΓ0 : IsGeneratingTrace W' ⊤ (fun r => Γ r - (0 : ℝ)) := by simpa only [ofReal_zero, sub_zero]
  have hc := Restart.IsGeneratingTrace.hcapSet_fillH_add hΓ0 hW'.continuousOn hW'0
    (ENNReal.coe_lt_top (r := (relClock U σ (fun r : ℝ => Wc r.toNNReal) v).toNNReal))
  rw [hc, Real.coe_toNNReal _ (hnn v hv)]
  ring

end Trace

end InteractingSLE.Theorem14.GW2TipSystem.RootE13
