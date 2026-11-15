/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE13Dense
import InteractingSLE.Spec.Supplement.GW2RootD12Upper

/-!
# Exact upper trace carriers in the joint chart before contact

Packet PROVE-T14-GW2ROOT2. GB6 identifies the physical tip at relative
interior times. Density through the continuous strictly increasing clock
proves the converse and equality of the finite upper trace carriers.
The hypotheses are the existing GB6 hull identification and its clock
continuity; their construction for a particular exploration is separate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE13

open Supp8.GB6

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

include hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ hsm hac hnn hK hdom hγdom

/-- Physical interior tips are relative interior tips, with the same
chart identification as GB6. Continuity fills its missing implication. -/
theorem relTrace_eq_of_physical_mem_H {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Tc)
    (hγH : γ t ∈ H) :
    Γ (relClock U σ (fun r : ℝ => Wc r.toNNReal) t).toNNReal ∈ H ∧
      Γ (relClock U σ (fun r : ℝ => Wc r.toNNReal) t).toNNReal = relMap U σ (γ t) := by
  let a : ℝ≥0 → ℝ := fun r => relClock U σ (fun q : ℝ => Wc q.toNNReal) r
  let E : Set ℝ≥0 := {r | (r : ℝ≥0∞) < Tc ∧ Γ (a r).toNNReal ∈ H}
  have hcl : t ∈ closure E := mem_closure_clock_mem_H hac hsm hnn hΓ hW' hW'0 ht
  have : (𝓝[E] t).NeBot := mem_closure_iff_clusterPt.mp hcl
  have hγc := GW2Cone.continuous_of_isGeneratingTrace_top hγ
  have hΓc := GW2Cone.continuous_of_isGeneratingTrace_top hΓ
  have ha : ContinuousWithinAt a E t := (hac t ht).mono (fun r hr => hr.1)
  have hF : Tendsto (fun r => Γ (a r).toNNReal) (𝓝[E] t) (𝓝 (Γ (a t).toNNReal)) :=
    (hΓc.tendsto _).comp ((continuous_real_toNNReal.tendsto _).comp ha)
  have hG : Tendsto (fun r => relMap U σ (γ r)) (𝓝[E] t) (𝓝 (relMap U σ (γ t))) :=
    ((continuousAt_relMap hU hσ hγH (hγdom t ht hγH)).tendsto.comp (hγc.tendsto t)).mono_left
      nhdsWithin_le_nhds
  have heq : (fun r => Γ (a r).toNNReal) =ᶠ[𝓝[E] t] (fun r => relMap U σ (γ r)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (relTrace_eq hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ hsm hnn hK hdom hγdom hr.1 hr.2).2
  have he := tendsto_nhds_unique_of_eventuallyEq hF hG heq
  exact ⟨he.symm ▸ relMap_mem_H hU hσ hγH (hγdom t ht hγH), he⟩

/-- Before contact, being an interior tip is equivalent in the two clocks. -/
theorem relTrace_mem_H_iff {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Tc) :
    Γ (relClock U σ (fun r : ℝ => Wc r.toNNReal) t).toNNReal ∈ H ↔ γ t ∈ H := by
  constructor
  · exact fun htH => (relTrace_eq hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
      hsm hnn hK hdom hγdom ht htH).1
  · exact fun htH => (relTrace_eq_of_physical_mem_H hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
      hsm hac hnn hK hdom hγdom ht htH).1

/-- The literal upper physical prefix in the joint chart is exactly the
relative upper trace prefix, including its endpoint and the zero cutoff. -/
theorem relMap_upper_prefix_eq (ha0 : relClock U σ (fun r : ℝ => Wc r.toNNReal) 0 = 0)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < Tc) :
    relMap U σ '' (γ '' Icc 0 v ∩ H) =
      Γ '' Icc 0 (relClock U σ (fun r : ℝ => Wc r.toNNReal) v).toNNReal ∩ H := by
  let a : ℝ≥0 → ℝ := fun r => relClock U σ (fun q : ℝ => Wc q.toNNReal) r
  have hsub : Icc 0 v ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < Tc} :=
    fun r hr => (ENNReal.coe_le_coe.mpr hr.2).trans_lt hv
  apply Subset.antisymm
  · rintro z ⟨_, ⟨⟨r, hr, rfl⟩, hrH⟩, rfl⟩
    obtain ⟨hH, heq⟩ := relTrace_eq_of_physical_mem_H hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
      hsm hac hnn hK hdom hγdom (hsub hr) hrH
    rw [← heq]
    refine ⟨⟨(a r).toNNReal, ⟨zero_le, ?_⟩, rfl⟩, hH⟩
    exact Real.toNNReal_mono (hsm.monotoneOn (hsub hr) hv hr.2)
  · rintro z ⟨⟨u, hu, rfl⟩, huH⟩
    have huR : (u : ℝ) ≤ a v := by
      have := NNReal.coe_le_coe.mpr hu.2
      rwa [Real.coe_toNNReal _ (hnn v hv)] at this
    have ha0' : a 0 = 0 := by simpa only [a, NNReal.coe_zero] using ha0
    have hu0 : a 0 ≤ (u : ℝ) := by rw [ha0']; exact u.coe_nonneg
    obtain ⟨r, hr, her⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ v)
      (hac.mono hsub) ⟨hu0, huR⟩
    change a r = (u : ℝ) at her
    have hrH : Γ (a r).toNNReal ∈ H := by simpa only [her, Real.toNNReal_coe] using huH
    obtain ⟨hγH, heq⟩ := relTrace_eq hWc hWc0 hU hU0 hσ hγ hW' hW'0 hΓ
      hsm hnn hK hdom hγdom (hsub hr) hrH
    refine ⟨γ r, ⟨⟨r, hr, rfl⟩, hγH⟩, ?_⟩
    change Γ (a r).toNNReal = relMap U σ (γ r) at heq
    rw [her, Real.toNNReal_coe] at heq
    exact heq.symm

end Trace

end InteractingSLE.Theorem14.GW2TipSystem.RootE13
