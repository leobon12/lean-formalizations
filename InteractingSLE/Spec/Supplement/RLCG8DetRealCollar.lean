/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetClosedMain
import InteractingSLE.Spec.Supplement.GB11GateFinalEnclosure

/-!
# G8: real contacts reduce to the endpoints of the remaining trace

The upper-half-ball argument used by GB11 also applies when the excluded
frontier is described in physical coordinates through a continuous inverse.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.G8Det.RealBoundary

/-- An adherent real point is outside the closed hull if an upper neighborhood
contains no point of the hull's upper frontier. -/
theorem notMem_closure_of_upper_frontier {A : Set ℂ} (hA : IsHPHull A) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (H \ A))
    (hfront : ∃ ε > 0, ∀ z ∈ ball (x : ℂ) ε, z ∈ A → z ∉ closure (H \ A)) :
    (x : ℂ) ∉ closure A := by
  obtain ⟨ε, hε, hav⟩ := hfront
  have hball : ball (x : ℂ) ε ∩ H ⊆ H \ A := by
    apply (HalfPlaneSep.isPreconnected_ball_inter_H (x : ℂ) ε).subset_left_of_subset_union
      hA.isOpen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure))
    · intro z hz
      by_cases hzA : z ∈ A
      · exact Or.inr (hav z hz.1 hzA)
      · exact Or.inl ⟨hz.2, hzA⟩
    · obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 hx ε hε
      exact ⟨z, ⟨by simpa only [mem_ball, dist_comm] using hzx, hz.1⟩, hz⟩
  intro hcl
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 hcl ε hε
  exact (hball ⟨by simpa only [mem_ball, dist_comm] using hzx, hA.1 hz⟩).2 hz

/-- A compact physical frontier avoids a real prime end whenever its continuous
inverse value is off that frontier and the end is adherent to the domain. -/
theorem notMem_closure_of_inverse_frontier {A B : Set ℂ} (hA : IsHPHull A)
    (hB : IsClosed B) {F : ℂ → ℂ} (hF : ContinuousOn F Hbar)
    (hfront : ∀ z ∈ A, z ∈ closure (H \ A) → F z ∈ B) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (H \ A)) (hxB : F x ∉ B) : (x : ℂ) ∉ closure A := by
  apply notMem_closure_of_upper_frontier hA hx
  have hc := hF x (ofReal_mem_Hbar x)
  have hev : ∀ᶠ z in 𝓝[Hbar] (x : ℂ), F z ∉ B :=
    hc.eventually (hB.isOpen_compl.mem_nhds hxB)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨ε, hε, fun z hz hzA hzcl => ?_⟩
  exact hball ⟨hz, H_subset_Hbar (hA.1 hzA)⟩ (hfront z hzA hzcl)

/-- A common real closure point of disjoint hulls must be on any closed trace
whose filling is the second hull. Off the trace, the existing free/trapped
half-ball dichotomy excludes the second hull altogether. -/
theorem mem_trace_of_common_real_closures {A S : Set ℂ} (hS : IsClosed S)
    (hAH : A ⊆ H) (hd : Disjoint A (fillH S)) {x : ℝ}
    (hxA : (x : ℂ) ∈ closure A) (hxK : (x : ℂ) ∈ closure (fillH S)) : (x : ℂ) ∈ S := by
  by_contra hxS
  have hsub : A ⊆ H \ fillH S := fun z hz =>
    ⟨hAH hz, fun hzK => Set.disjoint_left.1 hd hz hzK⟩
  have hf := Sec7.isFreeAt_of_mem_closure hS hxS (closure_mono hsub hxA)
  obtain ⟨ε, hε, hball⟩ := Sec7.exists_ball_of_isFreeAt hf
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 hxK ε hε
  exact (hball z (by simpa only [mem_ball, dist_comm] using hzx) (fillH_subset_H _ hz)).2 hz

end InteractingSLE.RLC.G8Det.RealBoundary
