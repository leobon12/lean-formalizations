/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS5SideProof
import InteractingSLE.Spec.Supplement.SB4SwitchKernel

/-!
# Actual-tail side transport for SB4

The gate lemma of S5 identifies the frozen half-plane sides with the Jordan
sides of a proper curve. The complete-tail form of S5 then transports the
closed right side, including real contacts, without choosing an artificial
completion of the physical walk. These are deterministic sewing facts;
identification of the retained conditional field is a separate obligation.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB

/-- The negative gate of S5 also witnesses membership in the frozen left side. -/
theorem leftSide_inter_H_subset_leftSideOf {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) :
    leftSide γ ∩ H ⊆ leftSideOf (range γ) := by
  intro w hw
  obtain ⟨x, hx, hxγ, hxC⟩ := s5_exists_negative_gate hγ hγ0 hw
  have hsub : leftSide γ ∩ H ⊆ H \ range γ := fun z hz =>
    ⟨hz.2, notMem_range_of_mem_leftSide hz.1⟩
  exact ⟨hsub hw, x, hx, hxγ,
    closure_mono (connectedComponentIn_mono w hsub) hxC⟩

/-- Reflection of S5's negative gate supplies the frozen right-side witness. -/
theorem rightSide_inter_H_subset_rightSideOf {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) :
    rightSide γ ∩ H ⊆ rightSideOf (range γ) := by
  intro w hw
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hγr := isProperCurve_reflectCurve hγ
  have hγr0 : reflectCurve γ 0 = 0 := by
    simp only [reflectCurve, hγ0, Supp9B.refl, map_zero, neg_zero]
  have hwr : Supp9B.refl w ∈ leftSide (reflectCurve γ) ∩ H :=
    ⟨refl_image_rightSide_subset hγ.2.2.1 h0 ⟨w, hw.1, rfl⟩,
      by simpa only [QuantumZipper.H, mem_ofPred_eq, refl_im] using hw.2⟩
  obtain ⟨x, hx, hxγ, hxC⟩ := s5_exists_negative_gate hγr hγr0 hwr
  have hreflect : Supp9B.refl '' (leftSide (reflectCurve γ) ∩ H) ⊆ H \ range γ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨by simpa only [QuantumZipper.H, mem_ofPred_eq, refl_im] using hz.2, ?_⟩
    rintro ⟨t, ht⟩
    exact notMem_range_of_mem_leftSide hz.1 ⟨t,
      (congrArg Supp9B.refl ht).trans (refl_refl z)⟩
  have hCsub : Supp9B.refl '' connectedComponentIn
      (leftSide (reflectCurve γ) ∩ H) (Supp9B.refl w) ⊆
      connectedComponentIn (H \ range γ) w := by
    have hc := continuous_refl.continuousOn.image_connectedComponentIn_subset hwr
    rw [refl_refl] at hc
    exact hc.trans (connectedComponentIn_mono w hreflect)
  have hxcl : Supp9B.refl (x : ℂ) ∈ closure (connectedComponentIn (H \ range γ) w) :=
    closure_mono hCsub (mem_closure_image continuous_refl.continuousAt hxC)
  have hxreal : Supp9B.refl (x : ℂ) = ((-x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp only [refl_re, refl_im, ofReal_re, ofReal_im]
  refine ⟨⟨hw.2, notMem_range_of_mem_rightSide hw.1⟩, -x, neg_pos.2 hx, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    apply hxγ
    refine ⟨t, ?_⟩
    change Supp9B.refl (γ t) = (x : ℂ)
    rw [ht, ← hxreal, refl_refl]
  · rwa [hxreal] at hxcl

/-- In the physical half-plane the two right-side conventions agree. -/
theorem rightSideOf_range_eq_inter_H {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) :
    rightSideOf (range γ) = rightSide γ ∩ H :=
  Subset.antisymm (fun _ hz =>
    ⟨rightSideOf_range_subset_rightSide hγ hγ0 hz, hz.1.1⟩)
    (rightSide_inter_H_subset_rightSideOf hγ hγ0)

/-- An interior point avoiding the frozen right side is on the closed left
Jordan side. Real points require the stronger prefix comparison below. -/
theorem mem_closedLeftSide_of_notMem_rightSideOf {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {z : ℂ} (hzH : z ∈ H)
    (hz : z ∉ rightSideOf (range γ)) : z ∈ closedLeftSide γ := by
  by_cases hzS : z ∈ seedRayClosure γ
  · exact Or.inr hzS
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hs : z ∈ leftSide γ ∪ rightSide γ := (compl_seedRayClosure_eq hγ h0) ▸ hzS
  rcases hs with hzL | hzR
  · exact Or.inl hzL
  · exact (hz (rightSide_inter_H_subset_rightSideOf hγ hγ0 ⟨hzR, hzH⟩)).elim

end InteractingSLE.Theorem14.SB
