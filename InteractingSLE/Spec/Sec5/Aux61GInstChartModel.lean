/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstChartFrontier

/-! # The bounded model of the retained counterflow and forward prefix -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Sec5.Aux61GInst
open WangWu (negInv)

/-- The circle and the two retained paths in the bounded physical coordinate. -/
def retainedModelBoundary (K A : Set ℂ) : Set ℂ :=
  (sphere (0 : ℂ) 1 ∪ (fun z => -cayley z) '' K) ∪ cayley '' A

theorem cayley_image_inverted_complement (K : Set ℂ) :
    cayley '' (H \ negInv '' fillH K) = Neg.neg '' (cayley '' (H \ fillH K)) := by
  rw [WangWu.H_diff_image_negInv, image_image, image_image]
  exact image_congr fun z hz => Sec7.PocketJordan.cayley_negInv
    (QuantumZipper.H_subset_Hbar hz.1) (WangWu.ne_zero_of_mem_H hz.1)

/-- A component's model boundary is covered by the circle and the two raw
retained traces, even when the counterflow trace has self-contacts. -/
theorem frontier_retainedModel_subset {K A : Set ℂ} (hK : IsCompact K)
    (hA : IsCompact A) (hAH : A ⊆ Hbar) {b : ℂ}
    (hb : b ∈ (H \ negInv '' fillH K) \ A) :
    frontier (cayley '' connectedComponentIn ((H \ negInv '' fillH K) \ A) b) ⊆
      retainedModelBoundary K A := by
  let U := H \ negInv '' fillH K
  have hUo : IsOpen U := by
    change IsOpen (H \ negInv '' fillH K)
    rw [WangWu.H_diff_image_negInv]
    exact WangWu.isOpen_image_negInv (isOpen_H_diff_fillH hK.isBounded) sdiff_subset
  have hUHo : U ⊆ H := sdiff_subset
  have hUD : ContinuousOn cayley (U \ A) := continuousOn_cayley_Hbar.mono
    (sdiff_subset.trans (hUHo.trans QuantumZipper.H_subset_Hbar))
  have he : cayley '' (U \ A) = cayley '' U \ cayley '' A := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨mem_image_of_mem _ hz.1, ?_⟩
      rintro ⟨a, ha, he⟩
      exact hz.2 ((QuantumZipper.CA.Uniformizer.cayley_injOn_Hbar (hAH ha)
        (QuantumZipper.H_subset_Hbar (hUHo hz.1)) he) ▸ ha)
    · exact subset_image_sdiff _ _ _
  have hcomp := image_component_of_leftInverse hUD
    (QuantumZipper.CA.continuousOn_cayleyInv.mono fun z hz =>
      Sec7.Lemma71F.ne_one_of_mem_ball (Sec7.Lemma71F.cayley_image_subset_ball
        (sdiff_subset.trans hUHo) hz))
    (fun z hz => cayleyInv_cayley_of_mem_Hbar (QuantumZipper.H_subset_Hbar (hUHo hz.1))) hb
  rw [hcomp, he]
  have hAc : IsCompact (cayley '' A) := hA.image_of_continuousOn
    (continuousOn_cayley_Hbar.mono hAH)
  intro z hz
  rcases frontier_component_diff_subset (Sec7.Lemma71F.isOpen_cayley_image hUo hUHo)
      hAc.isClosed (cayley b) hz with hzU | hzA
  · have hn : -z ∈ frontier (cayley '' (H \ fillH K)) := by
      rw [cayley_image_inverted_complement] at hzU
      change z ∈ frontier ((Homeomorph.neg ℂ) '' (cayley '' (H \ fillH K))) at hzU
      rw [← (Homeomorph.neg ℂ).image_frontier] at hzU
      obtain ⟨w, hw, hwz⟩ := hzU
      change -w = z at hwz
      rw [← hwz, neg_neg]
      exact hw
    rcases frontier_cayley_fill_subset hK hn with hzS | ⟨k, hk, hke⟩
    · exact Or.inl (Or.inl (by simpa [mem_sphere_zero_iff_norm] using hzS))
    · exact Or.inl (Or.inr ⟨k, hk, by simpa using congrArg Neg.neg hke⟩)
  · exact Or.inr hzA

/-- The same boundary cover avoids the retained component's model domain. -/
theorem retainedModelBoundary_disjoint {K A : Set ℂ} (hKH : K ⊆ Hbar)
    (hAH : A ⊆ Hbar) (b : ℂ) :
    Disjoint (retainedModelBoundary K A)
      (cayley '' connectedComponentIn ((H \ negInv '' fillH K) \ A) b) := by
  rw [Set.disjoint_left]
  rintro w (hw | hw) ⟨z, hz, rfl⟩
  · rcases hw with hw | ⟨k, hk, he⟩
    · have hzH := (connectedComponentIn_subset _ _ hz).1.1
      have hn := QuantumZipper.CA.cayley_mem_ball hzH
      rw [mem_sphere_zero_iff_norm] at hw
      rw [mem_ball_zero_iff, hw] at hn
      exact lt_irrefl _ hn
    · have hzU := (connectedComponentIn_subset _ _ hz).1
      have hm : cayley z ∈ cayley '' (H \ negInv '' fillH K) := ⟨z, hzU, rfl⟩
      rw [cayley_image_inverted_complement] at hm
      obtain ⟨v, ⟨u, hu, rfl⟩, heq⟩ := hm
      have hku : k = u := QuantumZipper.CA.Uniformizer.cayley_injOn_Hbar (hKH hk)
        (QuantumZipper.H_subset_Hbar hu.1) (neg_injective (he.trans heq.symm))
      exact hu.2 ⟨hu.1, Or.inl (subset_closure (hku ▸ hk))⟩
  · obtain ⟨a, ha, he⟩ := hw
    have hzD := connectedComponentIn_subset _ _ hz
    exact hzD.2 ((QuantumZipper.CA.Uniformizer.cayley_injOn_Hbar (hAH ha)
      (QuantumZipper.H_subset_Hbar hzD.1.1) he) ▸ ha)

end InteractingSLE.Sec5.Aux61GInst
