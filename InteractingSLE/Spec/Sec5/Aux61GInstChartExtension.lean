/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstChartModel
import InteractingSLE.GFF.Pushforward

/-! # Continuous bounded inverse extensions of retained charts -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open QuantumZipper.CA.Topo (ULC)

namespace InteractingSLE.Sec5.Aux61GInst
open WangWu (negInv)

theorem retainedModelBoundary_properties {K A : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hKu : ULC K)
    (hA : IsCompact A) (hAH : A ⊆ Hbar) (hAu : ULC A) :
    IsCompact (retainedModelBoundary K A) ∧ ULC (retainedModelBoundary K A) ∧
      retainedModelBoundary K A ⊆ closedBall (0 : ℂ) 1 := by
  have hKc := hK.image_of_continuousOn (continuousOn_cayley_Hbar.mono hKH)
  have hAc := hA.image_of_continuousOn (continuousOn_cayley_Hbar.mono hAH)
  have hKn : IsCompact ((fun z => -cayley z) '' K) :=
    hK.image_of_continuousOn ((continuousOn_cayley_Hbar.mono hKH).neg)
  have hKu' : ULC ((fun z => -cayley z) '' K) := by
    have hu := ulc_image_of_leftInvOn hKc continuous_neg.continuousOn continuous_neg.continuousOn
      (fun z _ => neg_neg z) (ulc_image_cayley hK hKH hKu)
    simpa only [image_image, Function.comp_def] using hu
  have hu := QuantumZipper.CA.Topo.ULC.union_of_isCompact_of_isClosed
    ((isCompact_sphere (0 : ℂ) 1).union hKn) hAc.isClosed
    (QuantumZipper.CA.Topo.ULC.union_of_isCompact_of_isClosed
      (isCompact_sphere (0 : ℂ) 1) hKn.isClosed
      (QuantumZipper.CA.Topo.ULC.sphere 0 1) hKu') (ulc_image_cayley hA hAH hAu)
  refine ⟨((isCompact_sphere (0 : ℂ) 1).union hKn).union hAc, hu, ?_⟩
  rintro z ((hz | ⟨k, hk, rfl⟩) | ⟨a, ha, rfl⟩)
  · exact sphere_subset_closedBall hz
  · simpa only [mem_closedBall_zero_iff, norm_neg] using QuantumZipper.CA.cayley_mem_closedBall (hKH hk)
  · exact QuantumZipper.CA.cayley_mem_closedBall (hAH ha)

/-- Carathéodory's theorem applies to every conformal chart of this retained
component, in the bounded physical coordinate `cayley`. -/
theorem exists_retained_inverse_extension {K A : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hKu : ULC K)
    (hA : IsCompact A) (hAH : A ⊆ Hbar) (hAu : ULC A) {b : ℂ}
    (hb : b ∈ (H \ negInv '' fillH K) \ A)
    {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = connectedComponentIn ((H \ negInv '' fillH K) \ A) b) :
    ∃ F : ℂ → ℂ, EqOn F (cayley ∘ c.2.1) H ∧ ContinuousOn F Hbar ∧
      DifferentiableOn ℂ F H ∧ InjOn F H ∧
      ∀ z : ℂ, z.im = 0 → F z ∉ F '' H := by
  let D : Set ℂ := cayley '' (c.dom : Set ℂ)
  let E : Set ℂ := retainedModelBoundary K A
  have hD : IsOpen D := Sec7.Lemma71F.isOpen_cayley_image c.dom.isOpen hc.dom_subset
  have hψ := isConformalBijection_comp
    (Sec7.Lemma71F.isConformalBijection_cayley_image hc.dom_subset) hc.isConformalBijection
  obtain ⟨hEc, hEu, hEb⟩ := retainedModelBoundary_properties hK hKH hKu hA hAH hAu
  have hcar : QuantumZipper.CA.Car.CarHyp (cayley ∘ c.2.1) D E 1 := by
    refine ⟨hψ.1, hψ.2, hD, Sec7.Lemma71F.cayley_image_subset_ball hc.dom_subset, hEc.isClosed,
      ?_, ?_, hEb⟩
    · dsimp only [D, E]
      rw [hdom]
      exact frontier_retainedModel_subset hK hA hAH hb
    · intro z hz hzD
      exact (retainedModelBoundary_disjoint hKH hAH b).le_bot
        ⟨hz, by simpa only [← hdom] using hzD⟩
  obtain ⟨F, hFeq, hFc, hFfr, -⟩ := QuantumZipper.CA.Car.continuousOn_extension hcar hEu
  have himg : F '' H = D := (image_congr fun _ hz => hFeq hz).trans hψ.2.image_eq
  refine ⟨F, hFeq, hFc, hψ.1.congr hFeq, ?_, ?_⟩
  · intro z hz w hw he
    exact hψ.2.injOn hz hw ((hFeq hz).symm.trans (he.trans (hFeq hw)))
  · intro z hz0 hzD
    have he : (z.re : ℂ) = z := Complex.ext rfl (by simp [hz0])
    have hfr := hFfr z.re
    rw [he, hD.frontier_eq] at hfr
    exact hfr.2 (himg ▸ hzD)

end InteractingSLE.Sec5.Aux61GInst
