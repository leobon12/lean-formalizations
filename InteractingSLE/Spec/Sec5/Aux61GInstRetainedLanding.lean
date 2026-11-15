/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstSeedGap

/-! # Selected-access landing for the retained chart's physical first contact -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData
open WangWu (negInv)

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}

/-- The positive physical clearance at the restart supplies a seed gap.
The extension hypotheses are supplied by `boundedInverse_spec_of_traces`. -/
theorem exists_seed_gap_of_retainedGeometry
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) (hT0 : 0 < T x)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hstart : ρ x 0 ∈ H \ negInv '' fillH K)
    (heq : EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H)
    (hc : ContinuousOn (boundedInverse (c x)) Hbar) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary K := by
  apply exists_real_seed_gap hc (isCompact_oldModelBoundary hK hKH).isClosed
  rw [boundedInverse_zero_of_restartSpec hs hx hT0 heq hc]
  exact cayley_notMem_oldModelBoundary hKH hstart

/-- On a piece with a uniform free seed collar, physical first contact and
the actual retained chart imply the weaker landing condition. Its inputs
contain no forward-chart limit at a physical contact point. -/
theorem hasAccessLanding_of_retainedGeometry
    (hs : IsRestartSpec E c ρ T) {U : Set ℂ} (hUb : Bornology.IsBounded U) (δ : ℝ)
    (K A : X → Set ℂ) (b : X → ℂ)
    (hK : ∀ x ∈ E, IsCompact (K x)) (hKH : ∀ x ∈ E, K x ⊆ Hbar)
    (hdom : ∀ x ∈ E, ((c x).dom : Set ℂ) =
      connectedComponentIn ((H \ negInv '' fillH (K x)) \ A x) (b x))
    (hF : ∀ x ∈ E,
      EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H ∧
      ContinuousOn (boundedInverse (c x)) Hbar ∧
      DifferentiableOn ℂ (boundedInverse (c x)) H ∧ InjOn (boundedInverse (c x)) H ∧
      ∀ z : ℂ, z.im = 0 → boundedInverse (c x) z ∉ boundedInverse (c x) '' H)
    (hseed : ∀ x ∈ E, ∀ a : ℝ, |a| < δ →
      boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary (K x))
    (hcontact : ∀ x ∈ E, 0 < T x → T x < ⊤ →
      ρ x (T x).toNNReal ∉ H \ negInv '' fillH (K x)) :
    HasAccessLanding E c ρ T (seedExitWindow U δ) := by
  apply hasAccessLanding_on_seedExitWindow hs hUb δ hF (fun x => oldModelBoundary (K x)) hseed
  · intro x hx
    rw [Set.disjoint_left]
    rintro w ⟨z, hz, rfl⟩ hw
    rw [(hF x hx).1 hz] at hw
    apply cayley_notMem_oldModelBoundary (hKH x hx) _ hw
    have hm := (hs.conf x hx).inv_mem_dom hz
    change (c x).2.1 z ∈ ((c x).dom : Set ℂ) at hm
    rw [hdom x hx] at hm
    exact (connectedComponentIn_subset _ _ hm).1
  · intro x hx hT0 hTfin
    have hxev : x ∈ exitEv E c ρ T (seedExitWindow U δ) :=
      ⟨⟨hx, hT0⟩, (IsRestartSpec.exitTime_le x).trans_lt hTfin⟩
    have hcl := hs.mem_closure_at_T hxev hTfin
    have hsub : ((c x).dom : Set ℂ) ⊆ H \ negInv '' fillH (K x) := by
      rw [hdom x hx]
      exact (connectedComponentIn_subset _ _).trans sdiff_subset
    have hUo : IsOpen (H \ negInv '' fillH (K x)) := by
      rw [WangWu.H_diff_image_negInv]
      exact WangWu.isOpen_image_negInv (isOpen_H_diff_fillH (hK x hx).isBounded) sdiff_subset
    apply cayley_mem_oldModelBoundary_of_frontier (hK x hx)
    rw [hUo.frontier_eq]
    exact ⟨closure_mono hsub hcl, hcontact x hx hT0 hTfin⟩

omit [MeasurableSpace X] in
/-- A finite closed-set hitting time is attained at that very time. -/
theorem mem_at_finite_hitTime {F : X → Set ℂ} {x : X}
    (hc : Continuous (ρ x)) (hF : IsClosed (F x))
    (hT : T x = hitTime ρ F x) (hfin : T x < ⊤) : ρ x (T x).toNNReal ∈ F x := by
  have he : ((T x).toNNReal : ℝ≥0∞) = T x := ENNReal.coe_toNNReal hfin.ne
  obtain ⟨u, hu, huF⟩ := (hitTime_le_iff hc hF (T x).toNNReal).1 (by rw [he, ← hT])
  have hTu : T x ≤ (u : ℝ≥0∞) := hT ▸ iInf₂_le u huF
  have hue : u = (T x).toNNReal := by
    apply ENNReal.coe_injective
    exact le_antisymm hu (he ▸ hTu)
  rwa [hue] at huF

end InteractingSLE.Sec5.Aux61GInst
