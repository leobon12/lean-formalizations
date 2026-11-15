/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2TraceRead

/-!
# Sewing geometry calibrated to the actual launch boundary readout

The remaining frame records the actual lower tail and its map correspondence.
It does not assume an image containment for the new upper piece: that clause
is proved from the retained readout and the same conditional driver's trace.
Constructing this frame for the histories in SB4 remains open.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.Supp9B

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Leaf FlowDilate

/-- The remaining lower-tail frame, calibrated on the whole closed half-plane
to the retained launch readout `f`. This is an open geometric input, not a
provider. Its data do not depend on the new upper trace. -/
def RetainedTailFrame (f : ℂ → ℂ) (S Wrel : Set ℂ) (m : ℝ) : Prop :=
  ∃ (p : ℝ → ℂ) (β γ : ℝ≥0 → ℂ) (c : Chart) (g J : ℂ → ℂ) (tL : ℝ≥0),
    ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
    IsProperCurve β ∧ β 0 = 0 ∧ p '' Icc 0 1 ⊆ closedRightSide β ∧
    IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c ∧
    ContinuousOn g Hbar ∧ EqOn g c.2.1 H ∧
    β tL = realMin (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧
    (∀ s, g (γ s) = β (tL + s)) ∧
    (∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β) ∧
    m ≤ 0 ∧ range (reflectCurve γ) = Wrel ∧ Function.Injective J ∧
    (∀ z ∈ Hbar, f z = J (Supp9B.refl (g (Supp9B.refl (aff 1 m z))))) ∧
    S ⊆ J '' rightSideOf (range (reflectCurve β))

/-- The frame's map identity supplies the actual new-piece image clause,
including its terminal endpoint. The translated trace's seed and half-plane
containment follow from the generating trace itself. -/
theorem RetainedTailFrame.hasRelTailGeometry
    {f : ℂ → ℂ} {A S Wrel : Set ℂ} {m : ℝ} (hframe : RetainedTailFrame f S Wrel m)
    {W : ℝ≥0 → ℝ} {ζ T : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W ζ α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) < ζ})
    (hW0 : W 0 = 0) (hT : T ≤ ζ)
    (hA : A ⊆ f '' (α '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T})) :
    HasRelTailGeometry A S Wrel m (fun t => aff 1 m (α t)) ζ := by
  obtain ⟨p, β, γ, c, g, J, tL, hp, hp0, hpH, hβ, hβ0, hpR, hc,
    hgc, hgi, hentry, hγ, hγ0, htail, hfree, hm, hwalk, hJ, hmap, hS⟩ := hframe
  have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → α t ∈ Hbar :=
    fun t ht => Sec7.IsGeneratingTrace.mem_Hbar hα hW hW0 ht
  refine ⟨p, β, γ, c, g, J, tL, hp, hp0, hpH, hβ, hβ0, hpR, hc,
    hgc, hgi, hentry, hγ, hγ0, htail, hfree, hm, ?_, ?_, hwalk, hJ, ?_, hS⟩
  · simp only [aff, one_smul, hα.1, zero_add]
  · intro t ht
    have htH : 0 ≤ (α t).im := hH t ht
    simpa only [aff_im, one_mul] using htH
  · intro z hz
    obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hA hz
    refine ⟨_, ⟨_, ⟨_, ⟨_, ⟨t, ht.trans hT, rfl⟩, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    exact (hmap _ (hH t (ht.trans hT))).symm

/-- Under any actual conditional flow law, readout plus the remaining frame
give all S1-free relative geometry. The lifetime is the original driver's,
and the physical upper piece may stop earlier at its prescribed own time. -/
theorem ae_relTailGeometry_of_frame_readout
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {bc : ℝ → ℝ} {jc : Finset ℝ} {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hl : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ bc jc θ Q hl W ζ)
    {f : ℂ → ℂ} {A S Wrel : Ω → Set ℂ} {m : ℝ} {T : ℝ≥0∞}
    (hread : ∀ᵐ ω ∂Q, A ω ⊆ f '' (GW2aSingle.chosenTrace W ζ ω ''
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min T (ζ ω)}))
    (hframe : ∀ᵐ ω ∂Q, RetainedTailFrame f (S ω) (Wrel ω) m) :
    ∀ᵐ ω ∂Q, HasRelTailGeometry (A ω) (S ω) (Wrel ω) m
      (fun t => aff 1 m (GW2aSingle.chosenTrace W ζ ω t)) (ζ ω) := by
  filter_upwards [hread, hframe, GW2aSingle.ae_chosenTrace h13 hκ hfl,
    Supp8.GB6.ae_driver_zero_continuousOn hfl] with ω hr hf ht hW
  exact hf.hasRelTailGeometry ht.1 hW.2 hW.1 (min_le_right _ _) hr

end InteractingSLE.Theorem14.SB.Retain
