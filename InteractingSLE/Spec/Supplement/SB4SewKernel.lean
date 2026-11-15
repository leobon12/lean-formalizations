/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewCompare
import InteractingSLE.Spec.Supplement.SB4SwitchRegularity

/-!
# Conditional sewing from an actual retained tail

The data below record a reflected entry chart, the complete actual lower tail,
and the relative finite-prefix comparisons. Physical side correspondence is
proved from S5, rather than assumed as a certificate field. The existence of
these data for arbitrary staged histories remains a named open construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

universe u

namespace InteractingSLE.Theorem14.SB

/-- Geometric retained-tail data for one new physical piece. The outer injective
map permits either orientation of the original physical comparison. This is
data to be constructed, and is not asserted for arbitrary staged histories. -/
def HasActualTailSewing (A S : Set ℂ) : Prop :=
  ∃ (p : ℝ → ℂ) (β γ η : ℝ≥0 → ℂ) (c : Chart) (g J : ℂ → ℂ)
    (tL : ℝ≥0) (ζ : ℝ≥0∞) (u : ℝ),
    ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
    IsProperCurve β ∧ β 0 = 0 ∧ p '' Icc 0 1 ⊆ closedRightSide β ∧
    IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c ∧
    ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g c.2.1 H ∧
    β tL = realMin (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧
    (∀ s, g (γ s) = β (tL + s)) ∧
    (∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β) ∧
    u ≤ 0 ∧ η 0 = u ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → 0 ≤ (η t).im) ∧
    (∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
      IsOneSided (reflectCurve γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) η a) ∧
    Function.Injective J ∧
    A ⊆ J '' (Supp9B.refl '' (g '' (Supp9B.refl '' (η '' {t | (t : ℝ≥0∞) ≤ ζ})))) ∧
    S ⊆ J '' rightSideOf (range (reflectCurve β))

/-- All relative finite-prefix comparisons sew to avoidance of the actual
physical forbidden side. Real contacts are included by closed-side transport. -/
theorem HasActualTailSewing.avoids {A S : Set ℂ} (h : HasActualTailSewing A S) :
    A ∩ S = ∅ := by
  obtain ⟨p, β, γ, η, c, g, J, tL, ζ, u, hp, hp0, hpH, hβ, hβ0, hA,
    hc, hgc, hgi, hentry, hγ, hγ0, htail, hfree, hu, hη0, hηH, hS1, hJ, hnew, hS⟩ := h
  have hside := image_available_subset_closedRightSide_of_actual_tail
    hp hp0 hpH hβ hβ0 hA hc hgc hgi hentry hγ hγ0 htail hfree hu hη0 hηH hS1
  have hβr := isProperCurve_reflectCurve hβ
  have hβr0 : reflectCurve β 0 = 0 := by
    simp only [reflectCurve, hβ0, Supp9B.refl, map_zero, neg_zero]
  refine eq_empty_of_forall_notMem ?_
  rintro z ⟨hzA, hzS⟩
  obtain ⟨_, ⟨w, hw, rfl⟩, hz⟩ := hnew hzA
  obtain ⟨v, hv, hvz⟩ := hS hzS
  have hvw : v = Supp9B.refl w := hJ (hvz.trans hz.symm)
  have hR := rightSideOf_range_subset_rightSide hβr hβr0 (hvw ▸ hv)
  have hclosed : Supp9B.refl w ∈ closedLeftSide (reflectCurve β) := by
    rcases hside hw with hwR | hwS
    · exact Or.inl (refl_image_rightSide_subset hβ.2.2.1
        (by rw [hβ0]; rfl) ⟨w, hwR, rfl⟩)
    · exact Or.inr (refl_image_seedRayClosure_subset β ⟨w, hwS, rfl⟩)
  rcases hclosed with hL | hcurve
  · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hβr
      (by rw [hβr0]; rfl)) hL hR
  · exact connectedComponentIn_subset _ _ hR hcurve

/-- The still-required retained conditional construction for a physical piece.
Measurable rational incidence and the actual launch event are explicit. -/
def HasConditionalActualTailSewing {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Set Ω) (A S : Ω → Set ℂ) : Prop :=
  ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (a : Ω → ℝ≥0 → ℂ),
    NullMeasurableSet F P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀),
      ω ∈ F → HasActualTailSewing (A ω) (S ω)

/-- Lift actual-tail sewing through the conditional kernel using the existing
null-measurable continuous-piece event, with no new measurability premise. -/
theorem ae_piece_avoids_of_conditionalActualTailSewing {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Set Ω} {A S : Ω → Set ℂ}
    (h : HasConditionalActualTailSewing P F A S) :
    ∀ᵐ ω ∂P, ω ∈ F → A ω ∩ S ω = ∅ := by
  obtain ⟨𝒢, a, hF, hm, hreg, hsew⟩ := h
  apply ae_of_ae_condExpKernel_of_nullMeasurableSet 𝒢.2
    (nullMeasurableSet_piece_avoidance hF hm hreg)
  filter_upwards [hsew] with ω₀ hω₀
  exact hω₀.mono fun ω hω hωF => (hω hωF).avoids

/-- The precise local construction needed at each actual schedule switch.
This is an open input, not a proved property of staged histories. -/
def ScheduleActualTailSewing {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (P : Measure Ω) [IsFiniteMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasConditionalActualTailSewing P
      {ω | (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k ≠ none}
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

/-- The local construction suffices for the unchanged one-piece switch target. -/
theorem scheduleStepAvoidance_of_actualTailSewing {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {x : ℝ} {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (h : ScheduleActualTailSewing κ b jumps P E x l S) :
    ScheduleStepAvoidance κ b jumps P E x l S :=
  fun k hk hprev => ae_piece_avoids_of_conditionalActualTailSewing (h k hk hprev)

end InteractingSLE.Theorem14.SB
