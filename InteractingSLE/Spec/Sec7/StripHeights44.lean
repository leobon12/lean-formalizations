/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowPocket
import InteractingSLE.Spec.Sec7.StripSys

/-!
# Carrying the (4.4) height bounds with strip data

Ruling R56: `IsStripSystem` records the staged histories but not the (4.4) height bounds needed by the R48-safe
determination of the two pieces. This file adds a wrapper carrying those bounds and proves them for the source's
four-height choice in Aux. lemma 130.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Sec7.StripHeights44

/-- The (4.4) boundary-height inequalities at one angle. -/
def IsHeightBounded44 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) : Prop :=
  (∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ) ∧
  (∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ)

/-- The height bounds required at both angles of the two-piece strip history. -/
structure StripHeightBounds44 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ θ : ℝ) : Prop where
  atStart : IsHeightBounded44 κ b jumps θ₀
  atFinish : IsHeightBounded44 κ b jumps θ

/-- Strip data equipped with the two (4.4) height bounds and angles in the source interval. -/
structure IsStripSystemWithHeights44 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (θ₀ θ : ℝ) : Prop where
  system : StripSys.IsStripSystem κ b jumps P h W' ζ' E
  startAngle_mem : θ₀ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  finishAngle_mem : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  heights : StripHeightBounds44 κ b jumps θ₀ θ

/-- The four source heights of Aux. lemma 130, with its sufficient lower bounds. -/
structure Aux130SourceHeights (κ : ℝ) where
  a : ℝ
  b : ℝ
  aUpper : ℝ
  bUpper : ℝ
  a_lower : sleLambda κ + Real.pi * chiC κ / 2 ≤ a
  b_lower : sleLambda κ + Real.pi * chiC κ / 2 ≤ b
  aUpper_lower : sleLambda κ + 3 * Real.pi * chiC κ / 2 ≤ aUpper
  bUpper_lower : sleLambda κ + 3 * Real.pi * chiC κ / 2 ≤ bUpper

/-- The four-level half-plane boundary word associated with the chosen strip heights. -/
def IsAux130HalfPlaneWord {κ : ℝ} (H : Aux130SourceHeights κ) (B : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  (∀ y : ℝ, y < 0 → y ∉ jumps → B y = -H.a ∨ B y = -H.aUpper) ∧
  (∀ y : ℝ, 0 < y → y ∉ jumps → B y = H.b ∨ B y = H.bUpper)

namespace Aux130SourceHeights

/-- Reuse Aux. lemma 130's checked computation of the four nonnegative cumulative force values. -/
theorem cumulative_nonneg {κ θ : ℝ} (H : Aux130SourceHeights κ) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ (H.a - θ * chiC κ) / sleLambda κ - 1 ∧
      0 ≤ (H.b + θ * chiC κ) / sleLambda κ - 1 ∧
      0 ≤ (H.aUpper - (θ + Real.pi) * chiC κ) / sleLambda κ - 1 ∧
      0 ≤ (H.bUpper + (θ - Real.pi) * chiC κ) / sleLambda κ - 1 := by
  exact (Sec7.aux130_heights hκ hκ4 hθ H.a_lower H.b_lower H.aUpper_lower H.bUpper_lower).1

end Aux130SourceHeights

/-- Aux. lemma 130's chosen four heights give (4.4) at every angle in `[-π/2, π/2]`. -/
theorem IsAux130HalfPlaneWord.heightBounds44 {κ θ : ℝ} (H : Aux130SourceHeights κ) {B : ℝ → ℝ}
    {jumps : Finset ℝ} (hword : IsAux130HalfPlaneWord H B jumps) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) : IsHeightBounded44 κ B jumps θ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ Real.pi * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hθhi : θ * chiC κ ≤ (Real.pi / 2) * chiC κ :=
    mul_le_mul_of_nonneg_right hθ.2 hχ.le
  have hθlo : -(Real.pi / 2) * chiC κ ≤ θ * chiC κ :=
    mul_le_mul_of_nonneg_right hθ.1 hχ.le
  refine ⟨?_, ?_⟩
  · intro y hy hyJ
    rcases hword.1 y hy hyJ with hyA | hyA'
    · rw [hyA]
      nlinarith [H.a_lower]
    · rw [hyA']
      nlinarith [H.aUpper_lower]
  · intro y hy hyJ
    rcases hword.2 y hy hyJ with hyB | hyB'
    · rw [hyB]
      nlinarith [H.b_lower]
    · rw [hyB']
      nlinarith [H.bUpper_lower]

/-- Attach the source's four-height choice to an existing strip system. -/
theorem isStripSystemWithHeights44_of_aux130 {κ : ℝ} {B : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ B jumps P h W' ζ' E)
    (H : Aux130SourceHeights κ) (hword : IsAux130HalfPlaneWord H B jumps) (hκ4 : κ < 4)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    IsStripSystemWithHeights44 κ B jumps P h W' ζ' E θ₀ θ := by
  exact ⟨hS, hθ₀, hθ,
    ⟨IsAux130HalfPlaneWord.heightBounds44 H hword hS.kappa_pos hκ4 hθ₀,
      IsAux130HalfPlaneWord.heightBounds44 H hword hS.kappa_pos hκ4 hθ⟩⟩

end InteractingSLE.Sec7.StripHeights44

end
