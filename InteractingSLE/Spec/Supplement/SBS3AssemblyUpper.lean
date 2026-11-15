/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AssemblyData

/-!
# S3 assembly from protected canonical-word comparisons

This is a conditional assembly theorem with the unchanged `S3RegStatement`
conclusion. `RationalProtectedWordStatement` names the remaining source
construction, including the actual canonical label and marked mean identities.
It is not a proved theorem or a replacement for Lemma S3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

/-- **Named mathematical input, not discharged here.** For every fixed rational
compact common arc, construct the protected marked-mean data and identify the
unmarked canonical word value as a side height of the actual old schedule.
Both canonical phases are then proved from the data's transition-hull gaps.
In a source construction the distributional representatives must come from
the actual retained single and joint means; arbitrary harmonic functions are
not a substitute for establishing that construction. -/
def RationalProtectedWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ),
      l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) →
      ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
    ∀ q₁ q₂ : ℚ, ∀ᵐ ω ∂P,
      (∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
        schedulePrefix κ b jumps E l k ω = p '' Icc 0 1) →
      firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) <
        ((q₁ : ℝ).toNNReal : ℝ≥0∞) →
      (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
      ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ ω →
      β ω '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆
        schedulePrefix κ b jumps E l k ω ∩ H →
      ∃ d : ProtectedWordComparison κ (-sleLambda κ - ϑ * chiC κ)
        (schedulePrefix κ b jumps E l k ω) (β ω)
        (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal,
        Lh.SideH κ l (d.word.fn d.coordinate)

/-- The explicit protected-word construction supplies the earlier local
analytic interface. The harmonic comparison and both phase limits are proved
by the local assembly, rather than requested as four unexplained limits. -/
theorem rationalJointComparisonStatement_of_protectedWord
    (hW : RationalProtectedWordStatement.{u}) : RationalJointComparisonStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR l k ϑ hl hθ hϑ β ζ hβ hS1 q₁ q₂
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh E hE hR l k ϑ hl hθ hϑ β ζ hβ hS1 q₁ q₂]
    with ω hω
  intro hp hτ hq hζ hA
  obtain ⟨d, hlabel⟩ := hω hp hτ hq hζ hA
  exact d.hasJointSideComparison hlabel

/-- The unchanged upper S3 conclusion, with the remaining canonical-word and
marked-mean construction displayed as an explicit mathematical hypothesis. -/
theorem s3RegStatement_of_protectedWord (hW : RationalProtectedWordStatement.{u}) :
    S3RegStatement.{u} :=
  s3RegStatement_of_rationalJointComparison
    (rationalJointComparisonStatement_of_protectedWord hW)

end InteractingSLE.Theorem14.SB.S3
