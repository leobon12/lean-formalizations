/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcRec

/-!
# Lemma S3 in SB2(1)'s form for upper angles `ψ ≤ π/2` (decision D22, ruling R121): the statement

Worker PROVE-R6-CORNER (round 8). Decision D22 (`planning/reviews/DECISIONS-FABLE-4.md`): SB2(1) and SB3 are applied
only to schedule angles in `(−π/2, π/2]`, so the bound `ψ ≤ π/2` is threaded through SB2(1)'s statements and
`Tc.SB2EntranceNoCommonArcStatement` (all angles `ψ > −π/2`) is replaced by
**`Tc.SB2EntranceNoCommonArcLeStatement`**: the same conclusion for launch problems carrying the bound as an instance
argument `[Fact (ψ ≤ Real.pi / 2)]`. It is PROVED from Theorems 1.2–1.3 in `SBS3DwEntr`
(`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`, from `S3.Asm.ae_entranceNoCommonArc_of_le`).

The bound is an instance argument so that the successor copies of SB2(1)'s version half (`SBS3Dw*`) keep the original
proofs verbatim: every application `hS3 κ b jumps P h E k u ψ η ζ HP` synthesizes it from the local instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Tc

open Lv Exist.Staged Exist.StagedLaw

/-- **Lemma S3 in SB2(1)'s configuration, upper angles `ψ ≤ π/2`** (D22): `SB2EntranceNoCommonArcStatement` for launch
problems with the bound `ψ ≤ π/2` (an instance argument). -/
def SB2EntranceNoCommonArcLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    SB2LaunchProblem κ b jumps P h E k u ψ η ζ → ∀ [Fact (ψ ≤ Real.pi / 2)],
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      ∀ s₁ s₂ : ℝ≥0, firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ≤ s₁ → s₁ < s₂ →
        (s₂ : ℝ≥0∞) ≤ ζ ω → ¬ η ω '' Ioo s₁ s₂ ⊆ lowerPrefix κ b jumps E (k + 1) u ω

/-- The all-angle statement gives the bounded one. -/
theorem sb2EntranceNoCommonArcLeStatement_of_all (h : SB2EntranceNoCommonArcStatement.{u}) :
    SB2EntranceNoCommonArcLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h' E k u ψ η ζ HP _ => h κ b jumps P h' E k u ψ η ζ HP

end InteractingSLE.Theorem14.SB.Tc
