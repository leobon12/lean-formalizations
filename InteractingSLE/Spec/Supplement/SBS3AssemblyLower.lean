/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AssemblyReflect
import InteractingSLE.Spec.Supplement.SB2LkS3

/-!
# S3 assembly for SB2(2)'s ordinary lower pieces

The strict height contradiction is the reflection of upper S3. The physical
curve here is exactly the boundary readout of the lower piece's launch chart,
and every countable intersection takes place under the retained upper kernel.
The protected-word construction remains an explicit named hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist.Staged Exist.StagedLaw Lu LuM

/-- The exact physical boundary readout used by
`Lk.SB2LowerNoCommonArcStatement`, with no time or lifetime truncation added. -/
def lowerOrdinaryPiece {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) : ℝ≥0 → ℂ :=
  fun t => bdVal (stChart (ExplState.run κ b jumps
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) j))
    (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) t)

/-- Whether that ordinary lower piece launches in the actual run. -/
def lowerOrdinaryLaunched {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) : Prop :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
    (j + 1)).2.2.2.1 j ≠ none

/-- **Named mathematical input, not discharged here.** The marked comparison
on each rational compact common arc of an actual charted lower piece, under
the retained upper kernel. The old word must have an upper-schedule label;
the exposed second value is the right height of angle `-π/2`. Construction
of the actual canonical word, marked means and transition gaps is required.
The claim is local to launched pieces and uses their full original lifetime,
matching the source consumer exactly. -/
def LowerRationalProtectedWordStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
    ∀ q₁ q₂ : ℚ,
      ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ j : ℕ, lowerOrdinaryLaunched κ b jumps E j ω →
        (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
        ((q₂ : ℝ).toNNReal : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2 →
        lowerOrdinaryPiece κ b jumps E j ω ''
          Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ upperPrefix κ b jumps E u l k ω₀ →
        ∃ d : ProtectedWordComparison κ (sleLambda κ - (-(Real.pi / 2)) * chiC κ)
          (upperPrefix κ b jumps E u l k ω₀) (lowerOrdinaryPiece κ b jumps E j ω)
          (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal,
          Lh.SideH κ l (d.word.fn d.coordinate)

/-- The unchanged reflected S3 consumer, conditional on the explicit local
canonical-word construction. The strict sign comparison and the countable
rational-to-all-interval passage under each retained kernel are discharged. -/
theorem sb2LowerNoCommonArcStatement_of_protectedWord
    (hW : LowerRationalProtectedWordStatement.{u}) : Lk.SB2LowerNoCommonArcStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER
    u l k hu hl hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact ae_no_common_arc_lower_of_protectedWord hκ hκ4
    (fun p hp => (hlθ p hp).1) (h₀ c θ hlaunch b' J' h' hb' hT' hG')

end InteractingSLE.Theorem14.SB.S3
