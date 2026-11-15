/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkEnd
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVkLife
import InteractingSLE.Spec.Supplement.SB2VkLife
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkFam

/-!
# Successor of `SB2VkEnd` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VkEnd` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2RelEndpointLeStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **Named input: SB2(1)'s relative endpoint.** Almost surely at a launch on the entrance event, if the relative
lifetime of the flow's lift is finite, then the physical remainder is finite, and every driver `W`, continuous from `0`
before the relative lifetime, whose generating trace `Γ` reads the lift in its capacity clock, converges at the
relative lifetime together with `Γ`. -/
def SB2RelEndpointLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    SB2LaunchProblem κ b jumps P h E k u ψ η ζ → ∀ [Fact (ψ ≤ Real.pi / 2)],
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      relLife κ b jumps E k u η ζ ω ≠ ⊤ → ζ ω ≠ ⊤ ∧
      ∀ (W : ℝ≥0 → ℝ) (Γ : ℝ≥0 → ℂ), W 0 = 0 →
        ContinuousOn W {t | (t : ℝ≥0∞) < relLife κ b jumps E k u η ζ ω} →
        (∀ T : ℝ≥0∞, T < relLife κ b jumps E k u η ζ ω → IsGeneratingTrace W T Γ) →
        (∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          Γ (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s).toNNReal =
            Ve.flowLift κ b jumps E k u η ζ ω s) →
        ∃ (x : ℝ) (z : ℂ), Tendsto W (𝓝[<] (relLife κ b jumps E k u η ζ ω).toNNReal) (𝓝 x) ∧
          Tendsto Γ (𝓝[<] (relLife κ b jumps E k u η ζ ω).toNNReal) (𝓝 z)

/-! ### Freezing at the lifetime -/

section Freeze

variable {X : Type*} [TopologicalSpace X] [Nonempty X]

end Freeze

section Trace

variable {W : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} {V : ℝ≥0∞}

end Trace

end InteractingSLE.Theorem14.SB.Vk
