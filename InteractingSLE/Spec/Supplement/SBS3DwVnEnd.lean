/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VnEnd
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVnTr
import InteractingSLE.Spec.Supplement.SB2VnTr
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwViRed
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkAsm
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SBS3DwVkLife
import InteractingSLE.Spec.Supplement.SBS3DwVkLink
import InteractingSLE.Spec.Supplement.SBS3DwVmAd
import InteractingSLE.Spec.Supplement.SBS3DwVmSafe

/-!
# Successor of `SB2VnEnd` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VnEnd` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_relEndpoint_of_identifiedLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vn

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **Steps 1 and 2: the relative endpoint after the identification.** Almost surely at a launch on the entrance
event, if the driven family's canonical driver agrees before its lifetime with a continuous canonical driver `Wc` from
`0` whose generating trace is continuous on `[0, ζc]`, `capLife ρ ≤ ζc`, then a finite `capLife ρ` forces `ζ < ∞`,
and the canonical driver and the capacity trace converge at `capLife ρ`. -/
theorem ae_relEndpoint_of_identifiedLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      IsDrivenCurve (ρ ω) → ∀ (Wc : ℝ≥0 → ℝ) (ηc : ℝ≥0 → ℂ) (ζc : ℝ≥0∞), Continuous Wc → Wc 0 = 0 →
        IsGeneratingTrace Wc ζc ηc → capLife (ρ ω) ≤ ζc →
        (∀ q : ℝ≥0, (q : ℝ≥0∞) < capLife (ρ ω) → segDriver (ρ ω) q = Wc q) →
        capLife (ρ ω) ≠ ⊤ →
          ζ ω ≠ ⊤ ∧ Tendsto (segDriver (ρ ω)) (𝓝[<] (capLife (ρ ω)).toNNReal) (𝓝 (Wc (capLife (ρ ω)).toNNReal)) ∧
            Tendsto (capTrace (ρ ω)) (𝓝[<] (capLife (ρ ω)).toNNReal) (𝓝 (ηc (capLife (ρ ω)).toNNReal)) := by
  filter_upwards [ae_ne_top_of_capTrace_tendstoLe h13 hS3 HP hρ] with ω hfin hl hT hd Wc ηc ζc hWc hWc0 hηc hle hW
    hV
  have hgen : ∀ T : ℝ≥0∞, T < capLife (ρ ω) → IsGeneratingTrace (segDriver (ρ ω)) T (capTrace (ρ ω)) :=
    fun T hT => Sec5.CrossRestart.isGeneratingTrace_congr_drive (hd.isGeneratingTrace hT) fun _ _ => rfl
  obtain ⟨h1, h2⟩ := tendsto_of_eqOn_canonical (Vk.capLife_pos hd) hV hle hWc hWc0 hηc hW hgen
  exact ⟨hfin hl hT hd hV _ h2, h1, h2⟩

end

end InteractingSLE.Theorem14.SB.Vn
