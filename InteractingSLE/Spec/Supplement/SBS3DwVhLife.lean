/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VhLife
import InteractingSLE.Spec.Supplement.SBS3DwBase

/-!
# Successor of `SB2VhLife` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VhLife` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2RemainderLifeLeStatement`;
* `life_of_remainderLifeLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vh

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal

/-- **Named input: the lifetime reconstruction E7** (SB2(1), supplement pp. 631–633). Almost surely at a launch, on
the entrance event and its type cell `w`, every relative driver `W` (continuous, from `0`) whose trace `Γ`
generates the remainder up to `Vg` and is linked to the actual upper flow after its entrance (`IsRemainderLink` in the
launch chart, read at the entry `m`) has lifetime `Vg` equal to the threshold of the launch word's force type `w`. -/
def SB2RemainderLifeLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (w : WordType), w ∈ I.types →
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      ω ∈ wordTypeCell κ ψ I.word D.event w →
      ∀ (W : ℝ≥0 → Ω → ℝ) (Vg : ℝ≥0∞) (Γ : ℝ≥0 → ℂ), Continuous (fun t => W t ω) → W 0 ω = 0 →
        IsGeneratingTrace (fun t => W t ω) Vg Γ →
        IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) (fun t => Γ t + launchEntry κ b jumps E (k + 1) u ω) Vg →
        Vg = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- **The `life` field from E7**: version data with continuous drivers from `0` whose traces generate the remainder
and are linked to it (the interface's `link` field) have the threshold as lifetime on every type cell. -/
theorem life_of_remainderLifeLe (hE7 : SB2RemainderLifeLeStatement.{u}) {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    {W : ℝ≥0 → Ω → ℝ} {Γ : Ω → ℝ≥0 → ℂ} {Vg : Ω → ℝ≥0∞} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hlink : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
        IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)) :
    ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      ω ∈ wordTypeCell κ ψ I.word D.event w →
      Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω := by
  intro w hw
  filter_upwards [hE7 κ b jumps P h E k u ψ η ζ HP I u₀ D w hw, hlink] with ω hE7ω hlinkω hl hT hcell
  obtain ⟨hgen, hrem⟩ := hlinkω hl hT
  exact hE7ω hl hT hcell W (Vg ω) (Γ ω) (hWc ω) (hW0 ω) hgen hrem

end InteractingSLE.Theorem14.SB.Vh
