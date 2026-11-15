/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIface

/-!
# SB2(1)'s version half: the lifetime reconstruction (E7) and force regularity

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108).

* **`SB2RemainderLifeStatement`** (named input, the source step E7, supplement pp. 631–633: "the remainder runs until
  the launch word's continuation threshold"): almost surely on every admissible type cell, every relative driver
  generating the remainder (`IsGeneratingTrace` up to `Vg`, linked to the actual remainder by `IsRemainderLink`) has
  the force-word threshold of the launch word's type as its lifetime: `Vg = FCDet.thr …` (on the whole type cell of
  the entrance event; in particular the seed is a.s. not at its threshold there). The threshold depends only
  on the driver up to the threshold, and the threshold condition holds at the lifetime by continuity, so the
  statement does not depend on how the driver continues after `Vg`.
* `life_of_remainderLife`: the interface's `life` field (exact form) for any version data with continuous drivers
  from `0` and the remainder link (the interface's `link` field).
* `reg_of_continuous`: the interface's `reg` field (`FCDet.isForceReg_thr`), at every sample.

**R48.** Serves Theorem 1.4 only.
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
def SB2RemainderLifeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
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
theorem life_of_remainderLife (hE7 : SB2RemainderLifeStatement.{u}) {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
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

/-- **The `reg` field at every sample** (`FCDet.isForceReg_thr`). -/
theorem reg_of_continuous {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    Aux79.IsForceReg W (geomLW W xL) (geomRW W xR) (FCDet.thr ρL ρR W xL xR) ω :=
  FCDet.isForceReg_thr hW0 hWc xL xR _ ω

end InteractingSLE.Theorem14.SB.Vh
