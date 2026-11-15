/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ViRed
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SB2VgClock
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SB2VeAsm
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2ViRed` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2ViRed` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2DriverVersionLeStatement`;
* `sb2MeasVersionStatement_of_driverLe`;
* `sb2LineVersionRStatement_of_driverLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vi

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal Ve

/-- **Named input: the driver part of the measurable version** (see the module docstring). -/
def SB2DriverVersionLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (a : ℝ≥0 → Ω → ℝ≥0∞)
    (ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)),
    (∀ ω, Continuous fun t => a t ω) → (∀ ω, Monotone fun t => a t ω) → (∀ ω, a 0 ω = 0) →
    (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (flowLift κ b jumps E k u η ζ ω) (entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) →
    ∃ (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ) (Vg : Ω → ℝ≥0∞) (ηr : Ω → ℝ → ℂ),
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
      StronglyAdapted (Tc.tcFilt (D.lineFiltC HP) a ha) W ∧
      (∀ w ∈ I.types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[D.lineFiltC HP t]
        {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) ∧
      (∀ w ∈ I.types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[D.lineFiltC HP t]
        {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → entT κ b jumps E k u η ζ ω < ζ ω →
        IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
        IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω) ∧
        Vg ω = ⨆ (s : ℝ≥0) (_ : (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
          ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR (flowLift κ b jumps E k u η ζ ω)) s) ∧
        IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) (ηr ω) ∧
        ∀ s : ℝ≥0, (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          ηr ω (Sec7.Lemma71C.capClock (Vd.liftR (flowLift κ b jumps E k u η ζ ω)) s) =
            flowLift κ b jumps E k u η ζ ω s

/-- **The measurable version from its driver part** (the clock is `Vg.exists_versionClockLe`). -/
theorem sb2MeasVersionStatement_of_driverLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hDV : SB2DriverVersionLeStatement.{u}) :
    SB2MeasVersionLeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP _ I u₀ D
  obtain ⟨a, ha, hac, ham, ha0, hae⟩ := Vg.exists_versionClockLe h13 hS3 HP I D
  obtain ⟨W, Γ, Vg, ηr, hW0, hWc, hWad, hsS, hsL, hdr⟩ :=
    hDV κ b jumps P h E k u ψ η ζ HP I u₀ D a ha hac ham ha0 hae
  refine ⟨W, Γ, Vg, ηr, a, ha, hW0, hWc, hac, ham, ha0, hWad, hsS, hsL, ?_⟩
  filter_upwards [hdr, hae] with ω hd hc hF hT
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd hF hT
  exact ⟨h1, h2, hc hF hT, h3, h4, h5⟩

/-- **`SB2LineVersionRLeStatement` from Theorem 1.3, S3, E7 and the driver part.** -/
theorem sb2LineVersionRStatement_of_driverLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u})
    (hDV : SB2DriverVersionLeStatement.{u}) : SB2LineVersionRLeStatement.{u} :=
  sb2LineVersionRStatement_of_inputsLe h13 hS3 hE7 (sb2MeasVersionStatement_of_driverLe h13 hS3 hDV)

end InteractingSLE.Theorem14.SB.Vi
