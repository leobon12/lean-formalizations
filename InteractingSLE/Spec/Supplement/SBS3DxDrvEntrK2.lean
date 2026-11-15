/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEntrK2
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxDrvAssemble
import InteractingSLE.Spec.Supplement.SBS3DxDrvEntrance
import InteractingSLE.Spec.Supplement.SBS3DxDrvHint
import InteractingSLE.Spec.Supplement.SBS3DxKAmb
import InteractingSLE.Spec.Supplement.SBS3DxKSplit
import InteractingSLE.Spec.Supplement.SBS3DxSBLuAmb
import InteractingSLE.Spec.Supplement.SBS3DxSBLuWire
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2DrvEntrK2` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2DrvEntrK2` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2EntranceLinesLeStatement`;
* `sb2EntranceK2NStatement_of_linesLe`;
* `sb2DriverLinkAmbStatement_of_linesLe`;
* `sb2EntranceK2NStatement_of_lineDataLe`;
* `sb2DriverLinkAmbStatement_of_lineDataLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal

/-- **Named input: K2's line data in the concrete entrance σ-algebra** (supplement pp. 631–633: physical time lines
from `T_L`, the version of the relative driver, the generating trace and remainder link, the lifetime
reconstruction), for the entrance σ-algebra `D.marks` and live event `D.event` of every entrance construction `D`. -/
def SB2EntranceLinesLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ),
      D.marks ≤ 𝓗 0 ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      (∀ w ∈ I.types,
        HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ ψ I.word D.event w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P 𝓗 (seedCell κ ψ I.word D.event w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))) ∧
      ∃ Vg : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
            IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
              (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
              (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)) ∧
        ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          ω ∈ wordTypeCell κ ψ I.word D.event w →
          Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- **`SB2EntranceK2NLeStatement` from the line data**: (E1) and (E2) are proved (Theorems 1.2–1.3 and the geometric
input `SB2ErasedAvoidStatement`). -/
theorem sb2EntranceK2NStatement_of_linesLe (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hgeo : SB2ErasedAvoidStatement.{u}) (hL : SB2EntranceLinesLeStatement.{u}) : SB2EntranceK2NLeStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h E k u ψ η ζ HP _ I
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension HP.boundary
  obtain ⟨D⟩ := exists_entranceUnion h12p HP u₀ hu₀
  obtain ⟨𝓗, W, Γ, h𝓗, hW0, hWc, hWa, hK2, Vg, hl, hlf⟩ := hL κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D
  refine ⟨⟨D.marks, D.marks_le HP⟩, D.event, 𝓗, W, Γ, D.past_le_marks, h𝓗, D.measurableSet_event HP,
    D.event_subset, ?_, ?_, hW0, hWc, hWa, hK2, Vg, hl, hlf⟩
  · filter_upwards [D.ae_mem_event_iff] with ω hω hlω hT
    exact (hω hlω).2 hT
  · filter_upwards [ae_erasure hgeo h12p h13 HP I hu₀ D] with ω₀ h₀ hF
    exact h₀ (D.event_subset hF)

/-- **SB2(1)'s ambient driver link from Theorems 1.2–1.3, the erasure geometry and the line data.** -/
theorem sb2DriverLinkAmbStatement_of_linesLe (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hgeo : SB2ErasedAvoidStatement.{u}) (hL : SB2EntranceLinesLeStatement.{u}) :
    SB2DriverLinkAmbLeStatement.{u} :=
  sb2DriverLinkAmbStatement_of_entranceK2NLe h12p h13 (sb2EntranceK2NStatement_of_linesLe h12p h13 hgeo hL)

/-- **`SB2EntranceK2NLeStatement` from Theorems 1.2–1.3 and the line data alone.** -/
theorem sb2EntranceK2NStatement_of_lineDataLe (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hL : SB2EntranceLinesLeStatement.{u}) : SB2EntranceK2NLeStatement.{u} :=
  sb2EntranceK2NStatement_of_linesLe h12p h13 sb2ErasedAvoidStatement hL

/-- **SB2(1)'s ambient driver link from Theorems 1.2–1.3 and the line data alone.** -/
theorem sb2DriverLinkAmbStatement_of_lineDataLe (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hL : SB2EntranceLinesLeStatement.{u}) : SB2DriverLinkAmbLeStatement.{u} :=
  sb2DriverLinkAmbStatement_of_linesLe h12p h13 sb2ErasedAvoidStatement hL

end InteractingSLE.Theorem14.SB.Lv
