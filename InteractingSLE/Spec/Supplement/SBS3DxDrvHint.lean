/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvHint
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxDrvAssemble
import InteractingSLE.Spec.Supplement.SBS3DxDrvEntrance
import InteractingSLE.Spec.Supplement.SBS3DxKAmb
import InteractingSLE.Spec.Supplement.SBS3DxKSplit
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2DrvHint` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2DrvHint` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2EntranceK2NLeStatement`;
* `sb2EntranceK2Statement_of_NLe`;
* `sb2DriverLinkAmbStatement_of_entranceK2NLe`.
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

/-! ### Values of stop words -/

section StopWord

variable {κ : ℝ}

end StopWord

/-! ### Uniformly bounded stage witnesses -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

end Stage

/-! ### The bounded conditional chart field and the integrability of its pairings -/

section Chart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

end Chart

/-! ### The named inputs without their integrability clause -/

/-- **Named input, route A, without (E4)**: `SB2EntranceK2LeStatement` with its integrability clause dropped (it is
proved, `integrableOn_chartPairing`). -/
def SB2EntranceK2NLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∃ (𝒢' : {m : MeasurableSpace Ω // m ≤ mΩ}) (F' : Set Ω) (𝓗 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ),
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ 𝒢'.1 ∧
      𝒢'.1 ≤ 𝓗 0 ∧ MeasurableSet[𝒢'.1] F' ∧ F' ⊆ launchSet κ b jumps E (k + 1) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω → ω ∈ F') ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ F' → ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (I.chart ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢'.1 ω₀) h' (I.word ω₀).fn (I.word ω₀).jumps) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      (∀ w ∈ I.types,
        HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ ψ I.word F' w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P 𝓗 (seedCell κ ψ I.word F' w)
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
          ω ∈ wordTypeCell κ ψ I.word F' w →
          Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- Route A without (E4) gives route A: the integrability clause on `F' ⊆ launchSet` from
`integrableOn_chartPairing`. -/
theorem sb2EntranceK2Statement_of_NLe (hN : SB2EntranceK2NLeStatement.{u}) : SB2EntranceK2LeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ H _ I
  obtain ⟨G', F', 𝓗, W, Γ, h1, h2, h3, h4, h5, h6, hW0, hWc, hWa, hK2, Vg, hl, hlf⟩ :=
    hN κ b jumps P h E k u ψ η ζ H I
  exact ⟨G', F', 𝓗, W, Γ, h1, h2, h3, h4, h5, h6, hW0, hWc, hWa,
    fun φ => (integrableOn_chartPairing H I φ).mono_set h4, hK2, Vg, hl, hlf⟩

/-- **SB2(1)'s clauses (1) and (3) at the launches after the first from Theorems 1.2–1.3 and route A without
(E4).** -/
theorem sb2DriverLinkAmbStatement_of_entranceK2NLe (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hN : SB2EntranceK2NLeStatement.{u}) :
    SB2DriverLinkAmbLeStatement.{u} :=
  sb2DriverLinkAmbStatement_of_entranceK2Le h12p h13 (sb2EntranceK2Statement_of_NLe hN)

end InteractingSLE.Theorem14.SB.Lv
