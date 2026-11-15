/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathFst
import InteractingSLE.Spec.Supplement.AStopProcWire
import InteractingSLE.Spec.Supplement.AStopPartWire
import InteractingSLE.Spec.Supplement.OrdModelSeed
import InteractingSLE.Spec.Supplement.OrdFstWord

/-!
# `AStopSourceInputs` for both continuations: assembly of items 1–6

Packet PROVE-T15-ASTOP-PATH. Items 1 (PROVE-T15-ASTOP-PART: `AStopPart.exists_ordTypePartition_snd/_fst`), 2–3
(PROVE-T15-ASTOP-PROC: `AStopProc.exists_sndProcInputs`/`exists_fstProcInputs`) and 6 (this packet:
`ae_aStopPath_snd`/`ae_aStopPath_fst`) are proved. The assembly below takes two named statements:

* **`AStopSafeSndStatement`** / **`AStopSafeFstStatement`** (items 4–5 of `AStopSourceInputs`, packet ASTOP-SAFE):
  the integrable pairings and the stopped-K2 safe laws (S), (L) for the processes of PROVE-T15-ASTOP-PROC (their
  explicit forms are the statements' hypotheses);
* **`AStopTerminalSndStatement`** / **`AStopTerminalFstStatement`** (the terminal case of item 6, proved in
  `AStopPathTermWire`): when the A-stopped
  continuation runs to the flow line's own finite lifetime at a point off `A`, the relative continuation threshold
  holds at the capacity lifetime (Lemma G7: "a relative threshold there is also an original threshold", read in
  reverse: the original terminal threshold is a relative one). See the handoff for its reduction.

**`retOrdAStopSourceSndStatement_of_inputs`** and **`retOrdAStopSourceFstSeedStatement_of_inputs`** derive
`RLC.OrdModel.RetOrdAStopSourceSndStatement` and `RLC.RetOrdAStopSourceFstSeedStatement` from these and Lemma 7.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart Restart.RetAux79 PiecewiseConstantBoundaryData MartChar.RealFlow OrdModel AStopProc
open Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal Sec7.Lemma76F
open Exist.StagedLaw.BoundaryWord (shiftW)

universe u

/-! ### The named inputs -/

/-- **The terminal case of the A-stopped second continuation** (see the module docstring): almost surely
at an ordinary pair, if the second continuation runs to the flow line's own lifetime `ζ₂` at a point off
`A = η₁[0, u] ∪ η₂[0, r]` and its canonical capacity lifetime `V` is finite, then for every continuous driver `W` from
`0` generating the canonical path up to `V` and every force-type reading of an untouched retained word, the
continuation threshold condition holds at `V`. Proved: `aStopTerminalSndStatement` (`AStopPathTermWire`). -/
def AStopTerminalSndStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω), d.IsMeasGood →
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ c : Ω → BoundaryWord,
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (c ω) ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (c ω)) →
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      contStop (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = ζ₂ ω →
      η₂ ω (ζ₂ ω).toNNReal ∉ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r →
      ∀ W : ℝ≥0 → ℝ, Continuous W → W 0 = 0 →
      IsGeneratingTrace W
        (canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0) →
      canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≠ ⊤ →
      ∀ (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), c ω ∈ FCDet.typeSet κ θ₂ nL nR ρL ρR →
      ForceWord.ThresholdCondition ρL ρR
        (W (canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0).toNNReal)
        (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ₂ nL nR ρL ρR (c ω) i)
          (canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0).toNNReal)
        (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ₂ nL nR ρL ρR (c ω) j)
          (canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0).toNNReal)

/-- **The terminal case of the A-stopped first continuation** (as `AStopTerminalSndStatement` in the
chart translated by `tipPos`, for the seeded word `shiftW tipPos c` and the angle `θ₁`). Proved:
`aStopTerminalFstStatement` (`AStopPathTermWire`). -/
def AStopTerminalFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω), d.IsMeasGood →
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ c : Ω → BoundaryWord,
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (c ω) ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (c ω)) →
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      contStop (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = ζ₁ ω →
      η₁ ω (ζ₁ ω).toNNReal ∉ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r →
      ∀ W : ℝ≥0 → ℝ, Continuous W → W 0 = 0 →
      IsGeneratingTrace W
        (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω))
        (fun t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) t - tipPos d η₁ ω) →
      canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ≠ ⊤ →
      ∀ (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
        shiftW (tipPos d η₁ ω) (c ω) ∈ FCDet.typeSet κ θ₁ nL nR ρL ρR →
      ForceWord.ThresholdCondition ρL ρR
        (W (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω)).toNNReal)
        (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
          (-FCDet.typeXL κ θ₁ nL nR ρL ρR (shiftW (tipPos d η₁ ω) (c ω)) i)
          (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω)).toNNReal)
        (fun j => rightImg (fun s : ℝ => W s.toNNReal)
          (FCDet.typeXR κ θ₁ nL nR ρL ρR (shiftW (tipPos d η₁ ω) (c ω)) j)
          (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω)).toNNReal)

/-- **Items 4–5 of `AStopSourceInputs` for the second continuation** (named input, packet ASTOP-SAFE): on a
stop-line event of ordinary pairs with one force type, for PROVE-T15-ASTOP-PROC's time-changed filtration, stop and
driver (given by their explicit forms), the shifted chart-field pairings are integrable and the stopped-K2 safe laws
(S), (L) hold. **Not proved in Lean.** -/
def AStopSafeSndStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∀ M : Set Ω, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M →
      (∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) →
    ∀ a : ForceWordType, (∀ ω ∈ M, (β ω).1 ∈ FCDet.typeSet κ θ₂ a.nL a.nR a.rhoL a.rhoR) →
    ∀ η₂' : Ω → ℝ≥0 → ℂ, (∀ ω ∈ M, IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω) →
    ∀ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ),
      (∃ hQa, 𝓗 = aFilt (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (sndChart d η₂' ζ₂) hQa) →
      (∀ ω, Continuous (W · ω)) → (∀ ω, W 0 ω = 0) → StronglyAdapted 𝓗 W →
      (∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂)) ω →
        W q ω = aDriver (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) q ω) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω) φ) (P.restrict M)) ∧
      HasSafeLaw κ a.rhoL a.rhoR P 𝓗 M (M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂))) W
        (geomLW W fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1)
        (geomRW W fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1)
        (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω)) ∧
      HasSafeMembers P 𝓗 M (M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂))) W
        (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω))

/-- **Items 4–5 of `AStopSourceInputs` for the first continuation at its seed** (named input, packet ASTOP-SAFE; the
seed `τ = β.2`, the word `shiftW τ β.1`, the field `flowField τ 0 chartField`, angle `θ₁`). **Not proved in Lean.** -/
def AStopSafeFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∀ M : Set Ω, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M →
      (∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) →
    ∀ a : ForceWordType, (∀ ω ∈ M, shiftW (β ω).2 (β ω).1 ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR) →
    ∀ η₁' : Ω → ℝ≥0 → ℂ, (∀ ω ∈ M, IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ (fun ω => (β ω).2) ω) →
    ∀ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ),
      (∃ hQa, 𝓗 = aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M
        (fstChart d (fun ω => (β ω).2) η₁' ζ₁) hQa) →
      (∀ ω, Continuous (W · ω)) → (∀ ω, W 0 ω = 0) → StronglyAdapted 𝓗 W →
      (∀ ω (q : ℝ≥0), (q : ℝ≥0∞) <
          M.indicator (aLife (fstChart d (fun ω => (β ω).2) η₁' ζ₁) (fstLifeP d η₁' ζ₁)) ω →
        W q ω = aDriver (fstChart d (fun ω => (β ω).2) η₁' ζ₁) (fstLifeP d η₁' ζ₁) q ω) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => Exist.flowField 0 (θ₁ * chiC κ)
          (Exist.flowField (β ω).2 0 (hd.chartField κ h ω)) φ) (P.restrict M)) ∧
      HasSafeLaw κ a.rhoL a.rhoR P 𝓗 M
        (M.indicator (aLife (fstChart d (fun ω => (β ω).2) η₁' ζ₁) (fstLifeP d η₁' ζ₁))) W
        (geomLW W fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
        (geomRW W fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
        (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (Exist.flowField (β ω).2 0 (hd.chartField κ h ω))) ∧
      HasSafeMembers P 𝓗 M
        (M.indicator (aLife (fstChart d (fun ω => (β ω).2) η₁' ζ₁) (fstLifeP d η₁' ζ₁))) W
        (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (Exist.flowField (β ω).2 0 (hd.chartField κ h ω)))


/-! ### The assembly -/

/-- **The A-stopped second continuation's source inputs**, from Lemma 7.5, items 4–5 and the terminal case (items 1–3
and the rest of item 6 are proved: PROVE-T15-ASTOP-PART, PROVE-T15-ASTOP-PROC, `ae_aStopPath_snd`). -/
theorem retOrdAStopSourceSndStatement_of_inputs (hL75 : Theorem15.Lemma75Statement.{u})
    (hsafe : AStopSafeSndStatement.{u}) (hterm : AStopTerminalSndStatement.{u}) :
    RetOrdAStopSourceSndStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, a, M, hMσ, -, hcover, hMord, htype⟩ :=
    AStopPart.exists_ordTypePartition_snd hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hβ hmean hword
  have hP := fun i => AStopProc.exists_sndProcInputs hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag (hMσ i) (hMord i)
  choose M' hM'M hM'σ hMM' 𝓗 W E V' γ' h0 hWc hW0 hWa hV hγm hγc hγ0 hE hcan hgen hEq hrest using hP
  have hT := hterm κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag (fun ω => (β ω).1)
    (hword.mono fun ω hω ho => ⟨(hω ho).2.2.2.1, (hω ho).2.2.2.2⟩)
  refine ⟨n, M', fun i => retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r _ (hM'σ i), ?_, fun i _ => ?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ i, ω ∈ M i → ω ∈ M' i := ae_all_iff.2 hMM'
    filter_upwards [hcover, hall] with ω hc ha hord
    obtain ⟨i, hi⟩ := hc hord
    exact ⟨i, ha i hi⟩
  have hM'ord : ∀ᵐ ω ∂P, ω ∈ M' i → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
    filter_upwards [hMord i] with ω hω hω' using hω (hM'M i hω')
  have htype' : ∀ᵐ ω ∂P, ω ∈ M' i → (β ω).1 ∈ FCDet.typeSet κ θ₂ (a i).nL (a i).nR (a i).rhoL (a i).rhoR :=
    Eventually.of_forall fun ω hω => htype i ω (hM'M i hω)
  obtain ⟨hpos, hthr, havoid, hend⟩ := ae_aStopPath_snd hκ hκ4 hb hx hh hη₁ hη₂ hd hag hword hM'ord htype'
    (hWc i) (hW0 i) (hcan i) (hgen i) (hEq i)
  obtain ⟨η₂', hgood, h𝓗, hV', -, hWe⟩ := hrest i
  obtain ⟨hint, hS, hL⟩ := hsafe κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
    β hβ hmean hword (M' i) (hM'σ i) hM'ord (a i) (fun ω hω => htype i ω (hM'M i hω)) η₂' hgood (𝓗 i) (W i) h𝓗
    (hWc i) (hW0 i) (hWa i) (by rw [← hV']; exact hWe)
  rw [← hV'] at hS hL
  refine ⟨a i, 𝓗 i, W i, E i, V' i, γ' i, h0 i _ (hM'σ i), hβ.fst.mono (h0 i) le_rfl,
    hd.measurable_chartField κ hh.1, hWc i, hW0 i, hWa i, hV i, hγm i, hγc i, hγ0 i, hE i, measurable_const,
    hcan i, htype', hint, hS, hL, hgen i, hpos, hthr, havoid, ?_⟩
  filter_upwards [hend, hT, hcan i, hgen i, hM'ord, hthr] with ω h1 h2 h3 h4 h5 h6 hω hfin
  rcases h1 hω hfin with ⟨hstop, hoff⟩ | h1
  · left
    obtain ⟨hVe, hγe⟩ := h3 hω
    have hg := h4 hω
    rw [hVe] at hg
    have hg' := isGeneratingTrace_congr_le hg fun t ht => (hγe t ht).symm
    have hth := h2 (h5 hω) hstop hoff (W i · ω) (hWc i ω) (hW0 i ω) hg' (hVe ▸ hfin) _ _ _ _
      (htype i ω (hM'M i hω))
    refine le_antisymm (h6 hω) ?_
    have hle := FCPlumb.thr_le_of_force_threshold (hWc i) (ω := ω)
      (T := (V' i ω).toNNReal) (ρL := (a i).rhoL) (ρR := (a i).rhoR)
      (xL := fun ω => FCDet.typeXL κ θ₂ (a i).nL (a i).nR (a i).rhoL (a i).rhoR (β ω).1)
      (xR := fun ω => FCDet.typeXR κ θ₂ (a i).nL (a i).nR (a i).rhoL (a i).rhoR (β ω).1) (by rw [hVe]; exact hth)
    rwa [ENNReal.coe_toNNReal hfin] at hle
  · exact Or.inr h1


/-- **The A-stopped first continuation's seeded source inputs**, from Lemma 7.5, items 4–5 and the terminal case
(items 1–3 and the rest of item 6 are proved: PROVE-T15-ASTOP-PART, PROVE-T15-ASTOP-PROC, `ae_aStopPath_fst`). -/
theorem retOrdAStopSourceFstSeedStatement_of_inputs (hL75 : Theorem15.Lemma75Statement.{u})
    (hsafe : AStopSafeFstStatement.{u}) (hterm : AStopTerminalFstStatement.{u}) :
    RetOrdAStopSourceFstSeedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, a, M, hMσ, -, hcover, hMord, htype, -⟩ :=
    AStopPart.exists_ordTypePartition_fst hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hβ hmean hword
  have hτ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).2 = tipPos d η₁ ω :=
    hword.mono fun ω hω ho => (hω ho).2.1
  have hP := fun i => AStopProc.exists_fstProcInputs hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag (τ := fun ω => (β ω).2)
    hβ.snd hτ (hMσ i) (hMord i)
  choose M' hM'M hM'σ hMM' 𝓗 W E V' γ' h0 hWc hW0 hWa hV hγm hγc hγ0 hE hτm hcan hgen hEq hrest using hP
  have hsided := ae_isRetainedWordFst_of_meanIdent hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hmean
    (hword.mono fun ω hω ho => ⟨(hω ho).1, (hω ho).2.2.2.1⟩)
  have hfst : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (β ω).1 ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1 := by
    filter_upwards [hsided, hword] with ω h1 h2 ho using ⟨h1 ho, (h2 ho).2.2.2.2⟩
  have hT := hterm κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag (fun ω => (β ω).1) hfst
  have hβm : Measurable β := hβ.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r) le_rfl
  refine ⟨n, M', fun i => retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r _ (hM'σ i), ?_, fun i _ => ?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ i, ω ∈ M i → ω ∈ M' i := ae_all_iff.2 hMM'
    filter_upwards [hcover, hall] with ω hc ha hord
    obtain ⟨i, hi⟩ := hc hord
    exact ⟨i, ha i hi⟩
  have hM'ord : ∀ᵐ ω ∂P, ω ∈ M' i → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
    filter_upwards [hMord i] with ω hω hω' using hω (hM'M i hω')
  have hτM : ∀ᵐ ω ∂P, ω ∈ M' i → (β ω).2 = tipPos d η₁ ω := by
    filter_upwards [hM'ord, hτ] with ω h1 h2 hω using h2 (h1 hω)
  have htype' : ∀ᵐ ω ∂P, ω ∈ M' i →
      shiftW (β ω).2 (β ω).1 ∈ FCDet.typeSet κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR :=
    Eventually.of_forall fun ω hω => htype i ω (hM'M i hω)
  obtain ⟨hpos, hthr, havoid, hend⟩ := ae_aStopPath_fst hκ hκ4 hb hx hh hη₁ hη₂ hd hag hfst hM'ord hτM htype'
    (hWc i) (hW0 i) (hcan i) (hgen i) (hEq i)
  obtain ⟨η₁', hgood, h𝓗, hV', -, hWe⟩ := hrest i
  obtain ⟨hint, hS, hL⟩ := hsafe κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
    β hβ hmean hword (M' i) (hM'σ i) hM'ord (a i) (fun ω hω => htype i ω (hM'M i hω)) η₁' hgood (𝓗 i) (W i) h𝓗
    (hWc i) (hW0 i) (hWa i) (by rw [← hV']; exact hWe)
  rw [← hV'] at hS hL
  have hcm : Measurable[𝓗 i 0] fun ω => shiftW (β ω).2 (β ω).1 :=
    (Exist.StagedLaw.BoundaryWord.measurable_shiftW.comp (hβ.snd.prodMk hβ.fst)).mono (h0 i) le_rfl
  have hpair : Measurable fun ω => ((β ω).2, hd.chartField κ h ω) :=
    hβm.snd.prodMk (hd.measurable_chartField κ hh.1)
  have hHm : Measurable fun ω => Exist.flowField (β ω).2 0 (hd.chartField κ h ω) := by
    have h1 := Exist.StagedLaw.measurable_flowField_uncurry.comp hpair
    exact h1
  refine ⟨a i, 𝓗 i, W i, E i, V' i, γ' i, h0 i _ (hM'σ i), hcm, hHm, hWc i, hW0 i, hWa i, hV i, hγm i, hγc i,
    hγ0 i, hE i, hτm i, hcan i, htype', hint, hS, hL, hgen i, hpos, hthr, havoid, ?_⟩
  filter_upwards [hend, hT, hcan i, hgen i, hM'ord, hthr, hτM] with ω h1 h2 h3 h4 h5 h6 h7 hω hfin
  rcases h1 hω hfin with ⟨hstop, hoff⟩ | h1
  · left
    obtain ⟨hVe, hγe⟩ := h3 hω
    have hτe := h7 hω
    have hg := h4 hω
    rw [hVe] at hg
    have hg' := isGeneratingTrace_congr_le (η' := fun t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
      (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) t - tipPos d η₁ ω) hg
      fun t ht => by rw [hγe t ht, hτe]
    have htyp := htype i ω (hM'M i hω)
    rw [hτe] at htyp
    have hth := h2 (h5 hω) hstop hoff (W i · ω) (hWc i ω) (hW0 i ω) hg' (hVe ▸ hfin) _ _ _ _ htyp
    rw [← hVe, ← hτe] at hth
    refine le_antisymm (h6 hω) ?_
    have hle := FCPlumb.thr_le_of_force_threshold (hWc i) (ω := ω)
      (T := (V' i ω).toNNReal) (ρL := (a i).rhoL) (ρR := (a i).rhoR)
      (xL := fun ω => FCDet.typeXL κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR (shiftW (β ω).2 (β ω).1))
      (xR := fun ω => FCDet.typeXR κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR (shiftW (β ω).2 (β ω).1)) hth
    rwa [ENNReal.coe_toNNReal hfin] at hle
  · exact Or.inr h1

end InteractingSLE.RLC.AStopPath
