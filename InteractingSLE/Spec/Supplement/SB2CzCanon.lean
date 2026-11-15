/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CzHull
import InteractingSLE.Spec.Supplement.SB2CzMix
import InteractingSLE.Spec.Supplement.SB2QxCanon

/-!
# The canonical tail objects of a stage from exact objects, the stage law and the chain facts

Packet PROVE-SB2-CANON. **`tailCanonAt_of_chainFacts`** reduces `Mz.TailCanonAt ℓ` (one conjunct of the target
`Mz.SB2LowerStageCanonStatement`) to:

* objects `c, K, x₀` measurable for the retained past `Ms.stageMarks ℓ` (uncompleted; for `K` see
  `exists_exactRetHull`) and an event `G` of `Ms.stageMarks (ℓ + 1)` (which sees whether B's piece `ℓ` has lifetime
  `0`);
* the conditional law, given `Ms.stageMarks ℓ`, of the field read in `Mo.hullChart (fill K) x₀`, almost surely on `G`
  (for a law given finer marks see `ae_isGFF_of_le_fine`);
* the coverage of the tail stage launches by `G`;
* almost surely on `G`, `fill K = fill (A ∪ B_{<ℓ})` and the chain facts `Qx.ChainFacts` of the canonical driver
  (B launches at `ℓ`, the stage chart is a domain chart of the unfilled retained complement, the chain clause
  `Mx.ChainFor` of B's piece, positive lifetime, continuity up to it).

The record clause of `Mz.CanonIdentOn` (a driver `Dr` measurable for `Ms.stageMarks (ℓ + 1)` with the canonical record)
is REVIEW-FABLE-T14's `Qx.exists_canonRec`.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx Mz

/-- **`Mz.TailCanonAt ℓ` from exact objects, the law given the retained past and the chain facts.** -/
theorem tailCanonAt_of_chainFacts (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ)
    (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    (hRw : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRu : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l)))
    (h𝓜 : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ) (hh : Measurable h)
    {G : Set Ω} {c : Ω → BoundaryWord} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hcm : Measurable[Ms.stageMarks κ b jumps E u l k ℓ] c)
    (hKm : @IsDyadicHitMeasurable Ω (Ms.stageMarks κ b jumps E u l k ℓ) K)
    (hx₀m : Measurable[Ms.stageMarks κ b jumps E u l k ℓ] x₀)
    (hG : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] G)
    (hlaw : ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P (Ms.stageMarks κ b jumps E u l k ℓ) ω₁)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (c ω₁).fn (c ω₁).jumps)
    (hcov : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) + 2 ≤ ℓ →
      (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ G)
    (hfill : ∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = fillH (retY (κ := κ) b jumps E u l k ℓ ω))
    (hfacts : ∀ᵐ ω ∂P, ω ∈ G → Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω) :
    TailCanonAt h12p hκ b jumps P h E u l k ℓ := by
  have hmono : Ms.stageMarks κ b jumps E u l k ℓ ≤ Ms.stageMarks κ b jumps E u l k (ℓ + 1) :=
    stageMarks_mono (Nat.le_succ ℓ)
  have hle : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ := hmono.trans h𝓜
  obtain ⟨Dr, hDrm, hDrreg, hDreq⟩ := Qx.exists_canonRec h12p hκ E u l k ℓ hRw hRu h𝓜 hh (hcm.mono hle le_rfl)
    hKc hKp (fun n j => hmono _ (hKm n j)) (hx₀m.mono hmono le_rfl) hG hfacts
  refine ⟨G, c, K, x₀, Dr, hKc, hKp, hcm, hKm, hx₀m, hlaw, hcov, hDrm, hDrreg, ?_⟩
  filter_upwards [hfill, hfacts, hDreq] with ω hf hc hr hω
  obtain ⟨-, -, -, hch, hpos, -⟩ := hc hω
  exact ⟨hf hω, hch, hpos, hr hω⟩

end InteractingSLE.Theorem14.SB.Cz
