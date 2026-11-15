/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockAssembly
import InteractingSLE.Spec.Restart.FCBridge
import InteractingSLE.Spec.Restart.R1GlueHist

/-!
# First-contact lifetime inputs

The canonical clock record identifies the chart lifetime with the capacity lifetime of the chart path. The remaining
first-contact geometric input is the equality between that capacity lifetime and the force-word threshold. This file
names that precise input and supplies the clock and positivity adapters used by the driver-to-path bridge.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open Sec2.Assembly

universe u

/-- The finite data which determine an angle-`θ` flow-line force type. Positions are excluded: for a fixed
boundary word they are determined by the same finite word and the counts and weights below are the type parameters. -/
structure FirstContactFlowTypeCode where
  leftCount : ℕ
  leftWeights : List ℝ
  rightCount : ℕ
  rightWeights : List ℝ
  deriving DecidableEq

/-- The force-type code of the flow-line word of `c` at seed `0`. -/
def firstContactFlowTypeCode (κ θ : ℝ) (c : BoundaryWord) : FirstContactFlowTypeCode :=
  { leftCount := flowLineNL c.fn c.jumps 0
    leftWeights := List.ofFn (flowLineRhoL κ c.fn c.jumps 0 θ)
    rightCount := flowLineNR c.fn c.jumps 0
    rightWeights := List.ofFn (flowLineRhoR κ c.fn c.jumps 0 θ) }

/-- **Finite-type input for a first-contact word.** This is the exact finite-range statement needed to split the
meeting branch into fixed `FCDet.typeSet` cases. The source route is that the word heights lie in the finite set of
original heights together with the two contact-side heights. -/
def FirstContactFiniteFlowTypes {Ω : Type u} (M : Set Ω) (β : Ω → BoundaryWord) (κ θ : ℝ) : Prop :=
  {τ : FirstContactFlowTypeCode |
    ∃ ω, ω ∈ M ∧ firstContactFlowTypeCode κ θ (β ω) = τ}.Finite

/-- **Auxiliary Lemma 78 seed input** on the first-contact branch, in the exact `FCDet` threshold-condition form. -/
def FirstContactAux78SeedInput {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω}
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ meetSet d → ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω)

/-- **R1 pairing-integrability input** in the exact form consumed by `FCDet.ae_driverCodeMatch_of_hasSafeLaw_on`.
The first-contact R1 Gaussian law with bounded conditional mean is the source of this input. -/
def FirstContactDriverIntegrabilityInput {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Set Ω) (κ θ : ℝ) (Hc : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ φ : TestOn upperHalfPlaneOpens,
    Integrable (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω) φ) (P.restrict M)

/-- **The chart-clock/force-threshold identity at first contact.** This is the deterministic geometric statement that
remains to be proved from the collision-weight telescoping and the no-return property. Its right side is written in
chart-clock coordinates; the left side is the threshold of the specified finite force word and driver. -/
def FirstContactChartClockThresholdIdentity {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {d : PairData Ω} (W : ℝ≥0 → Ω → ℝ)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ meetSet d →
    FCDet.thr ρL ρR W xL xR ω =
      capLife (chartClock (cPath d univ d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω)

/-- **Capacity lifetime equals force-word lifetime.** The only non-bookkeeping premise is the explicitly named
chart-clock/threshold identity. The canonical clock record supplies the identification of `U₁` with capacity life on
the first-contact event. -/
theorem ae_firstContact_lifetime_eq_thr_of_chartClockThresholdIdentity
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω}
    (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞)
    (hclock : d.IsCanonClock P γ₁ γ₂ U₁ U₂)
    (W : ℝ≥0 → Ω → ℝ)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    (hidentity : FirstContactChartClockThresholdIdentity (d := d) (P := P) W ρL ρR xL xR) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d → U₁ ω = FCDet.thr ρL ρR W xL xR ω := by
  filter_upwards [hclock, hidentity] with ω hclockω hidentityω hmeet
  have hmem := (mem_meetSet_iff (d := d)).1 hmeet
  have hcanon := hclockω hmem.1
  have hcap := (hcanon.1 hmem.2.1).2
  exact hcap.trans (hidentityω hmeet).symm

/-- **A seed-admissibility input gives positive first-contact lifetime.** This adapter reuses `FCDet.thr_pos`; the
Auxiliary Lemma 78 argument that proves `hseed` from the first-contact word remains separate. -/
theorem ae_firstContact_thr_pos_of_admissibleSeed
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω}
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hseed : FirstContactAux78SeedInput (d := d) (P := P) ρL ρR xL xR) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d → 0 < FCDet.thr ρL ρR W xL xR ω := by
  filter_upwards [hseed] with ω hseedω hmeet
  exact FCDet.thr_pos hW0 hWc hxL0 hxR0 (hseedω hmeet)

/-- **Fixed flow type on a live set.** A word in a fixed `typeSet` has the corresponding flow-line type, by the
existing `FCDetTransfer` adapter. For first-contact applications with finitely many force types, apply this lemma on
each type-set branch. -/
theorem ae_isFlowType_of_ae_mem_typeSet
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {M : Set Ω}
    {κ θ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (β : Ω → BoundaryWord)
    (hβ : ∀ᵐ ω ∂P, ω ∈ M → β ω ∈ FCDet.typeSet κ θ nL nR ρL ρR) :
    ∀ᵐ ω ∂P, ω ∈ M →
      FCDet.IsFlowType κ θ (β ω) (FCDet.typeXL κ θ nL nR ρL ρR (β ω))
        (FCDet.typeXR κ θ nL nR ρL ρR (β ω)) ρL ρR := by
  filter_upwards [hβ] with ω hω hM
  exact FCDet.isFlowType_of_mem_typeSet (hω hM)

end Restart

end InteractingSLE
