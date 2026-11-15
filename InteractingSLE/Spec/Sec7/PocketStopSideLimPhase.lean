/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMean
import InteractingSLE.Spec.Sec7.PhaseSel3

/-!
# The pocket side limit with one common exposed-side phase

PROVE-STRIPSYS38. Aux. 122 and Lemma R.6 distinguish the identification of the
boundary word up to a common lattice phase from the selection of phase zero.
`PocketStopPhaseSideLimit` records that distinction. The same scalar d is used
at every exposed boundary point, on both sides of the driver, and for every
version of the local-set mean. Unvisited sides retain their original word.

This does not replace or weaken `PocketStopSideLimit`. The zero-phase version
is equivalent to that unchanged predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PhaseSel

/-- The all-point boundary word with one common lattice shift on the exposed
interval. The phase is independent of the mean version and representative. -/
def PocketStopPhaseSideLimit {Ω : Type*} (κ : ℝ) {nL nR : ℕ}
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (a : ℝ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (K : Ω → Set ℂ)
    (d : Ω → ℝ) (q : ℝ≥0) : Prop :=
  (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, d ω = m * phaseStep κ) ∧
  ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ K ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g ω φ = ∫ z, v z * φ z) →
        ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
          Tendsto (fun y => v ((relChart c γ q ω).2.1 y) + u ((relChart c γ q ω).2.1 y) +
              chiC κ * (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ))
            (𝓝 (phaseData κ ρL ρR
              (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
              (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (d ω) ξ - a))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
  {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
  {K : Ω → Set ℂ} {d : Ω → ℝ} {q : ℝ≥0}

/-- Once the common phase vanishes on the live event, the original side-limit
predicate follows for every local-set-mean version. -/
theorem pocketStopSideLimit_of_phase_eq_zero
    (hside : PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K d q)
    (hd : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → d ω = 0) :
    PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q := by
  intro g hg
  filter_upwards [hside.2 g hg, hd] with ω hs hz hω hq v hv hvr ξ hξ
  have h := hs hω hq v hv hvr ξ hξ
  simpa only [phaseData, hz hω hq, zero_mul, add_zero] using h

/-- A canonical side limit is a phase side limit with phase identically zero. -/
theorem pocketStopPhaseSideLimit_zero
    (hside : PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K (fun _ => 0) q := by
  refine ⟨Eventually.of_forall (fun _ _ _ => ⟨0, by rw [Int.cast_zero, zero_mul]⟩), ?_⟩
  intro g hg
  filter_upwards [hside g hg] with ω hs hω hq v hv hvr ξ hξ
  simpa only [phaseData, zero_mul, add_zero] using hs hω hq v hv hvr ξ hξ

/-- The new predicate specializes exactly to the existing canonical predicate. -/
theorem pocketStopPhaseSideLimit_zero_iff :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K (fun _ => 0) q ↔
      PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q :=
  ⟨fun h => pocketStopSideLimit_of_phase_eq_zero h (Eventually.of_forall fun _ _ _ => rfl),
    pocketStopPhaseSideLimit_zero⟩

end InteractingSLE.Sec7.PocketStopSide
