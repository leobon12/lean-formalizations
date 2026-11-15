/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR12Dynamics

/-!
# Protected driver rules give the comparison stopped SDE

A rule decided by the killed driver is a stopping time of the actual
Brownian filtration. Its protection before the original lifetime then
gives the finite endpoint continuity required by the comparison core.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR12

open GW2JDetR11 GW2KM2

variable {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ} {κ : ℝ}
  {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {μ : Measure Ω}
  (d : LocalDynamics Ω nL nR)
  (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR μ
    d.filtration d.W d.VL d.VR d.B d.stop)

include hE

/-- The killed driver's information lies in the actual SDE filtration,
without any completeness, usual-augmentation or force-gap hypothesis. -/
theorem killedDriverSigma_le_filtration (t : ℝ≥0) :
    killedDriverSigma d.W d.stop t ≤ d.filtration t := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨r, hrt, A, hA, rfl⟩
  exact (d.filtration.mono hrt) _ (hE.adapted_W r A hA)

/-- A protected stop decided by the killed driver has the complete
comparison stopped SDE, with no separate Brownian-filtration premise. -/
theorem isStopped_at_killedDriverStop (V : Ω → ℝ≥0∞)
    (hV : ∀ t : ℝ≥0, MeasurableSet[killedDriverSigma d.W d.stop t]
      {ξ | V ξ ≤ (t : ℝ≥0∞)})
    (hle : ∀ ξ, V ξ ≤ d.stop ξ)
    (hprotected : ∀ᵐ ξ ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) = V ξ →
      (t : ℝ≥0∞) < d.stop ξ) :
    ({d with stop := V} : LocalDynamics Ω nL nR).IsStopped μ κ xL ρL xR ρR :=
  isStopped_at_protectedStop_of_localEvolution d hE V
    (fun t => killedDriverSigma_le_filtration d hE t _ (hV t)) hle hprotected

/-- Apply exactly the path-rule measurability used by the landed staged
canonical construction. The force word can have far nonadmissible groups. -/
theorem isStopped_at_pathRule
    (τ : ((ℝ≥0 → ℝ) × ℝ≥0∞) → ℝ≥0∞)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[pathKilledSigma t] {e | τ e ≤ (t : ℝ≥0∞)})
    (hle : ∀ ξ, τ ((fun t => d.W t ξ), d.stop ξ) ≤ d.stop ξ)
    (hprotected : ∀ᵐ ξ ∂μ, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) = τ ((fun u => d.W u ξ), d.stop ξ) → (t : ℝ≥0∞) < d.stop ξ) :
    ({d with stop := fun ξ => τ ((fun t => d.W t ξ), d.stop ξ)} :
      LocalDynamics Ω nL nR).IsStopped μ κ xL ρL xR ρR := by
  apply isStopped_at_killedDriverStop d hE _ _ hle hprotected
  intro t
  exact measurableSet_killedDriverSigma_preimage
    (fun ξ => ((fun u => d.W u ξ), d.stop ξ)) t (hτ t)

end InteractingSLE.Theorem14.GW2JDetR12
