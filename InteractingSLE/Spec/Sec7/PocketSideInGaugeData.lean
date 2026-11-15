/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGaugeActual
import InteractingSLE.Spec.Wire.Thm12LateSide

/-!
# Side data with the constructed capacity probes

PROVE-POCKET-SIDEIN. Install the selected lattice version and literal
mean/window observables in the existing side-data record. This proves
the probe leaf for the resulting record. Every other source law, including
any joint germ law, must concern this chosen phase version.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Late

open Sec7 Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PhaseSel Sec7.Lemma71C

/-- Select the phase version and its literal bounded-word probes before
using the record in any source-law or joint-germ assertion. -/
def capacityProbeSideData {Ω : Type} {nL nR : ℕ} (e : SideData Ω) (κ : ℝ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (n : Ω → ℤ) : SideData Ω :=
  let W := fun t ω => segDriver (γ ω) t
  let phase := positiveLatticePhase (e.phase 0) n (phaseStep κ)
  { e with phase := phase
           probe := capacityPhaseProbe κ ρL ρR W xL xR phase
           baseProbe := capacityBaseProbe κ ρL ρR W xL xR
           weight := capacityWindowProbe W xL xR }

/-- The exact side-probe leaf holds for the constructed record on any
event of actual driven paths. No additional probabilistic premise is used. -/
theorem capacityProbeSideData_probes {Ω : Type} [MeasurableSpace Ω] {nL nR : ℕ}
    {P : Measure Ω} {κ : ℝ} (hκ : 0 < κ) (e : SideData Ω)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {γ : Ω → ℝ → ℂ} {A : Set Ω} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (n : Ω → ℤ) :
    let refs := capacityProbeSideData e κ ρL ρR γ xL xR n
    ∀ N : ℕ, ∀ᵐ ω ∂P, ω ∈ A →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ t < (N : ℝ≥0) + 1}
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧
        ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧
          refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t := by
  intro refs N
  exact Eventually.of_forall fun ω hω =>
    capacity_probes_of_driven_lattice_version hκ ρL ρR hγ xL xR (e.phase 0) n N hω

end InteractingSLE.Wire.Late
