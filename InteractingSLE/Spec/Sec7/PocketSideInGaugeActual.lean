/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGaugeWord
import InteractingSLE.Spec.Sec7.PocketSideInGaugeVersion

/-!
# Actual driven-curve probes for the selected lattice phase

PROVE-POCKET-SIDEIN. Specialize the coordinate construction on each good
path. No regularity is required off the given event, and no witness or
random visit is chosen. The resulting property has exactly the horizon
and quantifiers of the side-probe leaf.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal PhaseSel Lemma71C

/-- Literal finite-word probes give the side-probe leaf at every actual
driven path for the selected positive-time lattice version. -/
theorem capacity_probes_of_driven_lattice_version {Ω : Type*} {nL nR : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {γ : Ω → ℝ → ℂ} {A : Set Ω} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (initial : Ω → ℝ) (n : Ω → ℤ) (N : ℕ) {ω : Ω} (hω : ω ∈ A) :
    let W := fun t ω => segDriver (γ ω) t
    let δ := positiveLatticePhase initial n (phaseStep κ)
    let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ t < (N : ℝ≥0) + 1}
    ContinuousOn (capacityPhaseProbe κ ρL ρR W xL xR δ N ω) S ∧
      ContinuousOn (capacityBaseProbe κ ρL ρR W xL xR N ω) S ∧
      ContinuousOn (capacityWindowProbe W xL xR N ω) S ∧
      ∀ t ∈ S, 0 < capacityWindowProbe W xL xR N ω t ∧
        capacityPhaseProbe κ ρL ρR W xL xR δ N ω t -
          capacityBaseProbe κ ρL ρR W xL xR N ω t = δ t ω * capacityWindowProbe W xL xR N ω t := by
  exact capacity_probes_of_positive_constant (Ω := Unit) hκ ρL ρR
    (W := fun t _ => segDriver (γ ω) t) (T := fun _ => capLife (γ ω))
    (fun _ => (hγ ω hω).segDriver_spec.2.1) (fun _ => xL ω) (fun _ => xR ω)
    (δ := fun t _ => positiveLatticePhase initial n (phaseStep κ) t ω)
    (c := fun _ => (n ω : ℝ) * phaseStep κ)
    (fun t _ ht => by rw [positiveLatticePhase, ite_eq_right (ne_of_gt ht)]) N ()

end InteractingSLE.Sec7.PocketStopSide
