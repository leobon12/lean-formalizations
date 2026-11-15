/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtMDrive

/-!
# Theorem 1.2's restart coupling: what remains is locality under `Q`

Packet PROVE-LOCEXT-M. PROVE-LOCEXT-K reduced `RestartSeedCouplingStatement κ` to `RestartDrivingLocalityInput κ`
(clause (a), the driving law through the local stop, and locality of the restarted hulls under `Q = restartQ`).
`LocalExtMDrive` proves clause (a) (`restartDriving`). This file isolates the remaining clause:

* `RestartLocalityInput κ` (**named input**): for the data of `RestartDrivingLocalityInput`, at every stopping time
  `τ ≤ S₀` of the restarted driving filtration, the restarted hull is a local set of the recoded restarted field under
  `Q = restartQ`;
* **`restartDrivingLocalityInput_of_locality`**: `RestartLocalityInput κ → RestartDrivingLocalityInput κ` (`κ > 0`);
* **`restartSeedCouplingStatement_of_locality`**: `RestartLocalityInput κ → RestartSeedCouplingStatement κ` (`κ > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (fwdHull)
open LQGMetric (DistOn)
open Sec7 Sec5.Markov Sec2.Restart

universe u

/-- **Named input: locality of the restarted hulls under `Q`** (Aux. lemma 55, step 5 at a restart, specification
p. 250; Aux. lemma 53's locality conditionally on the recorded history, p. 245). For the data of
`RestartSeedCouplingStatement` (a coupling, a finite driving stop `T`, a good event, a seed pattern and radius `r`, a cell
event `D ∈ 𝓓_T` and a `𝓓_T`-measurable version `K` of the recorded history `𝒳_T`): at every stopping time `τ` of the
restarted driving filtration with `τ ≤ S₀` (`restartQ`-a.s.), the restarted hull `K'_τ` is a local set of the recoded
restarted field under `Q = restartQ`. This is the second clause of `RestartDrivingLocalityInput`, verbatim. -/
def RestartLocalityInput (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
        (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (G : Set Ω)
        (_ : MeasurableSet G) (_ : P Gᶜ = 0) (_ : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
        (SL : Finset (Fin nL)) (SR : Finset (Fin nR)) (r : ℝ),
        -2 < ∑ i ∈ SL, ρL i → -2 < ∑ j ∈ SR, ρR j →
      ∀ D : Set Ω, MeasurableSet[hT.measurableSpace] D → P D ≠ 0 → IsRestartCell W VL VR ζ G T SL SR r D →
      ∀ K : Ω → DrivingHist nL nR, Measurable[hT.measurableSpace] K →
        (∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
          (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
            K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) →
        ∀ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ),
          (∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), τ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω) →
          IsLocalSet (fun ω => fwdHull (fun s : ℝ => r0W G W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
            (fun ω => restartRecode κ ρL ρR r (h ω, K ω)) (restartQ κ ρL ρR r P D K h)

/-- **`RestartDrivingLocalityInput κ` from the locality input** (`κ > 0`): clause (a) is `restartDriving`. -/
theorem restartDrivingLocalityInput_of_locality {κ : ℝ} (hκ : 0 < κ) (hloc : RestartLocalityInput.{u} κ) :
    RestartDrivingLocalityInput.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp K hKm hK
  exact ⟨restartDriving hκ hC hX hT hGm hG0 hG hSL hSR hD hPD hDp hKm hK,
    hloc xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp K hKm hK⟩

/-- **Theorem 1.2's restart coupling from the locality input** (`κ > 0`): `RestartSeedCouplingStatement κ` from
`RestartLocalityInput κ` (PROVE-LOCEXT-K's `restartSeedCouplingStatement_of_input` and clause (a), `restartDriving`). -/
theorem restartSeedCouplingStatement_of_locality {κ : ℝ} (hκ : 0 < κ) (hloc : RestartLocalityInput.{u} κ) :
    RestartSeedCouplingStatement.{u} κ :=
  restartSeedCouplingStatement_of_input hκ (restartDrivingLocalityInput_of_locality hκ hloc)

end LocalExt

end InteractingSLE
