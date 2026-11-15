/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11Data
import InteractingSLE.Spec.Supplement.GW2JDetR7Stages

/-!
# Actual flow-line SDEs in the comparison data format

The canonical staged law supplies a full flow-line coupling. Extract its
actual Brownian filtration and force coordinates. If every side prefix is
admissible, the landed lifetime theorem supplies the finite-stop clause
of the comparison predicate without an availability hypothesis.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR12

open Exist Staged GW2JDetR11

/-- Extract the actual SDE from a flow-line law, retaining its literal
driver and lifetime. Admissible prefixes supply the entire stopped fact. -/
theorem exists_flowDynamics {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ μ h W ζ) :
    ∃ d : LocalDynamics Ω (flowLineNL b J 0) (flowLineNR b J 0),
      d.W = W ∧ d.stop = ζ ∧
      Sec2.IsSLEEvolutionUpTo κ (flowLineXL b J 0) (flowLineXR b J 0)
        (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        μ d.filtration d.W d.VL d.VR d.B d.stop ∧
      ((∀ i : Fin (flowLineNL b J 0), -2 <
          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), flowLineRhoL κ b J 0 θ j) →
        (∀ i : Fin (flowLineNR b J 0), -2 <
          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), flowLineRhoR κ b J 0 θ j) →
        d.IsStopped μ κ (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ)
          (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ)) := by
  have htop := fun hL hR => GW2JDetR7.ae_lifetime_top_of_flow_prefixes hκ hL hR hfl
  obtain ⟨X, 𝓕, VL, VR, B, _, hc⟩ := hfl
  let d : LocalDynamics Ω (flowLineNL b J 0) (flowLineNR b J 0) :=
    ⟨𝓕, W, VL, VR, B, ζ⟩
  refine ⟨d, rfl, rfl, hc.1.isSLEEvolutionUpTo, fun hL hR => ?_⟩
  refine ⟨hc.1.isSLEEvolutionUpTo, ?_⟩
  filter_upwards [htop hL hR] with ξ hξ t ht
  exact (ENNReal.coe_ne_top (ht.trans hξ)).elim

/-- Restricting actual local dynamics at a protected stopping time
supplies the complete comparison predicate, including the finite endpoint.
Only the original filtration's stopping-time condition is used. -/
theorem isStopped_at_protectedStop_of_localEvolution
    {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ} {κ : ℝ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {μ : Measure Ω}
    (d : LocalDynamics Ω nL nR)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR μ
      d.filtration d.W d.VL d.VR d.B d.stop) (V : Ω → ℝ≥0∞)
    (hV : ∀ t : ℝ≥0, MeasurableSet[d.filtration t] {ξ | V ξ ≤ (t : ℝ≥0∞)})
    (hle : ∀ ξ, V ξ ≤ d.stop ξ)
    (hprotected : ∀ᵐ ξ ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) = V ξ →
      (t : ℝ≥0∞) < d.stop ξ) :
    ({d with stop := V} : LocalDynamics Ω nL nR).IsStopped μ κ xL ρL xR ρR := by
  refine ⟨hE.mono hV hle, ?_⟩
  filter_upwards [hE.ae_path, hprotected] with ξ hp hξ t ht
  exact (hp.continuousOn_w.prodMk
    ((continuousOn_pi.2 hp.continuousOn_vL).prodMk
      (continuousOn_pi.2 hp.continuousOn_vR))).mono
    (fun v hv => (ENNReal.coe_le_coe.mpr hv).trans_lt (hξ t ht))

/-- A protected stopping time supplies the endpoint clause for arbitrary
force words, including far nonadmissible groups. This does not demand that
the full evolution be infinite or that every force prefix be admissible. -/
theorem isStopped_at_protectedStop {Ω : Type u} [MeasurableSpace Ω]
    {nL nR : ℕ} {κ : ℝ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {μ : Measure Ω} (d : LocalDynamics Ω nL nR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR μ
      d.filtration d.W d.VL d.VR d.B d.stop) (V : Ω → ℝ≥0∞)
    (hV : ∀ t : ℝ≥0, MeasurableSet[d.filtration t] {ξ | V ξ ≤ (t : ℝ≥0∞)})
    (hle : ∀ ξ, V ξ ≤ d.stop ξ)
    (hprotected : ∀ᵐ ξ ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) = V ξ →
      (t : ℝ≥0∞) < d.stop ξ) :
    ({d with stop := V} : LocalDynamics Ω nL nR).IsStopped μ κ xL ρL xR ρR := by
  exact isStopped_at_protectedStop_of_localEvolution d hE.isSLEEvolutionUpTo V
    hV hle hprotected

end InteractingSLE.Theorem14.GW2JDetR12
