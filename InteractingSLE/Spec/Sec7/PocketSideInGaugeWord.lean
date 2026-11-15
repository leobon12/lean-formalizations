/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGaugeCoordinates

/-!
# Literal finite-word mean probes for a constant positive-time phase

PROVE-POCKET-SIDEIN. The phase probe is the coupling mean of the explicit
bounded Poisson phase word, evaluated at the high observation point. Its
difference from the canonical probe is exactly phase times harmonic measure.
For a phase constant at positive times, all three probe conditions follow.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal PhaseSel MartChar Aux117

/-- The full bounded phase-word coupling mean at the high observation point. -/
def capacityPhaseProbe {Ω : Type*} {nL nR : ℕ} (κ : ℝ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (δ : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  couplingMean κ (Ito.rpath (W · ω)) t
    (PhaseClause.phaseProc κ ρL ρR W (geomLW W xL) (geomRW W xR) (δ t) ω t)
    (capacityProbePoint N)

/-- The derivative corrections cancel in the difference of the two actual
Poisson-word coupling means. No mean-identity hypothesis is needed. -/
theorem capacityPhaseProbe_sub_base {Ω : Type*} {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < T ω})
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (δ : ℝ≥0 → Ω → ℝ) {N : ℕ} {ω : Ω} {t : ℝ≥0}
    (ht : 0 < t) (htT : (t : ℝ≥0∞) < T ω) (htN : t < (N : ℝ≥0) + 1) :
    capacityPhaseProbe κ ρL ρR W xL xR δ N ω t - capacityBaseProbe κ ρL ρR W xL xR N ω t =
      δ t ω * capacityWindowProbe W xL xR N ω t := by
  have hsep := PhaseClause.geomLW_lt_geomRW_of_pos hW xL xR 0 0 ht htT
  have hz := capacityProbePoint_mem_active (hW ω) htT htN
  have hw := Ito.continuousOn_rpath (hW ω) htT
  have hsol := Ito.exists_isForwardSol_of_mem t.coe_nonneg hz
  have hIm := Ito.im_fwdMap_pos_of_continuousOn t.coe_nonneg hw hz.1 hsol
    (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.coe_nonneg, le_rfl⟩)
  have hU := PhaseClause.isBoundedHarmonicExtension_phaseProc
    (κ := κ) (ρL := ρL) (ρR := ρR) (W := W) (VL := geomLW W xL) (VR := geomRW W xR)
    hκ (δ t)
      (PocketMartLife.geomLW_le_of_lt (hW ω) htT xL 0)
      (PocketMartLife.le_geomRW_of_lt (hW ω) htT xR 0)
  have hU' : IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - Ito.rpath (W · ω) t)
        (fun j => geomRW W xR j t ω - Ito.rpath (W · ω) t) (δ t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - Ito.rpath (W · ω) t)
        (fun j => geomRW W xR j t ω - Ito.rpath (W · ω) t))
      (PhaseClause.phaseProc κ ρL ρR W (geomLW W xL) (geomRW W xR) (δ t) ω t) := by
    simpa only [Ito.rpath, Real.toNNReal_coe] using hU
  have hEq := couplingMean_sub_couplingMean_eq (k := κ) (ρL := ρL) (ρR := ρR)
    (w := Ito.rpath (W · ω)) (t := (t : ℝ)) hsep hU' hIm
  dsimp only [capacityPhaseProbe, capacityBaseProbe, capacityWindowProbe]
  simpa only [Ito.rpath, Real.toNNReal_coe] using hEq

/-- A version constant on positive times has the exact mean-probe property
on every full truncated lifetime. The observables are the literal bounded
word means above, not algebraic stand-ins for the phase. -/
theorem capacity_probes_of_positive_constant {Ω : Type*} {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < T ω})
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    {δ : ℝ≥0 → Ω → ℝ} {c : Ω → ℝ}
    (hδ : ∀ t ω, 0 < t → δ t ω = c ω) (N : ℕ) (ω : Ω) :
    let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < T ω ∧ t < (N : ℝ≥0) + 1}
    ContinuousOn (capacityPhaseProbe κ ρL ρR W xL xR δ N ω) S ∧
      ContinuousOn (capacityBaseProbe κ ρL ρR W xL xR N ω) S ∧
      ContinuousOn (capacityWindowProbe W xL xR N ω) S ∧
      ∀ t ∈ S, 0 < capacityWindowProbe W xL xR N ω t ∧
        capacityPhaseProbe κ ρL ρR W xL xR δ N ω t -
          capacityBaseProbe κ ρL ρR W xL xR N ω t = δ t ω * capacityWindowProbe W xL xR N ω t := by
  obtain ⟨hBase, hWindow⟩ := continuousOn_capacity_coordinate_probes ρL ρR hW xL xR N ω
  have hSub : {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < T ω ∧ t < (N : ℝ≥0) + 1} ⊆
      {t : ℝ≥0 | (t : ℝ≥0∞) < T ω ∧ t < (N : ℝ≥0) + 1} := fun _ ht => ht.2
  refine ⟨?_, hBase.mono hSub, hWindow.mono hSub, fun t ht =>
    ⟨capacityWindowProbe_pos hW xL xR ht.1 ht.2.1 ht.2.2,
      capacityPhaseProbe_sub_base hκ ρL ρR hW xL xR δ ht.1 ht.2.1 ht.2.2⟩⟩
  refine ((hBase.mono hSub).add ((hWindow.mono hSub).const_mul (c ω))).congr fun t ht => ?_
  have hEq := capacityPhaseProbe_sub_base hκ ρL ρR hW xL xR δ ht.1 ht.2.1 ht.2.2
  rw [hδ t ω ht.1] at hEq
  dsimp only [Pi.add_apply]
  linarith only [hEq]

end InteractingSLE.Sec7.PocketStopSide
