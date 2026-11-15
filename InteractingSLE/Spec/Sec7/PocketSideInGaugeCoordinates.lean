/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGaugePoint

/-!
# The canonical mean and window probes before a finite lifetime

PROVE-POCKET-SIDEIN. The probes are literal Loewner coupling means and
interval harmonic measures at the deterministic high point. Their
continuity and strict positivity follow from the existing coordinate
theorems, without a phase, field-mean continuity or infinite lifetime.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal PhaseSel MartChar Aux117

/-- The canonical coupling mean read at the deterministic high point. -/
def capacityBaseProbe {Ω : Type*} {nL nR : ℕ} (κ : ℝ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (N : ℕ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  couplingMean κ (Ito.rpath (W · ω)) t
    (meanExt κ ρL ρR (W t ω) (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω))
    (capacityProbePoint N)

/-- The harmonic measure of the current exposed interval at the high point. -/
def capacityWindowProbe {Ω : Type*} {nL nR : ℕ}
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (N : ℕ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  phaseWindow (geomLW W xL 0 t ω - W t ω) (geomRW W xR 0 t ω - W t ω)
    (QuantumZipper.fwdMap (Ito.rpath (W · ω)) t (capacityProbePoint N))

/-- Both canonical probes are continuous on the full truncated lifetime,
including time zero. Different paths need no common driver extension. -/
theorem continuousOn_capacity_coordinate_probes {Ω : Type*} {nL nR : ℕ} {κ : ℝ}
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < T ω})
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (N : ℕ) (ω : Ω) :
    let S := {t : ℝ≥0 | (t : ℝ≥0∞) < T ω ∧ t < (N : ℝ≥0) + 1}
    ContinuousOn (capacityBaseProbe κ ρL ρR W xL xR N ω) S ∧
      ContinuousOn (capacityWindowProbe W xL xR N ω) S := by
  have hVL := fun i => PocketMartLife.continuousOn_geomLW_of_lt hW xL i ω
  have hVR := fun j => PocketMartLife.continuousOn_geomRW_of_lt hW xR j ω
  have hLocal (t : ℝ≥0) (ht : (t : ℝ≥0∞) < T ω ∧ t < (N : ℝ≥0) + 1) :
      ContinuousAt (capacityBaseProbe κ ρL ρR W xL xR N ω) t ∧
        ContinuousAt (capacityWindowProbe W xL xR N ω) t := by
    obtain ⟨r, htr, hrT, hrN⟩ := exists_larger_live_capacity ht.1 ht.2
    have hMaps : MapsTo Real.toNNReal (Icc 0 (r : ℝ)) {s | (s : ℝ≥0∞) < T ω} := by
      intro s hs
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hrT
    have hw : ContinuousOn (Ito.rpath (W · ω)) (Icc 0 (r : ℝ)) :=
      (hW ω).comp continuous_real_toNNReal.continuousOn hMaps
    have hvL : ∀ i, ContinuousOn (fun s : ℝ => geomLW W xL i s.toNNReal ω) (Icc 0 (r : ℝ)) :=
      fun i => (hVL i).comp continuous_real_toNNReal.continuousOn hMaps
    have hvR : ∀ j, ContinuousOn (fun s : ℝ => geomRW W xR j s.toNNReal ω) (Icc 0 (r : ℝ)) :=
      fun j => (hVR j).comp continuous_real_toNNReal.continuousOn hMaps
    have hz := capacityProbePoint_mem_active (hW ω) hrT hrN
    have hBase := PocketPhaseMeans.continuousOn_couplingMean_of_ext
      (κ := κ) (ρL := ρL) (ρR := ρR) r.coe_nonneg hw hvL hvR
      (fun s hs => ⟨fun i => PocketMartLife.geomLW_le_of_lt (hW ω) (hMaps hs) xL i,
        fun j => PocketMartLife.le_geomRW_of_lt (hW ω) (hMaps hs) xR j⟩)
      (fun s _ => isBoundedHarmonicExtension_meanExt κ ρL ρR
        (W s.toNNReal ω) (fun i => geomLW W xL i s.toNNReal ω)
        (fun j => geomRW W xR j s.toNNReal ω)) hz
    have hClamped := Ito.mem_diff_fwdHull_clampDrv r.coe_nonneg hw hz.1
      (Ito.exists_isForwardSol_of_mem r.coe_nonneg hz)
    have hWindow := continuousOn_phaseWindow (Ito.continuous_clampDrv r.coe_nonneg hw)
      r.coe_nonneg hClamped ((hvL 0).sub hw) ((hvR 0).sub hw)
    have hBaseNN : ContinuousOn (capacityBaseProbe κ ρL ρR W xL xR N ω) (Iic r) := by
      have hc := hBase.comp (s := Iic r)
        NNReal.continuous_coe.continuousOn
        (fun (s : ℝ≥0) hs => show (s : ℝ) ∈ Icc 0 (r : ℝ) from ⟨s.coe_nonneg, hs⟩)
      refine hc.congr fun s _ => ?_
      dsimp only [capacityBaseProbe, Function.comp_def]
      rw [Real.toNNReal_coe]
    have hWindowNN : ContinuousOn (capacityWindowProbe W xL xR N ω) (Iic r) := by
      have hc := hWindow.comp (s := Iic r)
        NNReal.continuous_coe.continuousOn
        (fun (s : ℝ≥0) hs => show (s : ℝ) ∈ Icc 0 (r : ℝ) from ⟨s.coe_nonneg, hs⟩)
      refine hc.congr fun s hs => ?_
      dsimp only [capacityWindowProbe, Function.comp_def, Pi.sub_apply, Ito.rpath]
      rw [Ito.fwdMap_clampDrv_of_le (show (s : ℝ) ≤ r from hs)]
      rw [Real.toNNReal_coe]
    exact ⟨hBaseNN.continuousAt (Iic_mem_nhds htr),
      hWindowNN.continuousAt (Iic_mem_nhds htr)⟩
  exact ⟨fun t ht => (hLocal t ht).1.continuousWithinAt,
    fun t ht => (hLocal t ht).2.continuousWithinAt⟩

/-- The actual geometric seed images separate at every positive live time,
so the deterministic window probe is strictly positive. -/
theorem capacityWindowProbe_pos {Ω : Type*} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < T ω})
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    {N : ℕ} {ω : Ω} {t : ℝ≥0} (ht : 0 < t) (htT : (t : ℝ≥0∞) < T ω)
    (htN : t < (N : ℝ≥0) + 1) : 0 < capacityWindowProbe W xL xR N ω t := by
  have hsep := PhaseClause.geomLW_lt_geomRW_of_pos hW xL xR 0 0 ht htT
  have hz := capacityProbePoint_mem_active (hW ω) htT htN
  have hw := Ito.continuousOn_rpath (hW ω) htT
  have hsol := Ito.exists_isForwardSol_of_mem t.coe_nonneg hz
  have hIm := Ito.im_fwdMap_pos_of_continuousOn t.coe_nonneg hw hz.1 hsol
    (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.coe_nonneg, le_rfl⟩)
  exact (phaseWindow_mem_Ioo (by linarith only [hsep]) hIm).1

end InteractingSLE.Sec7.PocketStopSide
