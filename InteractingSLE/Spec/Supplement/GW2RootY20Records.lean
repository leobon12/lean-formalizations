/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootY20Code
import InteractingSLE.Spec.Supplement.GW2RootR18Capacity

/-!
# The Borel recorded chart is the actual retained joint chart

Packet PROVE-T14-GW2ROOT2. On the original infinite continuous
counterflow sample, the stopped record driver agrees through the stop.
Locality identifies both the endpoint hull and the entire forward chart.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootY20

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- The recorded chart and its open domain agree with the literal
regularized joint chart on every original continuous infinite sample. -/
theorem record_chart_eq_regW {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (s : ℝ≥0) (ω : Ω) (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) :
    relMap (rdrv (cfRec s W ζ ω)) s =
        (GW2JointKernel.jointChart (Ito.rpath (regW s W ζ · ω)) s).1 ∧
      relDomain (rdrv (cfRec s W ζ ω)) s =
        (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull (Ito.rpath (regW s W ζ · ω)) s) := by
  let e := GW2JointKernel.cfE s W ζ ω
  have hreg : IsRegularDriver e := StagedReg.isRegularDriver_regularize _ _
  have hs : (s : ℝ≥0∞) < e.2 := by
    rw [show e.2 = ζ ω from GW2JointKernel.cfE_snd s W ζ ω, hζ]
    exact ENNReal.coe_lt_top
  have hg := isDrvGood_recOf_of_lt hreg hs
  have heq : EqOn (rdrv (cfRec s W ζ ω)) (Ito.rpath (regW s W ζ · ω)) (Icc 0 (s : ℝ)) := by
    intro t ht
    change recDrv (s : ℝ≥0∞) e t = e.1 t.toNNReal
    rw [recDrv_eq_stopDrv hreg hg]
    change e.1 (min (t.toNNReal : ℝ≥0∞) (min (s : ℝ≥0∞) e.2)).toNNReal = e.1 t.toNNReal
    rw [min_eq_left hs.le, min_eq_left (ENNReal.coe_le_coe.mpr
      (Real.toNNReal_le_iff_le_coe.mpr ht.2)), ENNReal.toNNReal_coe]
  have hU : Continuous (Ito.rpath (regW s W ζ · ω)) := by
    have he : Ito.rpath (regW s W ζ · ω) = Ito.rpath (W · ω) := by
      funext t
      exact regW_eq s hζ hW0 hW t.toNNReal
    rw [he]
    exact hW.comp continuous_real_toNNReal
  have hK := LocalExt.fwdHull_congr_of_continuousOn
    ((continuous_rdrv (cfRec s W ζ ω)).continuousOn (s := Icc 0 ((s : ℝ) + 1)))
    (hU.continuousOn (s := Icc 0 ((s : ℝ) + 1))) s.coe_nonneg (by linarith) heq
  refine ⟨?_, ?_⟩
  · funext z
    change -(QuantumZipper.fwdMap (rdrv (cfRec s W ζ ω)) s (-z⁻¹))⁻¹ = _
    rw [Ito.fwdMap_congr_of_eqOn heq]
    rfl
  · rw [relDomain_eq_jointDomain, hK]

end InteractingSLE.Theorem14.GW2TipSystem.RootY20
