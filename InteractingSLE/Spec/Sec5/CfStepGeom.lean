/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextZeroClause
import InteractingSLE.Spec.Sec7.SideHeightGeom

/-!
# Geometric force coordinates for an agreeing continuous driver

Packet PROVE-CFCHART2. The existing frozen-driver force-coordinate theorem and
causality identify the original coordinates on every infinite-lifetime sample.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfStep

open Restart Sec7.PocketTraversal

/-- On an infinite-lifetime integrated path, every original force coordinate is
the geometric image for any continuous driver agreeing with the original driver. -/
theorem force_eq_geom_of_path_top {Ω : Type*} {nL nR : ℕ} {α : ℝ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {W V B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hp : IsIntegratedSLEPath α xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω)) (hζ : ζ ω = ⊤)
    (hV : Continuous (V · ω)) (he : ∀ t, V t ω = W t ω) :
    (∀ i t, VL i t ω = geomLW V (fun _ => xL) i t ω) ∧
      ∀ j t, VR j t ω = geomRW V (fun _ => xR) j t ω := by
  have hc : Continuous fun r : ℝ => V r.toNNReal ω := hV.comp continuous_real_toNNReal
  have hfr (t : ℝ≥0) : EqOn (frozenDrive (W · ω) t) (fun r : ℝ => V r.toNNReal ω) (Icc 0 t) := by
    intro r hr
    rw [frozenDrive_eq hr]
    exact (he _).symm
  constructor
  · intro i t
    have ht : ENNReal.ofReal (t : ℝ) < ζ ω := by rw [hζ]; exact ENNReal.ofReal_lt_top
    rw [Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive hp ht le_rfl i,
      Sec7.Lemma71B.rightImg_congr hc.neg t.coe_nonneg (fun r hr => congrArg Neg.neg (hfr t hr))]
    rfl
  · intro j t
    have ht : ENNReal.ofReal (t : ℝ) < ζ ω := by rw [hζ]; exact ENNReal.ofReal_lt_top
    rw [Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp ht le_rfl j,
      Sec7.Lemma71B.rightImg_congr hc t.coe_nonneg (hfr t)]
    rfl

/-- An agreeing continuous version of an infinite-lifetime integrated path never
reaches the geometric continuation threshold. -/
theorem thr_eq_top_of_path_top {Ω : Type*} {nL nR : ℕ} {α : ℝ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {W V B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hp : IsIntegratedSLEPath α xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω)) (hζ : ζ ω = ⊤)
    (hV : Continuous (V · ω)) (he : ∀ t, V t ω = W t ω) :
    FCDet.thr ρL ρR V (fun _ => xL) (fun _ => xR) ω = ⊤ := by
  obtain ⟨hL, hR⟩ := force_eq_geom_of_path_top hp hζ hV he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, -, -⟩ := hp
  have hn : ¬ (MartChar.thresholdSet ρL ρR (V · ω)
      (fun i t => geomLW V (fun _ => xL) i t ω)
      (fun j t => geomRW V (fun _ => xR) j t ω)).Nonempty := by
    rintro ⟨t, ht⟩
    have htζ : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    apply hnot t htζ
    simpa only [MartChar.thresholdSet, mem_ofPred_eq, ← hL, ← hR, he] using ht
  exact ite_eq_right hn

end InteractingSLE.Sec5.CfStep
