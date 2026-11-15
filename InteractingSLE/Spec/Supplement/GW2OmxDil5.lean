/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil4
import InteractingSLE.Spec.Supplement.BW1LMeanRet
import InteractingSLE.Spec.Supplement.BW1VerRead
import InteractingSLE.Spec.Supplement.GW2RdStgChain
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# GW2's open lines: the stage chart sends the counterflow's continuation far away

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation, stage side at `∞`). Per sample:

* `relChart_gb6Rec_fst`: GB6's relative chart of the counterflow record at `s` is `relMap (W', s)`;
* **`stgChart_continuation_far`**: the stage chart `stgChart (relChart (gb6Rec …)) R a` sends the continuation
  `invHull W' (s + v) ∖ invHull W' s` outside any ball for small `v` (`relMap_continuation_far`, `loewner_fwd_far`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open Supp8.GB6 (relMap gb6Rec)
open Supp8.Q3Rel (invHull)
open Exist.StagedLaw

/-- GB6's relative chart of the counterflow record at `s` is the relative map of the counterflow at `s`. -/
theorem relChart_gb6Rec_fst {Ω : Type*} {s : ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hW0 : W 0 ω = 0)
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hs : (s : ℝ≥0∞) < ζ ω) (z : ℂ) :
    (Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)).1 z = relMap (fun u : ℝ => W u.toNNReal ω) s z := by
  rw [BW1LMean.relChart_fst]
  have hrs : BW1Ver.recS (gb6Rec s W ζ ω) = s := NNReal.coe_injective (by
    rw [← BW1Ver.rtime_eq_recS]
    exact Supp8.GB6.rtime_recOf_cfE s hs)
  rw [hrs]
  unfold relMap
  rw [fwdMap_eq_of_eqOn s.coe_nonneg (W' := fun u : ℝ => W u.toNNReal ω) fun r hr => by
    rw [gb6Rec]
    exact Supp8.GB6.rdrv_recOf_cfE s hW0 hWc hs hr.2]

/-- **The stage chart sends the counterflow's continuation far away.** -/
theorem stgChart_continuation_far {Ω : Type*} {s : ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hW0 : W 0 ω = 0) (hWc : Continuous fun t => W t ω) (hs : (s : ℝ≥0∞) < ζ ω)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) (a : ℝ≥0) (M : ℝ) :
    ∃ δ > 0, ∀ v : ℝ, 0 < v → v ≤ δ → ∀ z ∈ invHull (fun u : ℝ => W u.toNNReal ω) (s + v) \
      invHull (fun u : ℝ => W u.toNNReal ω) s,
      z ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)) R a).dom : Set ℂ) →
      M < ‖(GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)) R a).1 z‖ := by
  have hc₀ := Supp8.RelSafeS.isConformal_relChart (gb6Rec s W ζ ω)
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  obtain ⟨C, hC⟩ := loewner_fwd_far hc₀ hRp hRp0 a.coe_nonneg
  have hU : Continuous fun u : ℝ => W u.toNNReal ω := hWc.comp continuous_real_toNNReal
  have hU0 : (fun u : ℝ => W u.toNNReal ω) 0 = 0 := by simp [hW0]
  obtain ⟨δ, hδ, hfar⟩ := relMap_continuation_far hU hU0 s.coe_nonneg (M := max 1 (M + C + 1))
    (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨δ, hδ, fun v hv hvδ z hz hzd => ?_⟩
  have h1 := hC z hzd
  have h2 := hfar v hv hvδ z hz
  rw [← relChart_gb6Rec_fst hW0 hWc.continuousOn hs z] at h2
  change ‖(Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)).1 z‖ - C ≤
    ‖((Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)).loewner (Ito.rpath R) a).1 z‖ at h1
  change M < ‖((Supp8.RelSafeS.relChart (gb6Rec s W ζ ω)).loewner (Ito.rpath R) a).1 z‖
  have h3 : M + C + 1 ≤ max 1 (M + C + 1) := le_max_right _ _
  linarith

end InteractingSLE.Theorem14.GW2Omx
