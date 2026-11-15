/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuCont

/-!
# GEOM2's root-word bounds at a root `x` are the contact clause's junctions

Packet PROVE-GW2-BUF (round 18; one sample). On ROOTX's good samples (`PhysGoodX` with GB6's record event), GEOM2's
bounds of the root-`x` root word (`GW2Wm.rootWordX_label_bounds`) are `labelL (rdrv cf) s 0 − baseRead x s cf` and
`labelR (rdrv cf) s 0 − baseRead x s cf`. These are the junctions of the counterflow path moved by the root's real
chart image, `junctionR − Re relBdry x` and `junctionL − Re relBdry x`: the form of round 17's root-`x` contact clause.
The first is positive and the second negative.

* `rtime_cfRec`, **`root_bounds_eq_junctions`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart GW2TipSystem
  GW2TipSystem.RootC24 GW2Rz GW2Rd

theorem rtime_cfRec {Ω : Type*} {s : ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤) :
    rtime (cfRec s W ζ ω) = s := by
  rw [cfRec, rtime_recOf_coe, GW2JointKernel.cfE_snd, hζ, min_top_right, ENNReal.toNNReal_coe]

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)

include hα hW hW0 hζ hs hx harc hwc hw0 hγ

omit hs in
/-- **GEOM2's root-word bounds are the junctions moved by the root's chart image.** -/
theorem root_bounds_eq_junctions (hcf : cfRec s W ζ ω ∈ gb6TS s) :
    GW2Wm.labelL (rdrv (cfRec s W ζ ω)) (rtime (cfRec s W ζ ω)) 0 - baseRead x s (cfRec s W ζ ω) =
        junctionR (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ∧
      GW2Wm.labelR (rdrv (cfRec s W ζ ω)) (rtime (cfRec s W ζ ω)) 0 - baseRead x s (cfRec s W ζ ω) =
        junctionL (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ∧
      0 < junctionR (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ∧
      junctionL (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re < 0 := by
  have hU := continuous_rp hW
  have hU0 : rp (W · ω) 0 = 0 := by simp [rp, hW0]
  set U := rdrv (cfRec s W ζ ω) with hUdef
  have hrt : rtime (cfRec s W ζ ω) = s := rtime_cfRec hζ
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  -- the record driver agrees with the path on `[0, s]`
  have hEq : ∀ r ∈ Icc (0 : ℝ) s, U r = rp (W · ω) r := fun r hr =>
    GaugeE.record_prefix_eq (Wα := W) (ζα := ζ) s hW0 hW.continuousOn hsζ hr
  have hbL : baseL U s = baseL (rp (W · ω)) s := baseL_congr hU s.coe_nonneg hEq
  have hbR : baseR U s = baseR (rp (W · ω)) s := baseR_congr hU s.coe_nonneg hEq
  -- the root is safe (ROOT2's trace safety at time `0`)
  obtain ⟨v, hv0, hvT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1
    (GW2Rz.contact_pos (W := W) (ω := ω) hα hx harc hγ)
  have he : IsRegularDriver ((w, ⊤) : (ℝ≥0 → ℝ) × ℝ≥0∞) := Gm.isRegularDriver_top hwc hw0
  have hv' : (v : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) ((w, ⊤) : (ℝ≥0 → ℝ) × ℝ≥0∞).2 := by
    rw [min_top_right]; exact hvT
  have hsafe0 : (x : ℂ) ∈ relSafe U s := by
    have h := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv' (zero_le : (0 : ℝ≥0) ≤ v)
    rwa [hγ.1, add_zero] at h
  have hsafe0' : (x : ℂ) ∈ relSafe (rp (W · ω)) s := by
    rw [← relSafe_record_eq s hW0 hW hζ]; exact hsafe0
  have hbase : baseRead x s (cfRec s W ζ ω) = (relBdry (rp (W · ω)) s x).re := by
    unfold baseRead
    rw [RootA22.boundaryRead_eq_relBdry s _ hsafe0, relBdry_record_eq s hW0 hW hζ]
  have hc₀im : (relBdry (rp (W · ω)) s x).im = 0 := im_relBdry_of_real hU hU0 s.coe_nonneg hsafe0'.2
  have hc₀re : relBdry (rp (W · ω)) s x = (((relBdry (rp (W · ω)) s x).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hc₀im])
  -- the junction values
  have hLj : GW2Wm.labelL U (rtime (cfRec s W ζ ω)) 0 = junctionR (rp (W · ω)) s := by
    rw [hrt, labelL_zero_eq_junctionR (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg]
    unfold junctionR
    rw [hbL]
  have hRj : GW2Wm.labelR U (rtime (cfRec s W ζ ω)) 0 = junctionL (rp (W · ω)) s := by
    rw [hrt, labelR_zero_eq_junctionL (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg]
    unfold junctionL
    rw [hbR]
  -- the signs, from GB6's record event
  have hneg : baseL (rp (W · ω)) s < 0 := by
    have h := hcf.2.2.2
    rw [hrt, Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg
      le_rfl, neg_zero] at h
    rw [← hbL]
    exact h
  have hpos : 0 < baseR (rp (W · ω)) s := by
    have h := hcf.2.2.1
    rw [hrt, Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg
      le_rfl] at h
    rw [← hbR]
    exact h
  have h1 := lt_junctionR_of_relBdry_eq hU hU0 s.coe_nonneg hsafe0' hc₀re hneg
  have h2 := junctionL_lt_of_relBdry_eq hU hU0 s.coe_nonneg hsafe0' hc₀re hpos
  refine ⟨by rw [hLj, hbase], by rw [hRj, hbase], by linarith, by linarith⟩

end Sample

end InteractingSLE.Theorem14.GW2Bh
