/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Read

/-!
# The low-arc tip reader is the actual centered relative curve

Packet PROVE-T14-GW2ROOT2. Original pre-contact traces and the cover's
arc bound imply safety for the recorded boundary chart. The centered
reader is continuous, preserves precisely the interior visits, and has
zero boundary occupation in the original physical capacity time.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2)

include hα hW hW0 hζ hx harc he hγ hv

/-- The translated physical trace, including its real visits, is safe
for the actual recorded counterflow chart through the live cutoff. -/
theorem trace_mem_record_relSafe {t : ℝ≥0} (htv : t ≤ v) :
    (x : ℂ) + γ t ∈ relSafe (rdrv (cfRec s W ζ ω)) s := by
  have hc : ContinuousOn (fun q => (x : ℂ) + γ q) (Icc 0 v) :=
    continuousOn_const.add (hγ.2.1.mono fun q hq =>
      (ENNReal.coe_le_coe.mpr hq.2).trans (lt_min_iff.mp hv).2.le)
  have h0 : (x : ℂ) + γ 0 = x := by rw [hγ.1, add_zero]
  have hH : MapsTo (fun q => (x : ℂ) + γ q) (Icc 0 v) Hbar := by
    intro q hq
    have h := Sec7.IsGeneratingTrace.mem_Hbar hγ he.1 he.2.1
      ((ENNReal.coe_le_coe.mpr hq.2).trans (lt_min_iff.mp hv).2.le)
    change 0 ≤ (γ q).im at h
    change 0 ≤ ((x : ℂ) + γ q).im
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using h
  have hd : Disjoint (α '' Icc 0 s) ((fun z : ℂ => -z⁻¹) ''
      ((fun q => (x : ℂ) + γ q) '' Icc 0 v \ {0})) := by
    apply disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨z, ⟨⟨q, hq, rfl⟩, hn⟩, heq⟩
    have ht := (ENNReal.coe_le_coe.mpr hq.2).trans_lt (lt_min_iff.mp hv).1
    apply notMem_of_lt_firstContactTime ht
    refine ⟨u, hu, ?_⟩
    rw [sphereInv_coe_of_ne hn]
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) heq.symm
  have hsafe := path_mem_relSafe_of_real_arc hα hW hW0 ENNReal.coe_lt_top
    hx hc h0 hH harc hd ⟨zero_le, htv⟩
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hK := GaugeE.record_hull_eq s hW0 hW.continuousOn hs
  change QuantumZipper.fwdHull (rdrv (cfRec s W ζ ω)) s =
    QuantumZipper.fwdHull (Ito.rpath (W · ω)) s at hK
  unfold relSafe Supp8.Q3Rel.invHull at hsafe ⊢
  rw [hK]
  exact hsafe

/-- The low-arc reader is the original translated trace in the retained
boundary chart, centered at the image of the actual root. -/
theorem rootTipRead_eq {t : ℝ≥0} (htv : t ≤ v) :
    rootTipRead x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) =
      relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
        relBdry (rdrv (cfRec s W ζ ω)) s x := by
  have hsafe := trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv htv
  have hsafe0 := trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv
    (t := 0) zero_le
  rw [hγ.1, add_zero] at hsafe0
  unfold rootTipRead rootChartRead
  rw [RootA22.physicalTipRead_recOf_eq he hγ (lt_min_iff.mp hv).2 htv,
    RootA22.boundaryRead_eq_relBdry s _ hsafe,
    RootA22.boundaryRead_eq_relBdry s _ hsafe0]

/-- Continuity includes the protected endpoint and every real visit. -/
theorem continuousOn_rootTipRead :
    ContinuousOn (fun t => rootTipRead x s t
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) (Icc 0 v) := by
  have hc : ContinuousOn (fun q => (x : ℂ) + γ q) (Icc 0 v) :=
    continuousOn_const.add (hγ.2.1.mono fun q hq =>
      (ENNReal.coe_le_coe.mpr hq.2).trans (lt_min_iff.mp hv).2.le)
  have hmap := (continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg).comp
    hc (fun q hq => trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv hq.2)
  have hm := hmap.sub (continuousOn_const (c := relBdry (rdrv (cfRec s W ζ ω)) s x))
  exact hm.congr fun q hq => rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv hq.2

/-- Real recentering and the safe relative chart preserve exactly the
interior visits of the original physical trace. -/
theorem rootTipRead_mem_H_iff {t : ℝ≥0} (htv : t ≤ v) :
    rootTipRead x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) ∈ H ↔ γ t ∈ H := by
  have hsafe := trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv htv
  have hsafe0 := trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv
    (t := 0) zero_le
  rw [hγ.1, add_zero] at hsafe0
  have h0 := im_relBdry_of_real (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe0.2
  rw [rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv htv]
  have hi := relBdry_mem_H_iff (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe
  change (0 < (relBdry _ _ ((x : ℂ) + γ t)).im ↔ 0 < ((x : ℂ) + γ t).im) at hi
  change (0 < (relBdry _ _ _ - relBdry _ _ _).im) ↔ 0 < (γ t).im
  rw [Complex.sub_im, h0, sub_zero]
  simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hi

/-- Boundary occupation is null in the original physical capacity time;
no arbitrary time change is used to transport a null set. -/
theorem volume_rootTipRead_notMem_H :
    volume {t : ℝ | t ∈ Ioo 0 (v : ℝ) ∧ rootTipRead x s t.toNNReal
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) ∉ H} = 0 := by
  apply measure_mono_null ?_ (hγ.volume_setOf_notMem_H he.1 he.2.1)
  intro t ht
  have htv : t.toNNReal ≤ v := Real.toNNReal_le_iff_le_coe.mpr ht.1.2.le
  refine ⟨ht.1.1.le, (ENNReal.coe_le_coe.mpr htv).trans_lt (lt_min_iff.mp hv).2, ?_⟩
  exact fun htH => ht.2 ((rootTipRead_mem_H_iff W ζ ω hα hW hW0 hζ hx harc he hγ hv htv).2 htH)

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
