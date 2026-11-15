/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzCoord
import InteractingSLE.Spec.Supplement.GW2RzRead

/-!
# GW2 at a root `x`: the physical readback of the re-centred relative driver (decision D8, layer 4b)

Packet PROVE-GW2-ROOTX, round 3. GB6's live readout rests on the readback of the physical trace from the relative
coordinates (`ReadD.physicalTrace_of_relHulls`). At a root `x`, with ROOT2's translated disjointness
(`RootI30.disjoint_closure_translated_hull`), the root-`x` relative chain (`RootI30.exists_relative_chain`) and GB6's
bad-point avoidance (`Q3Rel.relBad_notMem_closure`, which takes any continuous explored driver):

* **`inverseRead_root`**: before the first contact the record's inverse chart pulls the boundary chart value of
  `x + γ t` back to `x + γ t`;
* **`physicalTraceX_of_chain`**: the read-back physical trace (`GW2Rz.physicalTraceX`) of a re-centred chain driver
  at the root-`x` clock of `t` is `x + γ t` (BUF's generating trace of the capacity tip, ROOT2's tip reader).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem

section Readback

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  (hΨ : Supp8.Q3Rel.IsRetainedChartOff (Supp8.Q3Rel.invHull (rdrv (cfRec s W ζ ω)) s)
    (relMap (rdrv (cfRec s W ζ ω)) s) (relInv (rdrv (cfRec s W ζ ω)) s)
    (Supp8.Q3Rel.relLog (rdrv (cfRec s W ζ ω)) s) (Supp8.Q3Rel.relBad (rdrv (cfRec s W ζ ω)) s))

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hΨ

/-- **The record's inverse chart reads the physical point back at a root `x`**: before the first contact, the
boundary chart value of `x + γ t` is pulled back to `x + γ t`. -/
theorem inverseRead_root {v : ℝ≥0} (hv0 : 0 < v)
    (hv : (v : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) {t : ℝ≥0} (ht : t ≤ v) :
    inverseRead s (cfRec s W ζ ω, relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t)) = (x : ℂ) + γ t := by
  set U := rdrv (cfRec s W ζ ω) with hUdef
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  -- the explored prefix up to `v` misses the retained prefix in the inversion
  have hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => γ t + x) '' Icc 0 v \ {0})) := by
    apply disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨_, ⟨⟨t', ht', rfl⟩, hn⟩, heq⟩
    change γ t' + (x : ℂ) ≠ 0 at hn
    change -(γ t' + (x : ℂ))⁻¹ = α u at heq
    have htn := (ENNReal.coe_le_coe.mpr ht'.2).trans_lt hv
    apply notMem_of_lt_firstContactTime htn
    refine ⟨u, hu, ?_⟩
    have hn' : (x : ℂ) + γ t' ≠ 0 := by simpa only [add_comm] using hn
    rw [sphereInv_coe_of_ne hn']
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (by simpa only [add_comm] using heq.symm)
  have hd := RootI30.disjoint_closure_translated_hull hα hW hW0 hγ hwc hw0 hv0 hx harc hsep
  have hKU : fwdHull U s = fwdHull (Ito.rpath (W · ω)) s := GaugeE.record_hull_eq s hW0 hW.continuousOn hsζ
  have hd' : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun t => Ito.rpath w t + x) v)) := by
    rw [hKU]; exact hd
  have hdA := Supp8.Q3Rel.disjoint_closure_invHull hU s.coe_nonneg hd'
  have hWX : Continuous fun t => Ito.rpath w t + x := (hwc.comp continuous_real_toNNReal).add continuous_const
  have hz : (x : ℂ) + γ t ∈ closure (fwdHull (fun t => Ito.rpath w t + x) v) := by
    rw [ConformalImageFull.fwdHull_add_const (Ito.rpath w) x v]
    have h1 := ReadD.generatingTrace_mem_closure_later hwc hw0 hγ hv0 ht
    have h2 := image_closure_subset_closure_image (f := fun z : ℂ => z + (x : ℂ))
      (continuous_id.add continuous_const) ⟨_, h1, rfl⟩
    have h3 : (x : ℂ) + γ t = (fun z : ℂ => z + (x : ℂ)) (γ t) := add_comm _ _
    rw [h3]
    exact h2
  have hm := ReadD.relBdry_mem_closure_image hU hU0 s.coe_nonneg hWX v.coe_nonneg hdA hz
  -- the relative image of the explored hull is a Loewner hull
  have htip := hα.tendsto_fwdMapInv_tip hW.continuousOn hW0 (show (s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hU' : Continuous (Ito.rpath (W · ω)) := hW.comp continuous_real_toNNReal
  have hU'0 : Ito.rpath (W · ω) 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hW0
  obtain ⟨V, hV, -, -, -, hK⟩ := RootI30.exists_relative_chain hWX hU' hU'0 (by exact_mod_cast hs)
    (by exact_mod_cast hv0) htip hd
  obtain ⟨hv1, hKv⟩ := hK v ⟨v.coe_nonneg, le_rfl⟩
  have hmap : relMap U s = relMap (Ito.rpath (W · ω)) s := GaugeE.record_relMap_eq s hW0 hW.continuousOn hsζ
  have hKv' : relMap U s '' fwdHull (fun t => Ito.rpath w t + x) v =
      fwdHull V (relClock (Ito.rpath (W · ω)) s (fun t => Ito.rpath w t + x) v) := by
    rw [hmap]; exact hKv.symm
  have hbad := Supp8.Q3Rel.relBad_notMem_closure hU hU0 s.coe_nonneg hWX v.coe_nonneg hKv' hdA
  have hy : relBdry U s ((x : ℂ) + γ t) ∈ invGood (Supp8.Q3Rel.relBad U s) := by
    refine ReadD.mem_invGood_of_mem_closure (isHPHull_fwdHull hV hv1).1 hbad ?_
    rw [← hKv']; exact hm
  have hsafe : (x : ℂ) + γ t ∈ relSafe U s := by
    refine ⟨?_, fun h => disjoint_left.mp hdA hz h⟩
    have hsub : closure (fwdHull (fun t => Ito.rpath w t + x) v) ⊆ Hbar := by
      rw [← closure_H]
      exact closure_mono (isHPHull_fwdHull hWX v.coe_nonneg).1
    exact hsub hz
  exact ReadD.inverseRead_relBdry s hΨ hsafe hy

/-- **The root-`x` readback**: the read-back physical trace of a re-centred chain driver (continuous, from `0`, with
the re-centred hull identity at a good horizon `v`) at the root-`x` clock of a time `t < v` is `x + γ t`. -/
theorem physicalTraceX_of_chain {v : ℝ≥0} (hv0 : 0 < v)
    (hv : (v : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) {R : ℝ≥0 → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0)
    (hR : ∀ t ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
        (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) {t : ℝ≥0} (ht : t < v) :
    physicalTraceX x s (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))).toNNReal
      (cfRec s W ζ ω, R) = (x : ℂ) + γ t := by
  set p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) with hp
  set a := fun t => RootH29.forwardCapacity x s t p with hadef
  set U := rdrv (cfRec s W ζ ω) with hUdef
  have he := Gm.isRegularDriver_top hwc hw0
  have hv' : (v : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (w, (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hv
  obtain ⟨-, -, h0', hm', hc', -⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv'
  have h0 : a 0 = 0 := h0'
  have hm : StrictMonoOn a (Icc 0 v) := hm'
  have hc : ContinuousOn a (Icc 0 v) := hc'
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have ha : IsClockOn a (v : ℝ≥0∞) := ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩
  have hgen := GW2Bf.isGeneratingTrace_capacityTip_of_hull W ζ ω hα hW hW0 hζ hs hx harc he hγ hv' hR
  have hat0 : 0 ≤ a t := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, h0]
    · exact le_of_lt (lt_of_eq_of_lt h0.symm (hm ⟨le_rfl, zero_le⟩ ⟨zero_le, ht.le⟩ h))
  have hatv : a t < a v := hm ⟨zero_le, ht.le⟩ ⟨zero_le, le_rfl⟩ ht
  have hu : (((a t).toNNReal : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (a v) := by
    rw [ENNReal.coe_lt_ofReal, Real.coe_toNNReal _ hat0]; exact hatv
  have htrace := LP.traceAt_eq_of_isGeneratingTrace hgen hRc.continuousOn hR0 hu
  have htip : RootI30.capacityTipRead x s v (a t).toNNReal p = relBdry U s ((x : ℂ) + γ t) - relBdry U s x := by
    change RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) (a t).toNNReal) p = _
    rw [ha.invClock_apply (ENNReal.coe_le_coe.2 ht.le)]
    exact RootH29.rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv' ht.le
  -- the root's chart image
  have hsafe0 : (x : ℂ) ∈ relSafe U s := by
    have h := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv' (zero_le : (0 : ℝ≥0) ≤ v)
    rwa [hγ.1, add_zero] at h
  have hc₀im : (relBdry U s x).im = 0 :=
    im_relBdry_of_real (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe0.2
  have hbase : ((baseRead x s (cfRec s W ζ ω) : ℝ) : ℂ) = relBdry U s x := by
    unfold baseRead
    rw [RootA22.boundaryRead_eq_relBdry s _ hsafe0]
    exact Complex.ext (by simp [hUdef]) (by rw [Complex.ofReal_im]; exact hc₀im.symm)
  unfold physicalTraceX
  change inverseRead s (cfRec s W ζ ω, LP.traceAt (a t).toNNReal R + _) = _
  rw [htrace, htip, hbase, sub_add_cancel]
  exact inverseRead_root W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hΨ hv0 hv ht.le

end Readback

end InteractingSLE.Theorem14.GW2Rz
