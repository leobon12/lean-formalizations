/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBPrefix

/-!
# A driven relative curve on a separated physical prefix

The mapped continuous curve, including its real visits, has local Loewner
drivers by GB6's existing fixed-hull restriction. This supplies the geometric
premise for the measurable driver construction in `GB6CoordBPrefix`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open Q3Rel (invHull)

/-- Every point of a generating prefix is safe for the relative chart when
the closed counterflow hull misses the inverted retained hull. -/
theorem trace_mem_relSafe {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s)
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0}
    (hd : Disjoint (closure (fwdHull (fun r : ℝ => w r.toNNReal) T)) (closure (invHull U s)))
    {t : ℝ≥0} (ht : t ≤ T) : γ t ∈ relSafe U s := by
  refine ⟨Sec7.IsGeneratingTrace.mem_Hbar hγ hw.continuousOn hw0 le_top, ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from zero_le) with ht0 | ht0
  · rw [← ht0, hγ.1]
    exact zero_notMem_closure_invHull hU hs
  · have hwr : Continuous (fun r : ℝ => w r.toNNReal) := hw.comp continuous_real_toNNReal
    have hwz : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw0
    have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hw.continuousOn hw0
      (show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
    have hmem := YuanCorollary13.mem_closure_fwdHull_of_tendsto hwr hwz
      (show (0 : ℝ) < t by exact_mod_cast ht0) htip
    have hsub := closure_mono ((QuantumZipper.fwdHull_mono (W := fun r : ℝ => w r.toNNReal)).1
      (show (t : ℝ) ≤ T by exact_mod_cast ht))
    exact fun hA => Set.disjoint_left.1 hd (hsub hmem) hA

/-- The relative curve of one separated physical prefix, parametrized on
`[0,∞)` by a fixed rational map onto `[0,T)`. -/
def localCurve (U : ℝ → ℝ) (s : ℝ) (γ : ℝ≥0 → ℂ) (T : ℝ≥0) : ℝ → ℂ :=
  Sec7.PocketTraversal.relCurve (fun t => relBdry U s (γ t.toNNReal)) T

/-- GB6's fixed-hull restriction gives a driven curve on every separated
physical prefix. Real counterflow visits are allowed. -/
theorem isDrivenCurve_localCurve {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 < s) {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hd : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) T))) :
    Sec7.PocketTraversal.IsDrivenCurve (localCurve U s γ T) := by
  have hwr : Continuous (fun r : ℝ => w r.toNNReal) := hw.comp continuous_real_toNNReal
  have hwz : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw0
  have hgc : Continuous γ := by
    have h := hγ.2.1
    simp only [le_top, ofPred_true] at h
    exact continuousOn_univ.1 h
  have hd' := Q3Rel.disjoint_closure_invHull hU hs.le hd
  apply isDrivenCurve_relBdry hU hU0 hs.le (by exact_mod_cast hT)
    ((hgc.comp continuous_real_toNNReal).continuousOn) (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hγ.1)
  · intro u hu
    exact trace_mem_relSafe hU hs.le hw hw0 hγ hd'
      (Real.toNNReal_le_iff_le_coe.2 hu.2.le)
  · intro S hS hST
    have hdis : Disjoint (closure (fwdHull U s))
        (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun r : ℝ => w r.toNNReal) S)) :=
      hd.mono_right (closure_mono (image_mono (QuantumZipper.fwdHull_mono.1 hST.le)))
    have hfill : ∀ t ∈ Icc (0 : ℝ) S, IsFilling
        (fwdHull (fun r : ℝ => w r.toNNReal) t) ((fun r : ℝ => γ r.toNNReal) '' Icc 0 t) := by
      intro t ht
      have hfill := hγ.2.2 t.toNNReal ENNReal.coe_lt_top
      rw [← image_Icc_toNNReal, Real.coe_toNNReal _ ht.1] at hfill
      exact hfill
    obtain ⟨V, hV, hV0, ha0, ham, hac, hK⟩ := exists_relChain_Icc hwr hwz hU hU0 hs htip hS.le hdis hfill
    exact ⟨V, hV, hV0, relClock U s (fun r : ℝ => w r.toNNReal), ha0, ham, hac,
      fun t ht => ⟨(hK t ht).1, (hK t ht).2.2⟩⟩

end InteractingSLE.Supp8.GB6.CoordB
