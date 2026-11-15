/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBLocal

/-!
# The canonical local driver's physical clock and hulls

The driver reconstructed from mapped prefixes generates the actual relative
hulls. Its lifetime covers every relative clock value strictly before the
chosen physical endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open Sec7.PocketTraversal Sec7.Lemma71C

variable {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 < s)
  {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
  {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0}
  (hd : Disjoint (closure (fwdHull U s))
    (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))

include hU hU0 hs htip hw hw0 hγ hd in
/-- The fixed-prefix Loewner chain fills the full boundary-extended curve. -/
theorem exists_relBdry_prefix_driver : ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧
    ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ relClock U s (Ito.rpath w) t ∧
      fwdHull V (relClock U s (Ito.rpath w) t) =
        fillH ((fun r : ℝ => relBdry U s (γ r.toNNReal)) '' Icc 0 t) ∧
      fwdHull V (relClock U s (Ito.rpath w) t) =
        relMap U s '' fwdHull (Ito.rpath w) t := by
  have hwr : Continuous (Ito.rpath w) := hw.comp continuous_real_toNNReal
  have hwz : Ito.rpath w 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hw0
  have hgc : Continuous γ := by
    have h := hγ.2.1
    simp only [le_top, ofPred_true] at h
    exact continuousOn_univ.1 h
  have hfill : ∀ t ∈ Icc (0 : ℝ) T,
      IsFilling (fwdHull (Ito.rpath w) t) ((fun r : ℝ => γ r.toNNReal) '' Icc 0 t) := by
    intro t ht
    have h := hγ.2.2 t.toNNReal ENNReal.coe_lt_top
    rw [← image_Icc_toNNReal, Real.coe_toNNReal _ ht.1] at h
    exact h
  obtain ⟨V, hV, hV0, -, -, -, hK⟩ := exists_relChain_Icc hwr hwz hU hU0 hs htip T.coe_nonneg hd hfill
  have hsafe : MapsTo (fun r : ℝ => γ r.toNNReal) (Icc 0 T) (relSafe U s) := by
    intro r hr
    exact trace_mem_relSafe hU hs.le hw hw0 hγ (Q3Rel.disjoint_closure_invHull hU hs.le hd)
      (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hc : ContinuousOn (fun r : ℝ => relBdry U s (γ r.toNNReal)) (Icc 0 T) :=
    continuousOn_relBdry_comp hU hU0 hs.le (hgc.comp continuous_real_toNNReal).continuousOn hsafe
  refine ⟨V, hV, hV0, fun t ht => ⟨(hK t ht).1, ?_, (hK t ht).2.1⟩⟩
  have hsub : (fun r : ℝ => γ r.toNNReal) '' Icc 0 t ⊆ relSafe U s := by
    rintro _ ⟨r, hr, rfl⟩
    exact hsafe ⟨hr.1, hr.2.trans ht.2⟩
  have hf := isFilling_relBdry_image hU hU0 hs.le hsub (hK t ht).2.2
  rw [image_image] at hf
  have hcompact := isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc_right ht.2))
  exact (fillH_eq_iff_isFilling_of_isClosed hcompact.isBounded hcompact.isClosed (fun z hz => hz.1)).1 hf

include hU hU0 hs htip hw hw0 hγ hd in
/-- The prefix reconstruction clock is exactly GB6's intrinsic relative clock. -/
theorem capClock_localCurve (hT : 0 < T) {u : ℝ} (hu : 0 ≤ u) :
    capClock (localCurve U s γ T) u =
      relClock U s (Ito.rpath w) (clockOf T u) := by
  obtain ⟨V, hV, hV0, hK⟩ := exists_relBdry_prefix_driver hU hU0 hs htip hw hw0 hγ hd
  have hq : clockOf T u ∈ Icc (0 : ℝ) T :=
    ⟨clockOf_nonneg (by exact_mod_cast hT) hu, (clockOf_lt (by exact_mod_cast hT) hu).le⟩
  unfold capClock localCurve
  rw [image_relCurve_Icc _ (by exact_mod_cast hT) hu,
    Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hV hV0 (hK _ hq).1 (hK _ hq).2.1]
  ring

/-- The fixed prefix reparametrization reaches every strictly earlier physical time. -/
theorem exists_clockOf_eq {T : ℝ≥0} {t : ℝ≥0} (ht : t < T) :
    ∃ u : ℝ, 0 ≤ u ∧ clockOf T u = t := by
  refine ⟨(t : ℝ) / (T - t), div_nonneg t.coe_nonneg (sub_nonneg.2 (by exact_mod_cast ht.le)), ?_⟩
  have h : (0 : ℝ) < T - t := sub_pos.2 (by exact_mod_cast ht)
  unfold clockOf
  field_simp
  nlinarith

include hU hU0 hs htip hw hw0 hγ hd in
/-- Every strict physical prefix lies strictly before the canonical driver's lifetime. -/
theorem relClock_lt_localLife (hT : 0 < T) {t : ℝ≥0} (ht : t < T) :
    ENNReal.ofReal (relClock U s (Ito.rpath w) t) < capLife (localCurve U s γ T) := by
  obtain ⟨u, hu, he⟩ := exists_clockOf_eq ht
  rw [← he, ← capClock_localCurve hU hU0 hs htip hw hw0 hγ hd hT hu]
  exact (isDrivenCurve_localCurve hU hU0 hs htip hw hw0 hγ hT hd).ofReal_capClock_lt hu

include hU hU0 hs htip hw hw0 hγ hd in
/-- The reconstructed measurable driver generates GB6's relative hulls. -/
theorem fwdHull_localDriver (hT : 0 < T) {t : ℝ≥0} (ht : t < T) :
    fwdHull (fun r : ℝ => drivenDriver (fun _ : Unit => localCurve U s γ T) r.toNNReal ())
      (relClock U s (Ito.rpath w) t) = relMap U s '' fwdHull (Ito.rpath w) t := by
  obtain ⟨u, hu, he⟩ := exists_clockOf_eq ht
  have hc := isDrivenCurve_localCurve hU hU0 hs htip hw hw0 hγ hT hd
  have hk := fwdHull_drivenDriver (fun _ : Unit => hc) () hu
  rw [capClock_localCurve hU hU0 hs htip hw hw0 hγ hd hT hu, he] at hk
  rw [hk, localCurve, image_relCurve_Icc _ (by exact_mod_cast hT) hu, he]
  obtain ⟨V, -, -, hK⟩ := exists_relBdry_prefix_driver hU hU0 hs htip hw hw0 hγ hd
  exact (hK t ⟨t.coe_nonneg, by exact_mod_cast ht.le⟩).2.1.symm.trans
    (hK t ⟨t.coe_nonneg, by exact_mod_cast ht.le⟩).2.2

/-- Every live local capacity time is below a physical relative clock value. -/
theorem lt_localLife_iff {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 < s) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hd : Disjoint (closure (QuantumZipper.fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' QuantumZipper.fwdHull (Ito.rpath w) T))) (r : ℝ≥0) :
    (r : ℝ≥0∞) < Sec7.Lemma71C.capLife (localCurve U s γ T) ↔
      ∃ t : ℝ≥0, t < T ∧ (r : ℝ) < relClock U s (Ito.rpath w) t := by
  constructor
  · intro hr
    have hr' : ENNReal.ofReal (r : ℝ) < Sec7.Lemma71C.capLife (localCurve U s γ T) := by
      rwa [ENNReal.ofReal_coe_nnreal]
    obtain ⟨n, _, hn⟩ := (isDrivenCurve_localCurve hU hU0 hs htip hw hw0 hγ hT hd).exists_pos_lt_capClock
      r.coe_nonneg hr'
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hq0 := Sec7.PocketTraversal.clockOf_nonneg (by exact_mod_cast hT) hn0
    refine ⟨⟨Sec7.PocketTraversal.clockOf T n, hq0⟩,
      Sec7.PocketTraversal.clockOf_lt (by exact_mod_cast hT) hn0, ?_⟩
    rwa [capClock_localCurve hU hU0 hs htip hw hw0 hγ hd hT hn0] at hn
  · rintro ⟨t, ht, hr⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal hr.le).trans_lt
      (relClock_lt_localLife hU hU0 hs htip hw hw0 hγ hd hT ht)

end InteractingSLE.Supp8.GB6.CoordB
