/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6ReadDMeas

/-!
# Causal Borel physical trace reconstruction

At a live local capacity time the canonical relative driver determines the
full mapped trace, including its real visits. The inverse boundary readout
then recovers the physical trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Supp8.GB6.ReadD

open Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- The physical trace read from the retained record and relative driver. -/
def physicalTrace (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℂ :=
  inverseRead s (p.1, LP.traceAt t p.2)

theorem measurable_physicalTrace (s t : ℝ≥0) : Measurable (physicalTrace s t) :=
  (measurable_inverseRead s).comp
    (measurable_fst.prodMk ((LP.measurable_traceAt t).comp measurable_snd))

/-- The readout at time `t` depends only on the relative driver through `t`. -/
theorem physicalTrace_congr (s t : ℝ≥0) (r : RecData) {w w' : ℝ≥0 → ℝ}
    (h : ∀ u ≤ t, w u = w' u) : physicalTrace s t (r, w) = physicalTrace s t (r, w') := by
  unfold physicalTrace
  rw [LP.traceAt_congr h]

/-- The canonical Borel driver has the capacity-parametrized trace of its
underlying driven curve at every live capacity time. -/
theorem traceAt_drivenDriver {Γ : ℝ → ℂ} (hc : IsDrivenCurve Γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < capLife Γ) :
    LP.traceAt v (fun u => CoordB.drivenDriver (fun _ : Unit => Γ) u ()) = capTrace Γ v := by
  obtain ⟨b, hvb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hv
  have he : ∀ u ≤ v, CoordB.drivenDriver (fun _ : Unit => Γ) u () = segDriver Γ u := by
    intro u hu
    exact CoordB.drivenDriver_eq (γ := fun _ : Unit => Γ) (ω := ())
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hv)
  calc
    _ = LP.traceAt v (segDriver Γ) := LP.traceAt_congr he
    _ = capTrace Γ v := LP.traceAt_eq_of_isGeneratingTrace (hc.isGeneratingTrace hb)
      (hc.segDriver_spec.2.1.mono fun u hu => hu.trans hb) hc.segDriver_spec.1 hvb

section Local

variable {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 < s)
  {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
  {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
  (hd : Disjoint (closure (fwdHull U s))
    (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))

include hU hU0 hs htip hw hw0 hγ hT hd

/-- The Borel trace selector of the canonical local relative driver is the
full boundary-extended physical trace at the relative clock. -/
theorem traceAt_localDriver {t : ℝ≥0} (ht : t < T) :
    LP.traceAt (relClock U s (Ito.rpath w) t).toNNReal
      (fun v => CoordB.drivenDriver (fun _ : Unit => CoordB.localCurve U s γ T) v ()) =
        CoordB.relBdry U s (γ t) := by
  let Γ := CoordB.localCurve U s γ T
  have hc : IsDrivenCurve Γ := CoordB.isDrivenCurve_localCurve hU hU0 hs htip hw hw0 hγ hT hd
  obtain ⟨u, hu, he⟩ := CoordB.exists_clockOf_eq ht
  have ha : capClock Γ u = relClock U s (Ito.rpath w) t := by
    rw [CoordB.capClock_localCurve hU hU0 hs htip hw hw0 hγ hd hT hu, he]
  have hnn : 0 ≤ relClock U s (Ito.rpath w) t := ha ▸ hc.capClock_nonneg hu
  have hlive : ((relClock U s (Ito.rpath w) t).toNNReal : ℝ≥0∞) < capLife Γ := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hnn]
    exact CoordB.relClock_lt_localLife hU hU0 hs htip hw hw0 hγ hd hT ht
  have hsel := traceAt_drivenDriver hc hlive
  change LP.traceAt _ (fun v => CoordB.drivenDriver (fun _ : Unit => Γ) v ()) = _
  rw [hsel]
  unfold capTrace
  rw [Real.coe_toNNReal _ hnn, ← ha, hc.capInv_eq hu]
  change CoordB.relBdry U s (γ (clockOf T u).toNNReal) = _
  rw [he, Real.toNNReal_coe]

end Local

/-- Forward boundary extension sends closed explored hulls into closed
relative hulls. This includes the real points of those closures. -/
theorem relBdry_mem_closure_image {U W : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s t : ℝ} (hs : 0 ≤ s) (hW : Continuous W) (ht : 0 ≤ t)
    (hd : Disjoint (closure (fwdHull W t)) (closure (Q3Rel.invHull U s)))
    {z : ℂ} (hz : z ∈ closure (fwdHull W t)) :
    CoordB.relBdry U s z ∈ closure (relMap U s '' fwdHull W t) := by
  have hsafe : closure (fwdHull W t) ⊆ CoordB.relSafe U s := by
    intro v hv
    refine ⟨?_, fun h => Set.disjoint_left.1 hd hv h⟩
    rw [← closure_H]
    exact closure_mono (isHPHull_fwdHull hW ht).1 hv
  have hc := (CoordB.continuousOn_relBdry hU hU0 hs).mono hsafe
  have he : CoordB.relBdry U s '' fwdHull W t = relMap U s '' fwdHull W t := by
    apply Set.image_congr
    intro v hv
    exact CoordB.relBdry_eq hU hs ((isHPHull_fwdHull hW ht).1 hv)
      (hsafe (subset_closure hv)).2
  rw [← he]
  exact hc.image_closure ⟨z, hz, rfl⟩

/-- A generating trace at any earlier time belongs to the closed later hull. -/
theorem generatingTrace_mem_closure_later {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    {t : ℝ≥0} (ht : t ≤ T) : γ t ∈ closure (fwdHull (Ito.rpath w) T) := by
  have hwr : Continuous (Ito.rpath w) := hw.comp continuous_real_toNNReal
  have hwz : Ito.rpath w 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hw0
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from zero_le) with h0 | h0
  · rw [← h0, hγ.1]
    exact ConformalImageFull.zero_mem_closure_fwdHull hwr hwz (by exact_mod_cast hT)
  · have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hw.continuousOn hw0
      (show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
    have hm := YuanCorollary13.mem_closure_fwdHull_of_tendsto hwr hwz
      (show (0 : ℝ) < t by exact_mod_cast h0) htip
    exact closure_mono (fwdHull_mono' (by exact_mod_cast ht)) hm

/-- The physical trace is recovered at every strict physical prefix time.
The retained-chart hypothesis is supplied by the existing no-return theorem;
there is no interior-tip restriction on the explored trace at `t`. -/
theorem physicalTrace_localDriver (s : ℝ≥0) {r : RecData} (hs : 0 < s)
    (hΨ : Q3Rel.IsRetainedChartOff (Q3Rel.invHull (rdrv r) s) (relMap (rdrv r) s)
      (relInv (rdrv r) s) (Q3Rel.relLog (rdrv r) s) (Q3Rel.relBad (rdrv r) s))
    {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv (rdrv r) s) (𝓝[H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hd : Disjoint (closure (fwdHull (rdrv r) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))
    {t : ℝ≥0} (ht : t < T) :
    physicalTrace s (relClock (rdrv r) s (Ito.rpath w) t).toNNReal
      (r, fun v => CoordB.drivenDriver (fun _ : Unit => CoordB.localCurve (rdrv r) s γ T) v ()) = γ t := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  unfold physicalTrace
  rw [traceAt_localDriver hU hU0 hs' htip hw hw0 hγ hT hd ht]
  have hdA := Q3Rel.disjoint_closure_invHull hU s.coe_nonneg hd
  have hsafe := CoordB.trace_mem_relSafe hU s.coe_nonneg hw hw0 hγ hdA ht.le
  apply inverseRead_relBdry s hΨ hsafe
  obtain ⟨V, hV, hV0, hK⟩ := CoordB.exists_relBdry_prefix_driver hU hU0 hs' htip hw hw0 hγ hd
  have hKV := (hK T ⟨T.coe_nonneg, le_rfl⟩).2.2.symm
  have hm := relBdry_mem_closure_image hU hU0 s.coe_nonneg
    (hw.comp continuous_real_toNNReal) T.coe_nonneg hdA
    (generatingTrace_mem_closure_later hw hw0 hγ hT ht.le)
  change CoordB.relBdry (rdrv r) s (γ t) ∈ closure (relMap (rdrv r) s '' fwdHull (Ito.rpath w) T) at hm
  rw [hKV] at hm
  exact mem_invGood_of_mem_closure (isHPHull_fwdHull hV (hK T ⟨T.coe_nonneg, le_rfl⟩).1).1
    (Q3Rel.relBad_notMem_closure hU hU0 s.coe_nonneg (hw.comp continuous_real_toNNReal)
      T.coe_nonneg hKV hdA) hm

end InteractingSLE.Supp8.GB6.ReadD
