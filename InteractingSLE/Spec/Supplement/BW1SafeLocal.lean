/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeGB6Read
import InteractingSLE.Spec.Supplement.BW1VerClock

/-!
# BW1's relative driver read in the physical history, part 1: local curves on physical prefixes

Packet PROVE-BW1-SAFELAW. GB6's `RelSafeGB6Local` with the retained time read from the record: BW1's relative driver
at relative time `u` is the canonical driver of the mapped local curve
`localCurve (rdrv r) (recS r) (traceAt · W) T` (the retained piece stops at the record's own time `recS r`, BW1's
threshold time). Everything is built from the record `rec` and the physical driver `W`:

* `BGood`: the pathwise conditions (`BW1Ver.IsGoodSample` with the record's trace and the physical trace reader);
* `bCurve`, `bTc` (the first contact), `locEv` (positive horizon `T` before the first contact, read through the
  frozen physical prefix and the record's trace cut to the good event);
* **`mem_locEv_iff`**, **`isDrivenCurve_of_mem_locEv`**: the geometry on the event;
* **`measurableSet_locEv`**, **`measurable_indicator_bCurve`**, `measurable_indicator_localDrv`,
  `measurable_indicator_localLife`: for `T ≤ t` the event, the local curve, its driver and its lifetime are readable
  in every σ-algebra reading the record and the physical driver before `t` (the random own time enters through
  `BW1Ver.measurableSet_lt_contactT` and `BW1Ver.measurable_indicator_relBdry_rand`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.RelSafe Sec7.Lemma71C Sec7.PocketTraversal BW1Ver

section Defs

variable {Ω : Type*}

/-- **BW1's good sample**: `BW1Ver.IsGoodSample` for the record, its retained trace and the physical driver with its
trace reader. -/
def BGood (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : Prop :=
  IsGoodSample (rec ω) (fun v => recordTrace v (rec ω)) (W · ω) (phTr W ω)

open Classical in
/-- The record's retained trace on the good event (`0` off it). -/
def sepA (rec : Ω → RecData) (GT : Set Ω) (ω : Ω) : ℝ≥0 → ℂ :=
  if ω ∈ GT then fun v => recordTrace v (rec ω) else 0

/-- **BW1's local relative curve with physical horizon `T`.** -/
def bCurve (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ → ℂ :=
  CoordB.localCurve (rdrv (rec ω)) (recS (rec ω)) (phTr W ω) T

/-- **BW1's first contact time** of the physical counterflow with the retained piece. -/
def bTc (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  contactT (phTr W ω) (fun v => recordTrace v (rec ω)) (recS (rec ω))

/-- **The local event with horizon `T`**: `T > 0`, a good sample, and `T` before the first contact (read through the
frozen physical prefix). -/
def locEv (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) : Set Ω :=
  {_ω | 0 < T} ∩ GT ∩ {ω | (T : ℝ≥0∞) < contactT (sepTr W GT T ω) (sepA rec GT ω) (recS (rec ω))}

end Defs

section Geometry

variable {Ω : Type*} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, BGood rec W ω)

theorem sepTr_of_mem' {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) : sepTr W GT T ω = fun v => phTr W ω (min v T) := by
  classical
  simp only [sepTr, hω, ↓reduceIte]

theorem sepA_of_mem {ω : Ω} (hω : ω ∈ GT) : sepA rec GT ω = fun v => recordTrace v (rec ω) := by
  classical
  simp only [sepA, hω, ↓reduceIte]

include hGT in
theorem continuous_sepTr' (T : ℝ≥0) (ω : Ω) : Continuous (sepTr W GT T ω) := by
  classical
  by_cases hω : ω ∈ GT
  · rw [sepTr_of_mem' hω]
    exact (hGT ω hω).continuous_γ.comp (continuous_id.min continuous_const)
  · simp only [sepTr, hω, ↓reduceIte]
    exact continuous_const

include hGT in
theorem continuous_sepA (ω : Ω) : Continuous (sepA rec GT ω) := by
  classical
  by_cases hω : ω ∈ GT
  · rw [sepA_of_mem hω]
    exact (hGT ω hω).continuous_A
  · simp only [sepA, hω, ↓reduceIte]
    exact continuous_const

include hGT in
/-- On the good event the contact event of the frozen prefix is the contact event of the trace. -/
theorem lt_contactT_sepTr_iff {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    (T : ℝ≥0∞) < contactT (sepTr W GT T ω) (sepA rec GT ω) (recS (rec ω)) ↔ (T : ℝ≥0∞) < bTc rec W ω := by
  have hg := hGT ω hω
  unfold bTc contactT
  rw [SourceC.lt_firstContactTime_iff (continuous_sepTr' hGT T ω) (continuous_sepA hGT ω),
    SourceC.lt_firstContactTime_iff hg.continuous_γ hg.continuous_A]
  have e : SourceC.prefixGap (sepTr W GT T ω) (sepA rec GT ω) T (recS (rec ω)) =
      SourceC.prefixGap (phTr W ω) (fun v => recordTrace v (rec ω)) T (recS (rec ω)) := by
    unfold SourceC.prefixGap
    refine iInf_congr fun p => ?_
    rw [sepTr_of_mem' hω, sepA_of_mem hω]
    simp only [min_eq_left p.1.2.2]
  rw [e]

include hGT in
/-- **The local event on the good event**: a positive horizon before the first contact. -/
theorem mem_locEv_iff {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    ω ∈ locEv rec W GT T ↔ 0 < T ∧ (T : ℝ≥0∞) < bTc rec W ω := by
  refine ⟨fun h => ⟨h.1.1, (lt_contactT_sepTr_iff hGT hω).1 h.2⟩,
    fun h => ⟨⟨h.1, hω⟩, (lt_contactT_sepTr_iff hGT hω).2 h.2⟩⟩

include hGT in
theorem lt_bTc_of_mem_locEv {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv rec W GT T) : (T : ℝ≥0∞) < bTc rec W ω :=
  ((mem_locEv_iff hGT hω.1.2).1 hω).2

theorem pos_recS_of_bGood {ω : Ω} (hω : BGood rec W ω) : (0 : ℝ) < recS (rec ω) := by
  exact_mod_cast hω.pos

include hGT in
/-- **The geometric data of the local curve on the local event** (the `hgeom` input of the `CoordB` lemmas). -/
theorem geom_of_mem_locEv {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv rec W GT T) :
    ∃ (w : ℝ≥0 → ℝ) (p : ℂ), Continuous w ∧ w 0 = 0 ∧ IsGeneratingTrace w ⊤ (phTr W ω) ∧
      Tendsto (QuantumZipper.fwdMapInv (rdrv (rec ω)) (recS (rec ω))) (𝓝[H] 0) (𝓝 p) ∧
      Disjoint (closure (fwdHull (rdrv (rec ω)) (recS (rec ω))))
        (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)) := by
  have hTc := lt_bTc_of_mem_locEv hGT hω
  have hg := hGT ω hω.1.2
  exact ⟨fun t => W t ω, _, hg.cont, hg.zero, hg.ctrace, hg.tip, hg.disjoint hTc⟩

include hGT in
/-- **The local curve is driven on the local event.** -/
theorem isDrivenCurve_of_mem_locEv {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv rec W GT T) :
    IsDrivenCurve (bCurve rec W T ω) := by
  obtain ⟨w, p, hw, hw0, hγ, htip, hd⟩ := geom_of_mem_locEv hGT hω
  exact CoordB.isDrivenCurve_localCurve (continuous_rdrv _) (rdrv_zero _) (pos_recS_of_bGood (hGT ω hω.1.2)) htip
    hw hw0 hγ hω.1.1 hd

end Geometry

section Meas

variable {Ω : Type*} {m : MeasurableSpace Ω} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {t : ℝ≥0}
  (hGT : ∀ ω ∈ GT, BGood rec W ω) (hrec : Measurable[m] rec)
  (hW : ∀ r ≤ t, Measurable[m] (W r)) (hGTm : MeasurableSet[m] GT)

include hGT hrec hW hGTm in
/-- **The local event is readable at every later physical time** (`T ≤ t`). -/
theorem measurableSet_locEv {T : ℝ≥0} (hTt : T ≤ t) : MeasurableSet[m] (locEv rec W GT T) := by
  classical
  refine ((MeasurableSet.const _).inter hGTm).inter ?_
  have hγm : ∀ v, Measurable[m] fun ω => sepTr W GT T ω v := fun v => by
    have h : (fun ω => sepTr W GT T ω v) = fun ω => if ω ∈ GT then phTr W ω (min v T) else 0 := by
      funext ω
      by_cases hω : ω ∈ GT <;> simp [sepTr, hω]
    rw [h]
    exact Measurable.ite hGTm (measurable_phTr hW ((min_le_right v T).trans hTt)) measurable_const
  have hαm : ∀ v, Measurable[m] fun ω => sepA rec GT ω v := fun v => by
    have h : (fun ω => sepA rec GT ω v) = fun ω => if ω ∈ GT then recordTrace v (rec ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ GT <;> simp [sepA, hω]
    rw [h]
    exact Measurable.ite hGTm ((measurable_recordTrace v).comp hrec) measurable_const
  exact measurableSet_lt_contactT (mΩ := m) (continuous_sepTr' hGT T) (continuous_sepA hGT) hγm hαm
    (measurable_recS.comp hrec) T

include hGT hrec hW hGTm in
/-- **The local curve is readable on the local event** (it reads the physical trace only before `T ≤ t`). -/
theorem measurable_indicator_bCurve {T : ℝ≥0} (hTt : T ≤ t) (v : ℝ) (hv : 0 ≤ v) :
    Measurable[m] ((locEv rec W GT T).indicator fun ω => bCurve rec W T ω v) := by
  have hE := measurableSet_locEv hGT hrec hW hGTm hTt
  by_cases hT : 0 < T
  swap
  · have he : locEv rec W GT T = ∅ := by
      ext ω; simp only [locEv, mem_inter_iff, mem_ofPred_eq, hT, false_and, mem_empty_iff_false]
    rw [he, indicator_empty]
    exact measurable_const
  have hVm : ∀ r : ℝ≥0, Measurable[m] fun ω => rdrv (rec ω) r := fun r =>
    (measurable_rdrv_apply (r : ℝ)).comp hrec
  have hz : Measurable[m] fun ω => phTr W ω (clockOf T v).toNNReal :=
    measurable_phTr hW ((Real.toNNReal_le_iff_le_coe.2 (clockOf_lt (by exact_mod_cast hT) hv).le).trans hTt)
  have h := measurable_indicator_relBdry_rand (mΩ := m) (V := fun r ω => rdrv (rec ω) r) hVm
    (fun ω => (continuous_rdrv _).comp NNReal.continuous_coe) (fun ω => rdrv_zero _)
    (measurable_recS.comp hrec) hE hz ?_
  · convert h using 2 with ω
    simp only [bCurve, CoordB.localCurve, relCurve, BW1Ver.rpath_rdrv, Function.comp_apply]
  · intro ω hω
    obtain ⟨w, p, hw, hw0, hγ, htip, hd⟩ := geom_of_mem_locEv hGT hω
    rw [BW1Ver.rpath_rdrv]
    have hd' := Supp8.Q3Rel.disjoint_closure_invHull (continuous_rdrv _) (recS (rec ω)).coe_nonneg hd
    exact CoordB.trace_mem_relSafe (continuous_rdrv _) (recS (rec ω)).coe_nonneg hw hw0 hγ hd'
      (Real.toNNReal_le_iff_le_coe.2 (clockOf_lt (by exact_mod_cast hT) hv).le)

include hGT hrec hW hGTm in
/-- **BW1's local relative driver with horizon `T ≤ t` is readable at `t`.** -/
theorem measurable_indicator_localDrv {T : ℝ≥0} (hTt : T ≤ t) (u : ℝ≥0) :
    Measurable[m] ((locEv rec W GT T).indicator (CoordB.drivenDriver (bCurve rec W T) u)) :=
  @CoordB.measurable_indicator_drivenDriver Ω m _ _ (measurableSet_locEv hGT hrec hW hGTm hTt)
    (fun _ hω => isDrivenCurve_of_mem_locEv hGT hω) (measurable_indicator_bCurve hGT hrec hW hGTm hTt) u

include hGT hrec hW hGTm in
/-- **The lifetime of the local relative curve with horizon `T ≤ t` is readable at `t`.** -/
theorem measurable_indicator_localLife {T : ℝ≥0} (hTt : T ≤ t) :
    Measurable[m] ((locEv rec W GT T).indicator fun ω => capLife (bCurve rec W T ω)) :=
  @CoordB.measurable_indicator_capLife Ω m _ _ (measurableSet_locEv hGT hrec hW hGTm hTt)
    (fun _ hω => isDrivenCurve_of_mem_locEv hGT hω) (measurable_indicator_bCurve hGT hrec hW hGTm hTt)

end Meas

end InteractingSLE.Theorem14.BW1Safe
