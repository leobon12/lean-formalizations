/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeCore
import InteractingSLE.Spec.Supplement.GB6GaugeEVersion

/-!
# GB6's relative driver read in the physical history, part 1: local curves on physical prefixes

Packet PROVE-GB6-RELSAFE. GB6's relative driver at relative time `u < a(T)` is the canonical driver (`segDriver`) of
the mapped local curve `localCurve (rdrv r) s (traceAt · W) T` (PROVE-GB6-VERSION's `CoordB` atlas), which reads the
physical driver only before `T`. Here everything is built from the record `gb6Rec` and the physical driver alone:

* `phTr`: the physical trace read from the driver (`LP.traceAt`, all samples);
* `gb6Curve`: the local relative curve with horizon `T`, `locEv`: the event (good sample on the record event, with
  `T` before the first contact, read through the measurable compact gap `prefixGap`);
* `PhysGood`: the pathwise conditions used (continuous physical driver with its trace, the flow prefix, the record and
  its tip);
* **`isDrivenCurve_of_mem_locEv`**, **`lt_gb6Tc_of_mem_locEv`**: the geometry on the event;
* **`measurableSet_locEv`**, **`measurable_indicator_gb6Curve`**: for `T ≤ t`, the event and the local curve are
  readable in `physSigma (gb6Rec) W t ⊔ 𝒩` (the curve reads the trace only before `T`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.RelSafe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Sec7.Lemma71C Sec7.PocketTraversal

section Defs

variable {Ω : Type*}

/-- The physical trace read from the driver (every sample). -/
def phTr (W : ℝ≥0 → Ω → ℝ) (ω : Ω) (v : ℝ≥0) : ℂ := LP.traceAt v (fun r => W r ω)

/-- **GB6's local relative curve with physical horizon `T`**, built from the record and the physical driver. -/
def gb6Curve (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω) : ℝ → ℂ :=
  CoordB.localCurve (rdrv (gb6Rec s Wα ζα ω)) s (phTr W ω) T

open Classical in
/-- The physical trace frozen at `T` on the good event (`0` off it): a continuous curve for every sample. -/
def sepTr (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) (ω : Ω) : ℝ≥0 → ℂ :=
  if ω ∈ GT then fun v => phTr W ω (min v T) else 0

open Classical in
/-- The retained trace of the record frozen at `s` on the good event (`0` off it). -/
def sepRec (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (ω : Ω) : ℝ≥0 → ℂ :=
  if ω ∈ GT then fun v => ReadD.recordTrace (min v s) (gb6Rec s Wα ζα ω) else 0

/-- **The local event with horizon `T`**: `T > 0`, a good sample, and `T` before the first contact (the compact
inversion gap of the frozen physical prefix and the retained prefix is positive). -/
def locEv (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (T : ℝ≥0) : Set Ω :=
  {_ω | 0 < T} ∩ GT ∩ {ω | 0 < SourceC.prefixGap (sepTr W GT T ω) (sepRec s Wα ζα GT ω) T s}

/-- **The pathwise conditions used on the good event**: the physical driver is continuous from `0` with its trace,
the flow prefix is regular, the sample lies on the interior-tip event, its record is good, and the record's retained
map has the tip `α(s)`. -/
def PhysGood (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ) (ω : Ω) : Prop :=
  (Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
    (Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω} ∧
      IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) ∧
    (s : ℝ≥0∞) < ζα ω ∧ α ω s ∈ H ∧ GB6RecGood s Wα ζα α ω ∧
    Tendsto (QuantumZipper.fwdMapInv (rdrv (gb6Rec s Wα ζα ω)) s) (𝓝[H] 0) (𝓝 (α ω s))

end Defs

section Geometry

variable {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

theorem rpath_rdrv (r : RecData) : Ito.rpath (fun t : ℝ≥0 => rdrv r t) = rdrv r := by
  funext x
  simp only [Ito.rpath, rdrv, Real.toNNReal_coe]

omit hGT in
/-- On a good sample the trace reader is the trace. -/
theorem phTr_eq {ω : Ω} (hω : PhysGood s W Wα ζα γ α ω) : phTr W ω = γ ω := by
  funext v
  exact LP.traceAt_eq_of_isGeneratingTrace hω.1.2.2 hω.1.1.continuousOn hω.1.2.1 ENNReal.coe_lt_top

omit hGT in
theorem continuous_γ {ω : Ω} (hω : PhysGood s W Wα ζα γ α ω) : Continuous (γ ω) := by
  have h := hω.1.2.2.2.1
  simp only [le_top, ofPred_true] at h
  exact continuousOn_univ.1 h

include hGT in
theorem sepTr_of_mem {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) : sepTr W GT T ω = fun v => γ ω (min v T) := by
  classical
  simp only [sepTr, hω, ↓reduceIte, phTr_eq (hGT ω hω)]

include hGT in
theorem sepRec_of_mem {ω : Ω} (hω : ω ∈ GT) : sepRec s Wα ζα GT ω = fun v => α ω (min v s) := by
  classical
  obtain ⟨-, ⟨h0, hc, hα⟩, hs, -⟩ := hGT ω hω
  simp only [sepRec, hω, ↓reduceIte]
  funext v
  exact GaugeE.recordTrace_eq s h0 hc hα hs (min_le_right v s)

include hGT in
theorem continuous_sepTr (T : ℝ≥0) (ω : Ω) : Continuous (sepTr W GT T ω) := by
  classical
  by_cases hω : ω ∈ GT
  · rw [sepTr_of_mem hGT hω]
    exact (continuous_γ (hGT ω hω)).comp (continuous_id.min continuous_const)
  · simp only [sepTr, hω, ↓reduceIte]
    exact continuous_const

include hGT in
theorem continuous_sepRec (ω : Ω) : Continuous (sepRec s Wα ζα GT ω) := by
  classical
  by_cases hω : ω ∈ GT
  · rw [sepRec_of_mem hGT hω]
    obtain ⟨-, ⟨-, -, hα⟩, hs, -⟩ := hGT ω hω
    refine hα.2.1.comp_continuous (continuous_id.min continuous_const) fun v => ?_
    show ((min v s : ℝ≥0) : ℝ≥0∞) ≤ ζα ω
    exact (ENNReal.coe_le_coe.2 (min_le_right v s)).trans hs.le
  · simp only [sepRec, hω, ↓reduceIte]
    exact continuous_const

include hGT in
/-- **On the local event, `T` is before GB6's first contact.** -/
theorem lt_gb6Tc_of_mem_locEv {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv s W Wα ζα GT T) :
    (T : ℝ≥0∞) < gb6Tc s γ α ω := by
  obtain ⟨⟨-, hωG⟩, hgap⟩ := hω
  have hg := hGT ω hωG
  have hγc := continuous_γ hg
  have hA := continuous_sepRec hGT (s := s) (Wα := Wα) (ζα := ζα) ω
  have e : SourceC.prefixGap (sepTr W GT T ω) (sepRec s Wα ζα GT ω) T s =
      SourceC.prefixGap (γ ω) (sepRec s Wα ζα GT ω) T s := by
    unfold SourceC.prefixGap
    refine iInf_congr fun p => ?_
    rw [sepTr_of_mem hGT hωG]
    simp only [min_eq_left p.1.2.2]
  have hgap' : 0 < SourceC.prefixGap (γ ω) (sepRec s Wα ζα GT ω) T s := by
    rw [← e]; exact hgap
  have h := (SourceC.lt_firstContactTime_iff hγc hA T s).2 hgap'
  unfold gb6Tc
  rwa [SourceC.firstContactTime_eq_of_prefix_eq (α := α ω) (fun v hv => by
    rw [sepRec_of_mem hGT hωG]; exact congrArg (α ω) (min_eq_left hv))] at h

include hGT in
/-- **The geometric data of the local curve on the local event** (the `hgeom` input of the `CoordB` lemmas). -/
theorem geom_of_mem_locEv {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv s W Wα ζα GT T) :
    ∃ (w : ℝ≥0 → ℝ) (p : ℂ), Continuous w ∧ w 0 = 0 ∧ IsGeneratingTrace w ⊤ (phTr W ω) ∧
      Tendsto (QuantumZipper.fwdMapInv (rdrv (gb6Rec s Wα ζα ω)) s) (𝓝[H] 0) (𝓝 p) ∧
      Disjoint (closure (fwdHull (rdrv (gb6Rec s Wα ζα ω)) s))
        (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)) := by
  have hTc := lt_gb6Tc_of_mem_locEv hGT hω
  obtain ⟨⟨-, hωG⟩, -⟩ := hω
  obtain ⟨⟨hWc, hW0, hγ⟩, ⟨h0, hc, hα⟩, hs, -, -, htip⟩ := hGT ω hωG
  refine ⟨fun t => W t ω, α ω s, hWc, hW0, ?_, htip, ?_⟩
  · rw [phTr_eq (hGT ω hωG)]; exact hγ
  · have hd := GB6.disjoint_closure_fwdHull_of_lt_firstContactTime hα hc h0 hγ hWc.continuousOn hW0 hs
      ENNReal.coe_lt_top hTc
    rw [GaugeE.record_hull_eq s h0 hc hs]
    exact hd

include hGT in
/-- **The local curve is driven on the local event.** -/
theorem isDrivenCurve_of_mem_locEv {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv s W Wα ζα GT T) :
    IsDrivenCurve (gb6Curve s W Wα ζα T ω) := by
  obtain ⟨w, p, hw, hw0, hγ, htip, hd⟩ := geom_of_mem_locEv hGT hω
  have hT : 0 < T := hω.1.1
  have hs : (0 : ℝ) < s := by
    obtain ⟨-, ⟨-, -, hα⟩, -, hαs, -⟩ := hGT ω hω.1.2
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
    · exfalso
      rw [← h, hα.1] at hαs
      simp [QuantumZipper.H] at hαs
    · exact_mod_cast h
  exact CoordB.isDrivenCurve_localCurve (continuous_rdrv _) (rdrv_zero _) hs htip hw hw0 hγ hT hd

end Geometry

section Meas

variable {Ω : Type*} {m : MeasurableSpace Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
  {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {t : ℝ≥0}

/-- The physical trace reader at a time `v ≤ t` is measurable for every σ-algebra reading the driver on `[0, t]`. -/
theorem measurable_phTr (hW : ∀ r ≤ t, Measurable[m] (W r)) {v : ℝ≥0} (hv : v ≤ t) :
    Measurable[m] fun ω => phTr W ω v := by
  have hpath : Measurable[m] fun ω => LP.freezeAt t (fun r => W r ω) :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) m _ _).2 fun r => hW (min r t) (min_le_right r t)
  have he : (fun ω => phTr W ω v) = fun ω => LP.traceAt v (LP.freezeAt t (fun r => W r ω)) := by
    funext ω
    refine LP.traceAt_congr fun r hr => ?_
    show W r ω = W (min r t) ω
    rw [min_eq_left (hr.trans hv)]
  rw [he]
  exact (LP.measurable_traceAt v).comp hpath

variable (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable[m] (gb6Rec s Wα ζα))
  (hW : ∀ r ≤ t, Measurable[m] (W r)) (hGTm : MeasurableSet[m] GT)

include hGT hrec hW hGTm in
/-- **The local event is readable at every later physical time** (`T ≤ t`). -/
theorem measurableSet_locEv {T : ℝ≥0} (hTt : T ≤ t) : MeasurableSet[m] (locEv s W Wα ζα GT T) := by
  classical
  refine ((MeasurableSet.const _).inter hGTm).inter ?_
  have hγm : ∀ v, Measurable[m] fun ω => sepTr W GT T ω v := fun v => by
    have h : (fun ω => sepTr W GT T ω v) = fun ω => if ω ∈ GT then phTr W ω (min v T) else 0 := by
      funext ω
      by_cases hω : ω ∈ GT <;> simp [sepTr, hω]
    rw [h]
    exact Measurable.ite hGTm (measurable_phTr hW ((min_le_right v T).trans hTt)) measurable_const
  have hαm : ∀ v, Measurable[m] fun ω => sepRec s Wα ζα GT ω v := fun v => by
    have h : (fun ω => sepRec s Wα ζα GT ω v) =
        fun ω => if ω ∈ GT then ReadD.recordTrace (min v s) (gb6Rec s Wα ζα ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ GT <;> simp [sepRec, hω]
    rw [h]
    exact Measurable.ite hGTm ((ReadD.measurable_recordTrace _).comp hrec) measurable_const
  exact measurableSet_lt measurable_const (@SourceC.measurable_prefixGap Ω m _ _
    (continuous_sepTr hGT T) (continuous_sepRec hGT) hγm hαm T s)

include hGT hrec hW hGTm in
/-- **The local curve is readable on the local event** (it reads the physical trace only before `T ≤ t`). -/
theorem measurable_indicator_gb6Curve {T : ℝ≥0} (hTt : T ≤ t) (v : ℝ) (hv : 0 ≤ v) :
    Measurable[m] ((locEv s W Wα ζα GT T).indicator fun ω => gb6Curve s W Wα ζα T ω v) := by
  have hE := measurableSet_locEv hGT hrec hW hGTm hTt
  by_cases hT : 0 < T
  swap
  · have he : locEv s W Wα ζα GT T = ∅ := by
      ext ω; simp only [locEv, mem_inter_iff, mem_ofPred_eq, hT, false_and, mem_empty_iff_false]
    rw [he, indicator_empty]
    exact measurable_const
  have hVm : ∀ r : ℝ≥0, Measurable[m] fun ω => rdrv (gb6Rec s Wα ζα ω) r := fun r =>
    (measurable_rdrv_apply (r : ℝ)).comp hrec
  have hz : Measurable[m] fun ω => phTr W ω (clockOf T v).toNNReal :=
    measurable_phTr hW ((Real.toNNReal_le_iff_le_coe.2 (clockOf_lt (by exact_mod_cast hT) hv).le).trans hTt)
  have h := CoordB.measurable_indicator_relBdry (mΩ := m) (V := fun r ω => rdrv (gb6Rec s Wα ζα ω) r) hVm
    (fun ω => (continuous_rdrv _).comp NNReal.continuous_coe) (fun ω => rdrv_zero _) s hE hz ?_
  · convert h using 2 with ω
    simp only [gb6Curve, CoordB.localCurve, relCurve, rpath_rdrv]
  · intro ω hω
    obtain ⟨w, p, hw, hw0, hγ, htip, hd⟩ := geom_of_mem_locEv hGT hω
    rw [rpath_rdrv]
    have hd' := Q3Rel.disjoint_closure_invHull (continuous_rdrv _) s.coe_nonneg hd
    exact CoordB.trace_mem_relSafe (continuous_rdrv _) s.coe_nonneg hw hw0 hγ hd'
      (Real.toNNReal_le_iff_le_coe.2 (clockOf_lt (by exact_mod_cast hT) hv).le)

include hGT hrec hW hGTm in
/-- **GB6's local relative driver with horizon `T ≤ t` is readable at `t`.** -/
theorem measurable_indicator_localDrv {T : ℝ≥0} (hTt : T ≤ t) (u : ℝ≥0) :
    Measurable[m] ((locEv s W Wα ζα GT T).indicator (CoordB.drivenDriver (gb6Curve s W Wα ζα T) u)) :=
  @CoordB.measurable_indicator_drivenDriver Ω m _ _ (measurableSet_locEv hGT hrec hW hGTm hTt)
    (fun _ hω => isDrivenCurve_of_mem_locEv hGT hω) (measurable_indicator_gb6Curve hGT hrec hW hGTm hTt) u

include hGT hrec hW hGTm in
/-- **The lifetime of the local relative curve with horizon `T ≤ t` is readable at `t`.** -/
theorem measurable_indicator_localLife {T : ℝ≥0} (hTt : T ≤ t) :
    Measurable[m] ((locEv s W Wα ζα GT T).indicator fun ω => capLife (gb6Curve s W Wα ζα T ω)) :=
  @CoordB.measurable_indicator_capLife Ω m _ _ (measurableSet_locEv hGT hrec hW hGTm hTt)
    (fun _ hω => isDrivenCurve_of_mem_locEv hGT hω) (measurable_indicator_gb6Curve hGT hrec hW hGTm hTt)

end Meas

end InteractingSLE.Supp8.RelSafe
