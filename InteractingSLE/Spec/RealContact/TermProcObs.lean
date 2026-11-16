/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermProcDefs

/-!
# The chart path of the first path is observed in the physical filtration

Packet PROVE-RC-TERM, second run (ruling R124). The physical filtration is the landed one at the lines `(t, N)`,
`RLC.AStopProc.fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N` (`t ↦ retSigma76 … (0 + t) N`): the first path up to time `t` and
the second path up to `N`, which on `{ζ₂ ≤ N}` is the completed second path.

* `recDom`, `isOpen_recDom`, `measurableSet_mem_recDom`, `measurable_recFwd`: the domain and the forward map of the
  builder-frame chart are measurable functions of the record;
* **`termObs`**: on an event `M` of good samples (`Term.IsTermGood`), measurable for `retSigma76 … 0 N`, the chart path
  `Term.pPath` with the physical stop `Term.pStop` satisfies `RLC.AStopProc.AObs`: its coordinates
  (`Restart.RetAux79.measurable_contPath_of_past` in the builder frame, the record through the bridge
  `Term.measurable_recOf_retSigma76`) and its survival events
  (`RLC.AStopProc.measurableSet_lt_contStopA_of_prefix`) are observed.

R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly Sec7.Lemma76F RLC.AStopProc
open Exist.StagedLaw (markPos markPosL)

/-! ### The builder-frame chart of a record -/

/-- The domain of the builder-frame chart of a record. -/
def recDom (d : ℝ) (r : RecData) : Set ℂ := (fun z : ℂ => z + (d : ℂ)) '' (H \ fwdHull (-(rdrv r)) (rtime r))

theorem isOpen_recDom (d : ℝ) (r : RecData) : IsOpen (recDom d r) := by
  have h1 := QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv r).neg (rtime_nonneg r)
  have h2 := (Homeomorph.addRight (d : ℂ)).isOpenMap _ h1
  rwa [Homeomorph.coe_addRight] at h2

theorem mem_recDom_iff {d : ℝ} {r : RecData} {z : ℂ} :
    z ∈ recDom d r ↔ 0 < z.im ∧ ∃ u, IsForwardSol (-(rdrv r)) (z - (d : ℂ)) (rtime r) u := by
  have hV : Continuous (-(rdrv r)) := (continuous_rdrv r).neg
  constructor
  · rintro ⟨w, ⟨hwH, hwK⟩, rfl⟩
    have hw0 : 0 < w.im := hwH
    refine ⟨by simpa using hw0, ?_⟩
    rw [add_sub_cancel_right]
    exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull (rtime_nonneg r) hwH hwK
  · rintro ⟨hz, u, hu⟩
    have hzH : 0 < (z - (d : ℂ)).im := by simpa using hz
    exact ⟨z - (d : ℂ), ⟨hzH, Ito.notMem_fwdHull_of_isForwardSol hV hzH (rtime_nonneg r) hu⟩,
      sub_add_cancel z (d : ℂ)⟩

theorem measurableSet_mem_recDom (d : ℝ) (z : ℂ) : MeasurableSet {r : RecData | z ∈ recDom d r} := by
  have h := (measurable_fwdMap_param (W := fun (r : RecData) (s : ℝ) => -rdrv r s)
    (fun r => (continuous_rdrv r).neg) (fun t => (measurable_rdrv_apply t).neg)
    (fun r => by simp [rdrv_zero r]) measurable_rtime rtime_nonneg
    (measurable_const (a := z - (d : ℂ)))).2
  by_cases hz : 0 < z.im
  · have e : {r : RecData | z ∈ recDom d r} =
        {r : RecData | ∃ u, IsForwardSol (fun s => -rdrv r s) (z - (d : ℂ)) (rtime r) u} := by
      ext r
      rw [mem_ofPred_eq, mem_recDom_iff]
      exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
    rw [e]
    exact h
  · have e : {r : RecData | z ∈ recDom d r} = ∅ := by
      ext r
      rw [mem_ofPred_eq, mem_recDom_iff]
      simp [hz]
    rw [e]
    exact MeasurableSet.empty

theorem measurable_recFwd (d : ℝ) (z : ℂ) :
    Measurable fun r : RecData => (entryChart (-(rdrv r)) (rtime r) d).1 z := by
  have h1 := (measurable_fwdMap_param (W := fun (r : RecData) (s : ℝ) => -rdrv r s)
    (fun r => (continuous_rdrv r).neg) (fun t => (measurable_rdrv_apply t).neg)
    (fun r => by simp [rdrv_zero r]) measurable_rtime rtime_nonneg
    (measurable_const (a := z - (d : ℂ)))).1
  have h2 := measurable_markPosL (W := fun (r : RecData) (s : ℝ) => -rdrv r s)
    (fun r => (continuous_rdrv r).neg) (fun t => (measurable_rdrv_apply t).neg)
    (fun r => by simp [rdrv_zero r]) measurable_rtime rtime_nonneg (measurable_const (a := -d))
  exact h1.sub (Complex.measurable_ofReal.comp h2)

/-- On an entry datum the domain of the record is the domain of the entry chart. -/
theorem IsEntryData.entryDom_eq {V : ℝ → ℝ} {T : ℝ} {ξ : ℝ → ℂ} {p d : ℝ} (h : IsEntryData V T ξ p d) :
    entryDom ξ T d = (fun z : ℂ => z + (d : ℂ)) '' (H \ fwdHull V T) := by
  rw [entryDom, h.fillH_entryPath, ← image_add_real_H_diff]

/-! ### The observation structure -/

section Obs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The chart path of the first path against the completed second path is observed in the physical
filtration** (see the module docstring). -/
theorem termObs {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {g : Ω → DistOn upperHalfPlaneOpens}
    {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : Measurable E) (hreg : ∀ ω, IsRegularDriver (E ω))
    (hE2 : ∀ ω, (E ω).2 = ζ₂ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun t => η₂ ω t - x₂))
    (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂) {N : ℝ≥0} {η₁' : Ω → ℝ≥0 → ℂ}
    (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    {ηc₂ : Ω → ℝ≥0 → ℂ} (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hmc₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s))
    (ηc₁ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (hc₁ : ∀ t ω, Continuous (ηc₁ t ω))
    (hmc₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (capR t N) (ζ₁ ω) s))
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] M)
    (hMg : ∀ ω ∈ M, IsTermGood N E ηc₂ η₁' ζ₁ x₁ x₂ ω) :
    AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂)
      (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) := by
  classical
  set d : ℝ := x₁ - x₂ with hd
  have hrec : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (pRec N E) :=
    measurable_recOf_retSigma76 hκ hEm hreg hE2 hfl htrace hζ₂ hc₂ hmc₂ hag₂
  have hmono : ∀ t : ℝ≥0, retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N ≤ retSigma76 P η₁ η₂ ζ₁ ζ₂ t N := fun t =>
    retSigma76_mono P η₁ η₂ ζ₁ ζ₂ zero_le le_rfl
  have hg : ∀ ω ∈ M, IsAGood (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω := fun ω hω =>
    (hMg ω hω).isAGood
  -- the builder-frame chart of the record
  set D₁ : Ω → Set ℂ := fun ω => recDom d (pRec N E ω) with hD₁
  set φ₁ : Ω → ℂ → ℂ := fun ω => (entryChart (-(pU N E ω)) (pT N E ω : ℝ) d).1 with hφ₁
  have hDo : ∀ ω, IsOpen (D₁ ω) := fun ω => isOpen_recDom d _
  have hDm : ∀ z, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] {ω | z ∈ D₁ ω} := fun z =>
    hrec (measurableSet_mem_recDom d z)
  have hφm : ∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] ({ω | z ∈ D₁ ω}.indicator fun ω => φ₁ ω z) :=
    fun z => (((measurable_recFwd d z).comp hrec : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N]
      fun ω => φ₁ ω z)).indicator (hDm z)
  have hDeq : ∀ ω ∈ M, D₁ ω = entryDom (fun s => reflectC (pRho₂ ηc₂ x₂ ω s)) (pT N E ω : ℝ) d := by
    intro ω hω
    obtain ⟨q, w, -, hs⟩ := (hMg ω hω).sample
    rw [(IsPathSample.entry hs).entryDom_eq]
    rfl
  -- survival
  have hsurv : ∀ t : ℝ≥0, MeasurableSet[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N t]
      (M ∩ {ω | (t : ℝ≥0∞) < pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω}) := by
    intro t
    change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (0 + t) N] _
    rw [zero_add]
    have hMt : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] M := hmono t _ hM
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · subst t
      have he : M ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω} = M := by
        ext ω
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [ENNReal.coe_zero]; exact (hMg ω h).pStop_pos⟩⟩
      rw [he]
      exact hMt
    have hA : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] (M ∩ {ω | (t : ℝ≥0∞) < ζ₁ ω}) := by
      have he : {ω | (t : ℝ≥0∞) < ζ₁ ω} = {ω | lifeRec (ζ₁ ω) t = ⊤} := by
        ext ω
        exact (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).symm
      rw [he]
      exact hMt.inter (measurable_lifeRec_retSigma76_left P η₁ η₂ ζ₁ ζ₂ hζ₁ t N (measurableSet_singleton ⊤))
    have hreadη : ∀ s ≤ t, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N]
        ((M ∩ {ω | (t : ℝ≥0∞) < ζ₁ ω}).indicator fun ω => η₁' ω s) := by
      intro s hs
      apply measurable_indicator_retSigma76_of_reader hA (hm₁ s)
        (measurable_capped_left_retSigma76 (hc₁ t) (hmc₁ t) (hag₁ t) hs)
      filter_upwards [ha₁, hag₁ t] with ω he hcω hω
      rw [hcω s, capTime_of_le _ _ (le_min ((ENNReal.coe_le_coe.2 hs).trans hω.2.le)
        (ENNReal.coe_le_coe.2 (hs.trans (lt_capR_left t N).le)))]
      exact he s ((ENNReal.coe_le_coe.2 hs).trans hω.2.le)
    have hreadβ : ∀ s ≤ N, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N]
        ((M ∩ {ω | (t : ℝ≥0∞) < ζ₁ ω}).indicator fun ω => ηc₂ ω s) := fun s hs =>
      ((measurable_capped_right_retSigma76 hc₂ hmc₂ hag₂ hs).mono (hmono t) le_rfl).indicator hA
    have hm := @measurableSet_lt_contStopA_of_prefix Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ t N) M η₁' η₁' ηc₂ ζ₁
      0 t 0 N ht hA hreadη (fun s hs => hreadη s (hs.trans zero_le)) hreadβ
      (fun ω hω hζ => (hMg ω hω).path.continuousOn.mono fun s hs => (ENNReal.coe_le_coe.2 hs).trans hζ.le)
      (fun ω hω hζ => isPathGood_continuousAt (hMg ω hω).path hζ)
      (fun ω hω => (hMg ω hω).path.continuousOn.mono fun s (hs : s ≤ 0) => by
        show (s : ℝ≥0∞) ≤ ζ₁ ω
        rw [le_antisymm hs zero_le]
        exact zero_le)
      (fun ω _ => (hc₂ ω).continuousOn)
    have he : M ∩ {ω | (t : ℝ≥0∞) < pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω} =
        M ∩ {ω | (t : ℝ≥0∞) < contStop (η₁' ω) (ζ₁ ω) 0 (η₁' ω '' Icc 0 0 ∪ ηc₂ ω '' Icc 0 N)} := by
      ext ω
      refine and_congr_right fun hω => ?_
      show (t : ℝ≥0∞) < pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω ↔ _
      rw [(hMg ω hω).pStop_eq]
      exact Iff.rfl
    rw [he]
    exact hm
  have hM₀ : MeasurableSet[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N 0] M := by
    change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (0 + 0) N] M
    rw [add_zero]
    exact hM
  refine ⟨hM₀, ?_, hsurv⟩
  intro t s hst
  change Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ (0 + t) N] _
  rw [zero_add]
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have hs : s = 0 := le_antisymm hst zero_le
    subst s
    have he : (M.indicator fun ω => pPath N E ηc₂ η₁' ζ₁ x₁ x₂ ω 0) = fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ M
      · simp only [indicator_of_mem hω]
        exact (hg ω hω).zero
      · exact indicator_of_notMem hω _
    rw [he]
    exact measurable_const
  have hMt : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] M := hmono t _ hM
  -- the killed and clipped proxy of the first path, in the builder frame
  set ηk := retObservedPath M η₁' ζ₁ (capR t N) t with hηk
  have hmη : ∀ q, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] fun ω => ηk ω q := fun q =>
    measurable_retObservedPath_retSigma76_left hMt hm₁ hζ₁ (fun ω hω => (hMg ω hω).path) ha₁ (hc₁ t) (hmc₁ t)
      (hag₁ t) q
  set β : Ω → ℝ≥0 → ℂ := fun ω q => reflectC (pRho₁ η₁' x₁ ω q) with hβ
  set βk : Ω → ℝ≥0 → ℂ := fun ω q => reflectC (ηk ω q - (x₁ : ℂ)) with hβk
  have hmβk : ∀ q, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] fun ω => βk ω q := fun q =>
    LP.continuous_reflectC.measurable.comp ((hmη q).sub measurable_const)
  have hcβk : ∀ ω ∈ M, Continuous (βk ω) := fun ω _ =>
    LP.continuous_reflectC.comp
      ((continuous_retObservedPath (fun ω hω => (hMg ω hω).path) _ _ ω).sub continuous_const)
  have hsurvt : ∀ s : ℝ≥0, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ s N]
      (M ∩ {ω | (s : ℝ≥0∞) < pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω}) := fun s => by
    have := hsurv s
    change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (0 + s) N] _ at this
    rwa [zero_add] at this
  have hVm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N]
      (M.indicator fun ω => min (pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω) (t : ℝ≥0∞)) := by
    have h := measurable_indicator_min_of_survival (𝓖 := fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) hM₀ hsurv t
    change Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ (0 + t) N] _ at h
    rwa [zero_add] at h
  have hprefix : ∀ ω ∈ M, ∀ q : ℝ≥0,
      (q : ℝ≥0∞) < min (pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω) (t : ℝ≥0∞) → βk ω (0 + q) = β ω (0 + q) := by
    intro ω hω q hq
    have hqt : q < t := ENNReal.coe_lt_coe.1 ((lt_min_iff.1 hq).2)
    have hζ : (q : ℝ≥0∞) ≤ ζ₁ ω := ((lt_min_iff.1 hq).1.trans_le IsKSample.kStop_le).le
    simp only [hβk, hβ, hηk, retObservedPath, indicator_of_mem hω, zero_add, min_eq_left hqt.le, pRho₁]
    rw [capTime_of_le _ _ (le_min hζ (ENNReal.coe_le_coe.2 (hqt.le.trans (lt_capR_left t N).le)))]
  suffices hm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] (M.indicator fun ω =>
      contPath (D₁ ω) (φ₁ ω) (β ω) 0 (pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω) s) by
    have he : (M.indicator fun ω => pPath N E ηc₂ η₁' ζ₁ x₁ x₂ ω s) = fun ω => reflectC
        ((M.indicator fun ω => contPath (D₁ ω) (φ₁ ω) (β ω) 0 (pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω) s) ω) := by
      funext ω
      by_cases hω : ω ∈ M
      · simp only [indicator_of_mem hω, hDeq ω hω]
        rfl
      · simp only [indicator_of_notMem hω]
        simp [reflectC]
    rw [he]
    exact LP.continuous_reflectC.measurable.comp hm
  apply @measurable_contPath_of_past Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ t N) M hMt D₁ hDo
    (fun z => hmono t _ (hDm z)) φ₁ (fun z => (hφm z).mono (hmono t) le_rfl) β βk hmβk hcβk 0 t ht
    (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) hVm (fun ω hω => (hMg ω hω).pStop_pos) hprefix ?_ ?_ ?_ s hst
  · intro ω hω q hq
    obtain ⟨q', w, -, hs⟩ := (hMg ω hω).sample
    rw [hDeq ω hω, zero_add]
    exact IsPathSample.mem_closure hs hq.le
  · intro ω hω q hq
    obtain ⟨q', w, -, hs⟩ := (hMg ω hω).sample
    rw [hDeq ω hω, zero_add]
    exact (IsPathSample.entry hs).exists_tendsto_fwd (IsPathSample.mem_closure hs hq.le)
  · intro ω hω
    obtain ⟨q', w, -, hs⟩ := (hMg ω hω).sample
    rw [hDeq ω hω]
    exact IsPathSample.continuous_chartPath hs

end Obs

end Term

end InteractingSLE.RealContact
