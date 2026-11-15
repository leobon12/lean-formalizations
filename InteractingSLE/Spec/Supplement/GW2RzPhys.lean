/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzMono
import InteractingSLE.Spec.Supplement.RelSafeGB6Read


/-!
# GW2 at a root `x`: the relative clock and driver read in the physical history (decision D8, layer 3)

Packet PROVE-GW2-ROOTX, round 3. GB6's physical layer (`RelSafeGB6Local`, `RelSafeGB6Drv`, `RelSafeGB6Clock`) at a
root `x`, with J31's capacity readers in place of GB6's local curves. The horizons are `hz t k = min(q_k, t)`:

* `recOf_top_eq`, **`measurable_recPair_le`**: the record pair at a horizon `T` reads the explored driver only on
  `[0, T]`;
* `sepTrX`, `locEvX` (a positive horizon before the root-`x` first contact, through the compact gap), `locLifeX`,
  `locDrvX` (J31's reader life and reader at the horizon), **`physClockX`**, `validEvX`, **`physDrvX`**, `PhysGoodX`;
* on the good event: **`mem_locEvX_iff`**, `clockX_props`, **`physClockX_eq_iSup`** (the root-`x` clock stopped at the
  root-`x` contact), `physClockX_zero`, `monotone_physClockX`, **`continuous_physClockX`** (every sample),
  `physClockX_eq_clockX`;
* `VersionAtX`, **`version_eq_reader`** (Loewner uniqueness, `Sec6.eqOn_of_fwdHull_eq`), **`eq_physDrvX_of_version`**;
* **`measurableSet_locEvX`**, `measurable_locLifeX`, `measurable_locDrvX`, **`measurable_physClockX`**,
  **`measurable_physDrvX`** (every σ-algebra reading the record and the explored driver on `[0, t]`);
* **`exists_goodSetX`**: a measurable good event, almost surely the good records `goodX x s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.ReadD GW2TipSystem
open Supp8.RelSafe (hz hz_le exists_hz_eq selIdx selIdx_mem measurable_selIdx phTr sepRec supBelow
  monotone_supBelow supBelow_zero supBelow_eq_of_lt continuous_supBelow measurable_phTr)

/-! ### The explored record up to a horizon -/

/-- The record of a complete explored driver up to a horizon reads the driver only up to the horizon. -/
theorem recOf_top_eq (T : ℝ≥0) (e : ℝ≥0 → ℝ) :
    recOf (T : ℝ≥0∞) (e, ⊤) = (fun q : ℚ => e (min ((q : ℝ).toNNReal) T), (T : ℝ≥0∞), false) := by
  simp only [recOf, retOf, readRec, min_top_right, ← ENNReal.coe_min, ENNReal.toNNReal_coe, top_le_iff,
    ENNReal.coe_ne_top, decide_false]

/-- **The record pair at a horizon `T` is readable in every σ-algebra reading the counterflow record and the
explored driver on `[0, T]`.** -/
theorem measurable_recPair_le {Ω : Type*} {m : MeasurableSpace Ω} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} (hrec : Measurable[m] (cfRec s W' ζ'))
    (hw : ∀ r ≤ T, Measurable[m] (w r)) : Measurable[m] (recPair s W' ζ' w T) := by
  let _ : MeasurableSpace Ω := m
  have e : (fun ω => recOf (T : ℝ≥0∞) (fun t => w t ω, ⊤)) =
      fun ω => ((fun q : ℚ => w (min ((q : ℝ).toNNReal) T) ω), (T : ℝ≥0∞), false) :=
    funext fun ω => recOf_top_eq T _
  have h2 : Measurable fun ω => recOf (T : ℝ≥0∞) (fun t => w t ω, ⊤) := by
    rw [e]
    exact (measurable_pi_iff.2 fun q => hw _ (min_le_right _ _)).prodMk measurable_const
  exact hrec.prodMk h2

/-! ### The local events, lives and drivers at a root `x` -/

section Defs

variable {Ω : Type*}

open Classical in
/-- The translated physical trace frozen at `T` on the good event (`0` off it). -/
def sepTrX (x : ℝ) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) (ω : Ω) : ℝ≥0 → ℂ :=
  if ω ∈ GT then fun v => (x : ℂ) + phTr w ω (min v T) else 0

/-- **The root-`x` local event with horizon `T`**: `T > 0`, a good sample, and `T` before the root-`x` first contact
(read through the compact inversion gap of the frozen translated prefix and the retained prefix). -/
def locEvX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) :
    Set Ω :=
  {_ω | 0 < T} ∩ GT ∩ {ω | 0 < SourceC.prefixGap (sepTrX x w GT T ω) (sepRec s W' ζ' GT ω) T s}

/-- The life of J31's reader with horizon `T` on its event (`0` off it). -/
def locLifeX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  (locEvX x s W' ζ' w GT T).indicator (fun ω => ENNReal.ofReal (clockX x s W' ζ' w T ω)) ω

/-- J31's capacity reader with horizon `T` on its event (`0` off it). -/
def locDrvX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (T u : ℝ≥0) (ω : Ω) : ℝ :=
  (locEvX x s W' ζ' w GT T).indicator (fun ω => RootJ31.capacityDriverRead x s T u (recPair s W' ζ' w T ω)) ω

/-- **The root-`x` relative clock read in the physical history**: the supremum of the reader lives of the horizons
before `t`. -/
def physClockX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ k, locLifeX x s W' ζ' w GT (hz t k) ω

/-- The horizons before `t` whose reader lives past `u`. -/
def validEvX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (t u : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | (u : ℝ≥0∞) < locLifeX x s W' ζ' w GT (hz t k) ω}

/-- **The root-`x` relative driver read in the physical history**: the reader of the first horizon before `t` whose
reader lives past `u`. -/
def physDrvX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (t u : ℝ≥0) (ω : Ω) : ℝ :=
  locDrvX x s W' ζ' w GT (hz t (selIdx (validEvX x s W' ζ' w GT t u) ω)) u ω

/-- **The pathwise conditions used on the good event at a root `x`**: the explored driver continuous from `0` with
its trace, the counterflow complete with its trace, the protected root arc, the record's trace, and a good record. -/
def PhysGoodX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ)
    (ω : Ω) : Prop :=
  (Continuous (fun t => w t ω) ∧ w 0 ω = 0 ∧ IsGeneratingTrace (fun t => w t ω) ⊤ (γ ω)) ∧
    (IsGeneratingTrace (W' · ω) ⊤ (α ω) ∧ Continuous (W' · ω) ∧ W' 0 ω = 0 ∧ ζ' ω = ⊤) ∧
    (∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1) ∧ (∀ v ≤ s, recordTrace v (cfRec s W' ζ' ω) = α ω v) ∧
    cfRec s W' ζ' ω ∈ goodX x s

end Defs

/-! ### The geometry on the good event -/

section Geometry

variable {Ω : Type*} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ}
  {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}

theorem phTr_eqX {ω : Ω} (hω : PhysGoodX x s W' ζ' w γ α ω) : phTr w ω = γ ω :=
  funext fun _ => LP.traceAt_eq_of_isGeneratingTrace hω.1.2.2 hω.1.1.continuousOn hω.1.2.1 ENNReal.coe_lt_top

theorem continuous_γX {ω : Ω} (hω : PhysGoodX x s W' ζ' w γ α ω) : Continuous (γ ω) := by
  have h := hω.1.2.2.2.1
  simp only [le_top, ofPred_true] at h
  exact continuousOn_univ.1 h

theorem continuous_αX {ω : Ω} (hω : PhysGoodX x s W' ζ' w γ α ω) : Continuous (α ω) := by
  have h := hω.2.1.1.2.1
  simp only [le_top, ofPred_true] at h
  exact continuousOn_univ.1 h

variable (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω)

include hGT in
theorem sepTrX_of_mem {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    sepTrX x w GT T ω = fun v => (x : ℂ) + γ ω (min v T) := by
  classical
  simp only [sepTrX, hω, ↓reduceIte, phTr_eqX (hGT ω hω)]

include hGT in
theorem sepRec_of_memX {ω : Ω} (hω : ω ∈ GT) : sepRec s W' ζ' GT ω = fun v => α ω (min v s) := by
  classical
  simp only [sepRec, hω, ↓reduceIte]
  funext v
  exact (hGT ω hω).2.2.2.1 _ (min_le_right v s)

include hGT in
theorem continuous_sepTrX (T : ℝ≥0) (ω : Ω) : Continuous (sepTrX x w GT T ω) := by
  classical
  by_cases hω : ω ∈ GT
  · rw [sepTrX_of_mem hGT hω]
    exact continuous_const.add ((continuous_γX (hGT ω hω)).comp (continuous_id.min continuous_const))
  · simp only [sepTrX, hω, ↓reduceIte]
    exact continuous_const

include hGT in
theorem continuous_sepRecX (ω : Ω) : Continuous (sepRec s W' ζ' GT ω) := by
  classical
  by_cases hω : ω ∈ GT
  · rw [sepRec_of_memX hGT hω]
    exact (continuous_αX (hGT ω hω)).comp (continuous_id.min continuous_const)
  · simp only [sepRec, hω, ↓reduceIte]
    exact continuous_const

include hGT in
/-- **The root-`x` local event on the good event**: a positive horizon before the root-`x` first contact. -/
theorem mem_locEvX_iff {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    ω ∈ locEvX x s W' ζ' w GT T ↔ 0 < T ∧ (T : ℝ≥0∞) < contactX x s γ α ω := by
  have hxγ : Continuous fun v => (x : ℂ) + γ ω v := continuous_const.add (continuous_γX (hGT ω hω))
  have hA := continuous_sepRecX hGT (s := s) (W' := W') (ζ' := ζ') ω
  have e : SourceC.prefixGap (sepTrX x w GT T ω) (sepRec s W' ζ' GT ω) T s =
      SourceC.prefixGap (fun v => (x : ℂ) + γ ω v) (sepRec s W' ζ' GT ω) T s := by
    unfold SourceC.prefixGap
    refine iInf_congr fun p => ?_
    rw [sepTrX_of_mem hGT hω]
    simp only [min_eq_left p.1.2.2]
  have hc : firstContactTime (fun t => sphereInv (((x : ℂ) + γ ω t : ℂ) : OnePoint ℂ))
      ((fun u => (sepRec s W' ζ' GT ω u : OnePoint ℂ)) '' Icc 0 s) = contactX x s γ α ω := by
    unfold contactX
    exact SourceC.firstContactTime_eq_of_prefix_eq (α := α ω) (fun v hv => by
      rw [sepRec_of_memX hGT hω]; exact congrArg (α ω) (min_eq_left hv))
  have hiff := SourceC.lt_firstContactTime_iff hxγ hA T s
  rw [hc] at hiff
  constructor
  · rintro ⟨⟨hT, -⟩, hgap⟩
    exact ⟨hT, hiff.2 (e ▸ hgap)⟩
  · rintro ⟨hT, hTc⟩
    exact ⟨⟨hT, hω⟩, show 0 < SourceC.prefixGap (sepTrX x w GT T ω) (sepRec s W' ζ' GT ω) T s from
      e ▸ hiff.1 hTc⟩

variable (hs : 0 < s) (hx : 0 ≤ x)

include hGT hs hx in
/-- The root-`x` clock on the good event: `0` at `0`, monotone and continuous before the root-`x` contact. -/
theorem clockX_props {ω : Ω} (hω : ω ∈ GT) :
    ContinuousOn (fun t => ENNReal.ofReal (clockX x s W' ζ' w t ω)) {t | (t : ℝ≥0∞) < contactX x s γ α ω} ∧
      MonotoneOn (fun t => ENNReal.ofReal (clockX x s W' ζ' w t ω)) {t | (t : ℝ≥0∞) < contactX x s γ α ω} ∧
      ENNReal.ofReal (clockX x s W' ζ' w 0 ω) = 0 := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  obtain ⟨h0, hm, hc⟩ := clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  refine ⟨ENNReal.continuous_ofReal.comp_continuousOn hc, fun a ha b hb hab =>
    ENNReal.ofReal_le_ofReal (hm.monotoneOn ha hb hab), ?_⟩
  show ENNReal.ofReal (RootH29.forwardCapacity x s 0 (cfRec s W' ζ' ω, recOf ((0 : ℝ≥0) : ℝ≥0∞) _)) = 0
  rw [h0, ENNReal.ofReal_zero]

include hGT hs hx in
/-- **The root-`x` physical clock on the good event** is the root-`x` clock stopped at the root-`x` contact. -/
theorem physClockX_eq_iSup {t : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    physClockX x s W' ζ' w GT t ω =
      supBelow (fun t' => ENNReal.ofReal (clockX x s W' ζ' w t' ω)) (contactX x s γ α ω) t := by
  obtain ⟨hfc, hfm, hf0⟩ := clockX_props hGT hs hx hω
  refine le_antisymm (iSup_le fun k => ?_) (iSup₂_le fun t' ht' => ?_)
  · unfold locLifeX
    by_cases hk : ω ∈ locEvX x s W' ζ' w GT (hz t k)
    · rw [indicator_of_mem hk]
      have hTc := ((mem_locEvX_iff hGT hω).1 hk).2
      rw [← supBelow_eq_of_lt hfc hfm hf0 hTc]
      exact monotone_supBelow (hz_le t k)
    · rw [indicator_of_notMem hk]
      exact zero_le
  · have hlt : (t' : ℝ≥0∞) < min (t : ℝ≥0∞) (contactX x s γ α ω) :=
      lt_min (ENNReal.coe_lt_coe.2 ht'.1) ht'.2
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hqt : (q : ℝ) < t := by
      have h := hq2.trans_le (min_le_left _ _)
      rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe (by exact_mod_cast hq0)] at h
      exact h
    obtain ⟨k, hk⟩ := exists_hz_eq hqt
    have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < contactX x s γ α ω := hq2.trans_le (min_le_right _ _)
    have hmem : ω ∈ locEvX x s W' ζ' w GT (hz t k) := by
      rw [mem_locEvX_iff hGT hω, hk]
      exact ⟨lt_of_le_of_lt zero_le (ENNReal.coe_lt_coe.1 hq1), hqc⟩
    refine le_trans ?_ (le_iSup _ k)
    rw [locLifeX, indicator_of_mem hmem, hk]
    exact hfm ht'.2 hqc (ENNReal.coe_lt_coe.1 hq1).le

omit hGT in
/-- Off the good event the root-`x` physical clock vanishes. -/
theorem physClockX_eq_zero_of_notMem {t : ℝ≥0} {ω : Ω} (hω : ω ∉ GT) : physClockX x s W' ζ' w GT t ω = 0 := by
  unfold physClockX locLifeX
  exact ENNReal.iSup_eq_zero.2 fun k => indicator_of_notMem (fun h => hω h.1.2) _

include hGT hs hx in
theorem physClockX_zero (ω : Ω) : physClockX x s W' ζ' w GT 0 ω = 0 := by
  by_cases hω : ω ∈ GT
  · rw [physClockX_eq_iSup hGT hs hx hω, supBelow_zero]
  · exact physClockX_eq_zero_of_notMem hω

include hGT hs hx in
theorem monotone_physClockX (ω : Ω) : Monotone fun t => physClockX x s W' ζ' w GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [physClockX_eq_iSup hGT hs hx hω]
    exact monotone_supBelow
  · simp only [physClockX_eq_zero_of_notMem hω]
    exact monotone_const

include hGT hs hx in
theorem continuous_physClockX (ω : Ω) : Continuous fun t => physClockX x s W' ζ' w GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [physClockX_eq_iSup hGT hs hx hω]
    obtain ⟨h1, h2, h3⟩ := clockX_props hGT hs hx hω
    exact continuous_supBelow h1 h2 h3
  · simp only [physClockX_eq_zero_of_notMem hω]
    exact continuous_const

include hGT hs hx in
/-- Before the root-`x` contact the root-`x` physical clock is the root-`x` clock. -/
theorem physClockX_eq_clockX {ω : Ω} (hω : ω ∈ GT) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < contactX x s γ α ω) :
    physClockX x s W' ζ' w GT t ω = ENNReal.ofReal (clockX x s W' ζ' w t ω) := by
  obtain ⟨h1, h2, h3⟩ := clockX_props hGT hs hx hω
  rw [physClockX_eq_iSup hGT hs hx hω]
  exact supBelow_eq_of_lt h1 h2 h3 ht

end Geometry

/-! ### Identification with a version -/

section Ident

variable {Ω : Type*} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ}
  {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hs : 0 < s) (hx : 0 ≤ x)

/-- **The pathwise content of a root-`x` version at one sample**: a continuous relative driver from `0` whose hulls,
at every root-`x` clock value before the root-`x` contact and not after the stop, are the re-centred relative
hulls. -/
def VersionAtX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  Continuous (fun t => R t ω) ∧ R 0 ω = 0 ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω → ENNReal.ofReal (clockX x s W' ζ' w t ω) ≤ V ω →
      fwdHull (fun r : ℝ => R r.toNNReal ω) (clockX x s W' ζ' w t ω) = hullX x s W' ζ' w t ω

include hGT hs hx in
/-- **A root-`x` version is J31's reader** of a good horizon `T` at every relative time below the horizon's clock and
the stop (Loewner uniqueness: both drivers generate the re-centred relative hulls there). -/
theorem version_eq_reader {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hR : VersionAtX x s W' ζ' w γ α R V ω) {T : ℝ≥0} (hT0 : 0 < T) (hTc : (T : ℝ≥0∞) < contactX x s γ α ω)
    {u : ℝ≥0} (hu : (u : ℝ) < clockX x s W' ζ' w T ω) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = RootJ31.capacityDriverRead x s T u (recPair s W' ζ' w T ω) := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  obtain ⟨hRc, hR0, hhull⟩ := hR
  have he := Gm.isRegularDriver_top hwc hw0
  have hv : (T : ℝ≥0∞) < min (contactX x s γ α ω) ((fun t => w t ω), (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hTc
  obtain ⟨RT, hRTc, hRT0, -, hm, hc, hRThull, hRTeq⟩ := reader_eq_chain W' ζ' ω hα hW hW0 hζ hs hx harc he hγ hv hT0
  have hpre : ∀ t ≤ T, clockX x s W' ζ' w t ω =
      RootH29.forwardCapacity x s t (cfRec s W' ζ' ω, recOf (T : ℝ≥0∞) ((fun t => w t ω), ⊤)) := fun t ht =>
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top ht le_rfl
  have hpreH : ∀ t ≤ T, hullX x s W' ζ' w t ω =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W' ζ' ω, recOf (T : ℝ≥0∞) ((fun t => w t ω), ⊤)) : ℝ) :
        ℂ)) '' RootH29.forwardHull x s t (cfRec s W' ζ' ω, recOf (T : ℝ≥0∞) ((fun t => w t ω), ⊤)) := by
    intro t ht
    unfold hullX recPair
    rw [forwardHull_prefix_eq he _ ENNReal.coe_lt_top ht le_rfl]
    rfl
  have hclkc : ContinuousOn (fun t => clockX x s W' ζ' w t ω) (Icc 0 T) :=
    hc.congr fun t ht => hpre t ht.2
  have hclk0 : clockX x s W' ζ' w 0 ω = 0 := by
    have h := (clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ).1
    exact h
  -- the two drivers have the same hulls up to `u`
  have hRc' : Continuous fun r : ℝ => R r.toNNReal ω := hRc.comp continuous_real_toNNReal
  have hRTc' : Continuous fun r : ℝ => RT r.toNNReal := hRTc.comp continuous_real_toNNReal
  have hEq := Sec6.eqOn_of_fwdHull_eq hRc' hRTc' (by simp only [Real.toNNReal_zero, hR0])
    (by simp only [Real.toNNReal_zero, hRT0]) u.coe_nonneg (fun a ha => ?_)
  · have h := hEq ⟨u.coe_nonneg, le_rfl⟩
    simp only [Real.toNNReal_coe] at h
    rw [h]
    refine (hRTeq u ?_).symm
    rw [← hpre T le_rfl]; exact hu
  · obtain ⟨t, ht, hat⟩ := Supp8.GB6.GaugeE.exists_clock_eq hclkc hclk0 (u := a.toNNReal)
      (by rw [Real.coe_toNNReal _ ha.1]; exact ha.2.trans hu.le)
    rw [Real.coe_toNNReal _ ha.1] at hat
    have htc : (t : ℝ≥0∞) < contactX x s γ α ω := (ENNReal.coe_le_coe.2 ht.2).trans_lt hTc
    have hav : ENNReal.ofReal (clockX x s W' ζ' w t ω) ≤ V ω := by
      rw [hat]
      calc ENNReal.ofReal a ≤ ENNReal.ofReal (u : ℝ) := ENNReal.ofReal_le_ofReal ha.2
        _ = (u : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
        _ ≤ V ω := huV
    have h1 := hhull t htc hav
    rw [hat] at h1
    rw [h1, hpreH t ht.2, ← hRThull t ht, ← hpre t ht.2, hat]

include hGT hs hx in
/-- **A root-`x` version is the root-`x` physical relative driver** below the physical clock and up to the stop
(pathwise). -/
theorem eq_physDrvX_of_version {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hR : ω ∈ GT → VersionAtX x s W' ζ' w γ α R V ω) (t u : ℝ≥0)
    (hu : (u : ℝ≥0∞) < physClockX x s W' ζ' w GT t ω) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = physDrvX x s W' ζ' w GT t u ω := by
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hu
  have hv := selIdx_mem (valid := validEvX x s W' ζ' w GT t u) (show ω ∈ validEvX x s W' ζ' w GT t u k from hk)
  set k' := selIdx (validEvX x s W' ζ' w GT t u) ω
  have hmem : ω ∈ locEvX x s W' ζ' w GT (hz t k') := by
    by_contra hn
    have h0 : locLifeX x s W' ζ' w GT (hz t k') ω = 0 := indicator_of_notMem hn _
    have hv' : (u : ℝ≥0∞) < locLifeX x s W' ζ' w GT (hz t k') ω := hv
    rw [h0] at hv'
    exact not_lt_zero hv'
  have hlife : (u : ℝ) < clockX x s W' ζ' w (hz t k') ω := by
    have hv' : (u : ℝ≥0∞) < locLifeX x s W' ζ' w GT (hz t k') ω := hv
    rw [locLifeX, indicator_of_mem hmem] at hv'
    exact ENNReal.coe_lt_ofReal.1 hv'
  have hωG : ω ∈ GT := hmem.1.2
  obtain ⟨hT0, hTc⟩ := (mem_locEvX_iff hGT hωG).1 hmem
  show R u ω = locDrvX x s W' ζ' w GT (hz t k') u ω
  rw [locDrvX, indicator_of_mem hmem]
  exact version_eq_reader hGT hs hx hωG (hR hωG) hT0 hTc hlife huV

end Ident

/-! ### Measurability -/

section Meas

variable {Ω : Type*} {m : MeasurableSpace Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {t : ℝ≥0}
  (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hrec : Measurable[m] (cfRec s W' ζ'))
  (hw : ∀ r ≤ t, Measurable[m] (w r)) (hGTm : MeasurableSet[m] GT)

include hGT hrec hw hGTm in
/-- **The root-`x` local event is readable at every later physical time** (`T ≤ t`). -/
theorem measurableSet_locEvX {T : ℝ≥0} (hTt : T ≤ t) : MeasurableSet[m] (locEvX x s W' ζ' w GT T) := by
  classical
  refine ((MeasurableSet.const _).inter hGTm).inter ?_
  have hγm : ∀ v, Measurable[m] fun ω => sepTrX x w GT T ω v := fun v => by
    have h : (fun ω => sepTrX x w GT T ω v) = fun ω => if ω ∈ GT then (x : ℂ) + phTr w ω (min v T) else 0 := by
      funext ω
      by_cases hω : ω ∈ GT <;> simp [sepTrX, hω]
    rw [h]
    exact Measurable.ite hGTm (measurable_const.add (measurable_phTr hw ((min_le_right v T).trans hTt)))
      measurable_const
  have hαm : ∀ v, Measurable[m] fun ω => sepRec s W' ζ' GT ω v := fun v => by
    have h : (fun ω => sepRec s W' ζ' GT ω v) =
        fun ω => if ω ∈ GT then recordTrace (min v s) (cfRec s W' ζ' ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ GT
      · simp only [sepRec, hω, ↓reduceIte]
        rfl
      · simp [sepRec, hω]
    rw [h]
    exact Measurable.ite hGTm ((measurable_recordTrace _).comp hrec) measurable_const
  exact measurableSet_lt measurable_const (@SourceC.measurable_prefixGap Ω m _ _
    (continuous_sepTrX hGT T) (continuous_sepRecX hGT) hγm hαm T s)

include hGT hrec hw hGTm in
/-- The reader life of a horizon `T ≤ t` is readable at `t`. -/
theorem measurable_locLifeX {T : ℝ≥0} (hTt : T ≤ t) : Measurable[m] (locLifeX x s W' ζ' w GT T) := by
  let _ : MeasurableSpace Ω := m
  have hpm := measurable_recPair_le (w := w) (T := T) hrec fun r hr => hw r (hr.trans hTt)
  exact (ENNReal.measurable_ofReal.comp (RootH29.measurable_forwardCapacity_random x s hpm measurable_const)).indicator
    (measurableSet_locEvX hGT hrec hw hGTm hTt)

include hGT hrec hw hGTm in
/-- J31's reader of a horizon `T ≤ t` is readable at `t`. -/
theorem measurable_locDrvX {T : ℝ≥0} (hTt : T ≤ t) (u : ℝ≥0) : Measurable[m] (locDrvX x s W' ζ' w GT T u) := by
  let _ : MeasurableSpace Ω := m
  have hpm := measurable_recPair_le (w := w) (T := T) hrec fun r hr => hw r (hr.trans hTt)
  exact (RootJ31.measurable_capacityDriverRead_random hpm (measurable_const (a := u)) x s T).indicator
    (measurableSet_locEvX hGT hrec hw hGTm hTt)

include hGT hrec hw hGTm in
/-- **The root-`x` physical clock at `t` reads only the record and the explored driver before `t`.** -/
theorem measurable_physClockX : Measurable[m] (physClockX x s W' ζ' w GT t) := by
  let _ : MeasurableSpace Ω := m
  exact Measurable.iSup fun k => measurable_locLifeX hGT hrec hw hGTm (hz_le t k)

include hGT hrec hw hGTm in
/-- **The root-`x` physical relative driver at `t` reads only the record and the explored driver before `t`.** -/
theorem measurable_physDrvX (u : ℝ≥0) : Measurable[m] (physDrvX x s W' ζ' w GT t u) := by
  have hidx : Measurable[m] (selIdx (validEvX x s W' ζ' w GT t u)) :=
    measurable_selIdx fun k => measurableSet_lt measurable_const
      (measurable_locLifeX hGT hrec hw hGTm (hz_le t k))
  exact @Ito.measurable_comp_index Ω ℝ m _ (fun ω k => locDrvX x s W' ζ' w GT (hz t k) u ω)
    (fun k => measurable_locDrvX hGT hrec hw hGTm (hz_le t k) u) _ hidx

end Meas

/-! ### The good event -/

section Good

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
  {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}

/-- **The root-`x` good event**: measurable, almost surely the good records, and `PhysGoodX` on it. -/
theorem exists_goodSetX (hF : IsFlowLineDriver κ b J θ P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω)) (x : ℝ) (s : ℝ≥0) :
    ∃ GT : Set Ω, (∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) ∧ MeasurableSet GT ∧
      (∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s W' ζ' ω ∈ goodX x s) := by
  have hrecm : Measurable (cfRec s W' ζ') := (measurable_recOf_cfE hF s).2
  have hall : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ (ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0) ∧
      IsGeneratingTrace (W' · ω) (ζ' ω) (α ω) := by
    filter_upwards [hγ, hcf, hα] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hall
  refine ⟨G ∩ cfRec s W' ζ' ⁻¹' goodX x s, fun ω hω => ?_, hGm.inter (hrecm (measurableSet_goodX x s)), ?_⟩
  · obtain ⟨hγω, ⟨hζ, hWc, hW0⟩, hαω⟩ := hG ω hω.1
    rw [hζ] at hαω
    have hαc : Continuous (α ω) :=
      continuousOn_univ.1 (hαω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hAe : ∀ v ≤ s, recordTrace v (cfRec s W' ζ' ω) = α ω v := fun v hv =>
      Supp8.GB6.GaugeE.recordTrace_eq (Wα := W') (ζα := ζ') s hW0 (by rw [hζ]; exact hWc.continuousOn)
        (by rw [hζ]; exact hαω) (by rw [hζ]; exact ENNReal.coe_lt_top) hv
    have hA : ContinuousOn (fun v => recordTrace v (cfRec s W' ζ' ω)) (Iic s) :=
      hαc.continuousOn.congr fun v hv => hAe v hv
    refine ⟨⟨hwc ω, hw0 ω, hγω⟩, ⟨hαω, hWc, hW0, hζ⟩, fun u hu => ?_, hAe, hω.2⟩
    have h := (mem_arcSet_iff hA).1 hω.2.2 u hu
    rwa [hAe u hu.2] at h
  · filter_upwards [hGae] with ω hω
    exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

end Good

end InteractingSLE.Theorem14.GW2Rz
