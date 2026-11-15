/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConst
import InteractingSLE.Spec.Sec7.Aux50HitPath

/-!
# The image word before a forward time from the two stopped histories (deterministic part)

Packet PROVE-WW-B19 (Astra's follow-up note, E.6: "R and a mapped stopped prefix recover its original geometric
prefix"). For the named input `ImgMarksStatement`, the image word before the forward time `t` must be read from the
forward history stopped at `t` and the reverse history stopped at `s`. This file sets up the deterministic side:

* `revStop_revStop` and its consequences: every frozen reverse datum is a function of the stopped reverse history;
* congruence of the killed-arc functionals: `capClock_congr`, `locDrv_congr`, `IsKilledArc.congr`,
  `IsKilledArc.inter_Iio`, **`kW_eq_of_eqOn`**, `kVL_eq_of_eqOn`, `kVR_eq_of_eqOn`,
  `IsKilledArc.exists_lt_capClock_lt`;
* the stopped data `stopData t s p = (stopHistory t (killedHistory p.1), revStop s p.2)`, measurable for the marks
  `twoSlitMarks t s` (`measurable_stopData`);
* the curve read from stopped data: `alphaY`, `GY`, `gammaY`, `PcY`, `PY`, `gXLY`, `gXRY`, and on good samples
  (`StopGood`: good glued sample with a good forward path) their identification with the image word's data
  (`alphaY_stopData`, `gammaY_stopData`, `mem_PcY_stopData_iff`, `isKilledArc_gammaY_stopData`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique Sec4

/-! ### Constant stops are idempotent -/

theorem stopHistory_const_stopHistory_const {nL nR : ℕ} (c : ℝ≥0) (y : HistorySpace nL nR) :
    stopHistory (fun _ => c) (stopHistory (fun _ => c) y) = stopHistory (fun _ => c) y := by
  simp only [stopHistory, Prod.mk.injEq, true_and]
  funext p
  split_ifs <;> rfl

theorem revStop_revStop (s : ℚ) (y : HistorySpace 1 1) : revStop s (revStop s y) = revStop s y :=
  stopHistory_const_stopHistory_const _ y

theorem frzDrive_revStop (s : ℚ) (y : HistorySpace 1 1) : frzDrive s (revStop s y) = frzDrive s y := by
  rw [frzDrive, frzDrive, revStop_revStop]

theorem frzLine_revStop (s : ℚ) (y : HistorySpace 1 1) : frzLine s (revStop s y) = frzLine s y := by
  funext u
  rw [frzLine, frzLine, frzDrive_revStop]

theorem frzVL_revStop (s : ℚ) (y : HistorySpace 1 1) : frzVL s (revStop s y) = frzVL s y := by
  rw [frzVL, frzVL, revStop_revStop]

theorem frzVR_revStop (s : ℚ) (y : HistorySpace 1 1) : frzVR s (revStop s y) = frzVR s y := by
  rw [frzVR, frzVR, revStop_revStop]

theorem revDrv0_revStop (s : ℚ) (y : HistorySpace 1 1) : revDrv0 s (revStop s y) = revDrv0 s y := by
  funext u
  rw [revDrv0, revDrv0, frzDrive_revStop]

/-! ### Congruence of the killed-arc functionals -/

section Congr

variable {γ γ' : ℝ → ℂ} {P P' : Set ℝ}

theorem capClock_congr {u : ℝ} (h : EqOn γ γ' (Icc 0 u)) : capClock γ u = capClock γ' u := by
  rw [capClock, capClock, image_congr h]

theorem locDrv_congr {S : ℝ} (h : EqOn γ γ' (Icc 0 S)) : locDrv γ S = locDrv γ' S := by
  have e : (fun W : ℝ → ℝ => Continuous W ∧ W 0 = 0 ∧ ∀ u ∈ Icc 0 S, fwdHull W (capClock γ u) = γ '' Ioc 0 u) =
      fun W => Continuous W ∧ W 0 = 0 ∧ ∀ u ∈ Icc 0 S, fwdHull W (capClock γ' u) = γ' '' Ioc 0 u := by
    funext W
    refine propext (and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun u hu => ?_)
    have hu' : EqOn γ γ' (Icc 0 u) := h.mono (Icc_subset_Icc_right hu.2)
    rw [capClock_congr hu', image_congr (hu'.mono Ioc_subset_Icc_self)]
  unfold locDrv
  rw [e]

theorem IsKilledArc.congr (hγ : IsKilledArc γ P) (h : EqOn γ γ' P) : IsKilledArc γ' P where
  zero_mem := hγ.zero_mem
  nonneg := hγ.nonneg
  icc := hγ.icc
  exists_gt := hγ.exists_gt
  zero := (h hγ.zero_mem).symm.trans hγ.zero
  cont := hγ.cont.congr fun _ hu => (h hu).symm
  inj := hγ.inj.congr h
  mem_H _u hu hu0 := h hu ▸ hγ.mem_H _ hu hu0

theorem IsKilledArc.inter_Iio (hγ : IsKilledArc γ P) {t : ℝ} (ht : 0 < t) : IsKilledArc γ (P ∩ Iio t) where
  zero_mem := ⟨hγ.zero_mem, ht⟩
  nonneg u hu := hγ.nonneg u hu.1
  icc S hS := fun u hu => ⟨hγ.icc S hS.1 hu, lt_of_le_of_lt hu.2 hS.2⟩
  exists_gt S hS := by
    obtain ⟨S', hS'P, hSS'⟩ := hγ.exists_gt S hS.1
    refine ⟨(S + min S' t) / 2, ⟨hγ.icc S' hS'P ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have := hγ.nonneg S hS.1
      have : 0 ≤ min S' t := le_min (by linarith) ht.le
      linarith
    · have := min_le_left S' t; linarith
    · have h1 := min_le_right S' t
      have h2 : S < min S' t := lt_min hSS' hS.2
      show (S + min S' t) / 2 < t
      linarith
    · linarith [show S < min S' t from lt_min hSS' hS.2]
  zero := hγ.zero
  cont := hγ.cont.mono inter_subset_left
  inj := hγ.inj.mono inter_subset_left
  mem_H u hu hu0 := hγ.mem_H u hu.1 hu0

/-- Before a time `t' ∈ P` with `r < σ(t')`, some earlier positive time `S ∈ P` already has `r < σ(S)`. -/
theorem IsKilledArc.exists_lt_capClock_lt (hγ : IsKilledArc γ P) {t' : ℝ} (ht' : t' ∈ P) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < capClock γ t') : ∃ S ∈ P, 0 < S ∧ S < t' ∧ r < capClock γ S := by
  have ht'0 : 0 < t' := by
    rcases (hγ.nonneg t' ht').eq_or_lt with h | h
    · rw [← h, hγ.capClock_zero] at hr; linarith
    · exact h
  have hcw : ContinuousWithinAt (capClock γ) (Icc 0 t') t' :=
    (hγ.continuousOn_capClock t' ht').mono (hγ.icc t' ht')
  have hev : ∀ᶠ u in 𝓝[Ioo 0 t'] t', r < capClock γ u :=
    (hcw.mono Ioo_subset_Icc_self).eventually (lt_mem_nhds hr)
  have hne : (𝓝[Ioo 0 t'] t').NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo ht'0.ne]
    exact right_mem_Icc.2 ht'0.le
  obtain ⟨S, hS, hSI⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨S, hγ.icc t' ht' ⟨hSI.1.le, hSI.2.le⟩, hSI.1, hSI.2, hS⟩

/-- **The killed driver only depends on the arc up to a common prefix.** -/
theorem kW_eq_of_eqOn (hγ : IsKilledArc γ P) (hγ' : IsKilledArc γ' P') {S : ℝ} (hS : S ∈ P) (hS' : S ∈ P')
    (hS0 : 0 < S) (h : EqOn γ γ' (Icc 0 S)) {r : ℝ≥0} (hr : (r : ℝ) ≤ capClock γ S) :
    kW γ P r = kW γ' P' r := by
  have hc : capClock γ S = capClock γ' S := capClock_congr h
  have hlt : (r : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (by
      exact (NNReal.coe_nonneg r).trans hr) |>.2 hr)) (hγ.lt_kLife hS)
  have hlt' : (r : WithTop ℝ≥0) < kLife γ' P' :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (by
      exact (NNReal.coe_nonneg r).trans (hc ▸ hr)) |>.2 (hc ▸ hr))) (hγ'.lt_kLife hS')
  rw [kW_of_lt hlt, kW_of_lt hlt', hγ.chainDrv_eq hS hS0 ⟨r.coe_nonneg, hr⟩,
    hγ'.chainDrv_eq hS' hS0 ⟨r.coe_nonneg, hc ▸ hr⟩, locDrv_congr h]

/-- The killed paths agree on the common capacity range. -/
theorem kPath_eqOn_of_eqOn (hγ : IsKilledArc γ P) (hγ' : IsKilledArc γ' P') {S : ℝ} (hS : S ∈ P) (hS' : S ∈ P')
    (hS0 : 0 < S) (h : EqOn γ γ' (Icc 0 S)) : EqOn (kPath γ P) (kPath γ' P') (Icc 0 (capClock γ S)) :=
  fun r hr => by
    rw [kPath, kPath]
    exact kW_eq_of_eqOn hγ hγ' hS hS' hS0 h (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)

/-- **The images of the left marks only depend on the arc up to a common prefix.** -/
theorem kVL_eq_of_eqOn (hγ : IsKilledArc γ P) (hγ' : IsKilledArc γ' P') {S : ℝ} (hS : S ∈ P) (hS' : S ∈ P')
    (hS0 : 0 < S) (h : EqOn γ γ' (Icc 0 S)) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ capClock γ S) : kVL γ P xL i r = kVL γ' P' xL i r := by
  have hc : capClock γ S = capClock γ' S := capClock_congr h
  have hlt : (r : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (by
      exact (NNReal.coe_nonneg r).trans hr) |>.2 hr)) (hγ.lt_kLife hS)
  have hlt' : (r : WithTop ℝ≥0) < kLife γ' P' :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (by
      exact (NNReal.coe_nonneg r).trans (hc ▸ hr)) |>.2 (hc ▸ hr))) (hγ'.lt_kLife hS')
  obtain ⟨Wl, hWl, -, hEq, -⟩ := hγ.chainDrv_spec hS hS0
  have h1 : EqOn (fun u => -kPath γ P u) (fun u => -Wl u) (Icc 0 (capClock γ S)) := fun u hu => by
    simp only [neg_inj]
    rw [kPath, (hγ.kW_eq_chainDrv hS).2 u hu, hEq hu]
  have h2 : EqOn (fun u => -kPath γ' P' u) (fun u => -Wl u) (Icc 0 (capClock γ S)) := fun u hu => by
    simp only [neg_inj]
    rw [← kPath_eqOn_of_eqOn hγ hγ' hS hS' hS0 h hu, kPath, (hγ.kW_eq_chainDrv hS).2 u hu, hEq hu]
  rw [kVL_of_lt _ _ hlt, kVL_of_lt _ _ hlt', kVLr, kVLr, kImg_eq hWl.neg h1 hr, kImg_eq hWl.neg h2 hr]

/-- **The images of the right marks only depend on the arc up to a common prefix.** -/
theorem kVR_eq_of_eqOn (hγ : IsKilledArc γ P) (hγ' : IsKilledArc γ' P') {S : ℝ} (hS : S ∈ P) (hS' : S ∈ P')
    (hS0 : 0 < S) (h : EqOn γ γ' (Icc 0 S)) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ capClock γ S) : kVR γ P xR j r = kVR γ' P' xR j r := by
  have hc : capClock γ S = capClock γ' S := capClock_congr h
  have hlt : (r : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (by
      exact (NNReal.coe_nonneg r).trans hr) |>.2 hr)) (hγ.lt_kLife hS)
  have hlt' : (r : WithTop ℝ≥0) < kLife γ' P' :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (by
      exact (NNReal.coe_nonneg r).trans (hc ▸ hr)) |>.2 (hc ▸ hr))) (hγ'.lt_kLife hS')
  obtain ⟨Wl, hWl, -, hEq, -⟩ := hγ.chainDrv_spec hS hS0
  have h1 : EqOn (kPath γ P) Wl (Icc 0 (capClock γ S)) := fun u hu => by
    rw [kPath, (hγ.kW_eq_chainDrv hS).2 u hu, hEq hu]
  have h2 : EqOn (kPath γ' P') Wl (Icc 0 (capClock γ S)) := fun u hu => by
    rw [← kPath_eqOn_of_eqOn hγ hγ' hS hS' hS0 h hu, kPath, (hγ.kW_eq_chainDrv hS).2 u hu, hEq hu]
  rw [kVR_of_lt _ _ hlt, kVR_of_lt _ _ hlt', kVRr, kVRr, kImg_eq hWl h1 hr, kImg_eq hWl h2 hr]

end Congr

/-! ### The stopped data -/

namespace ChartConst

/-- The space of the two stopped histories. -/
abbrev YSp : Type := HistorySpace 1 1 × HistorySpace 1 1

/-- **The two stopped histories** of a glued sample: the forward history stopped at `t`, the reverse history stopped
at `s`. -/
def stopData {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t s : ℚ)
    (p : Ω × HistorySpace 1 1) : YSp :=
  (stopHistory (fun _ => (t : ℝ).toNNReal) (killedHistory W VL VR ζ p.1), revStop s p.2)

/-- The forward line read from stopped data. -/
def alphaY (y : YSp) (u : ℝ) : ℂ := LP.traceAt u.toNNReal (regPath y.1)

/-- The reflected reverse slit read from stopped data. -/
def GY (s : ℚ) (y : YSp) : Set ℂ := negInv '' (frzLine s y.2 '' Ioc 0 s)

/-- The image curve read from stopped data. -/
def gammaY (s : ℚ) (y : YSp) : ℝ → ℂ := imgCurve (revDrv0 s y.2) s (alphaY y)

/-- The pre-contact times read from stopped data. -/
def PcY (s : ℚ) (y : YSp) : Set ℝ := preContact (alphaY y) (GY s y)

/-- The pre-contact times before `t`, read from stopped data. -/
def PY (t s : ℚ) (y : YSp) : Set ℝ := PcY s y ∩ Iio t

/-- The left marks read from stopped data. -/
def gXLY (s : ℚ) (y : YSp) : Fin 2 → ℝ := ![0, -1 / frzVR s y.2]

/-- The right marks read from stopped data. -/
def gXRY (s : ℚ) (y : YSp) : Fin 2 → ℝ := ![0, -1 / frzVL s y.2]

end ChartConst

open ChartConst

section StopData

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : Set (Ω × HistorySpace 1 1)} {s t : ℚ}

theorem measurable_stopData [MeasurableSpace Ω] (t s : ℚ) :
    Measurable[twoSlitMarks W VL VR ζ t s] (stopData W VL VR ζ t s) := by
  refine Measurable.prodMk ?_ ?_
  · have h : Measurable[MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1)
        (stopSigma (t : ℝ).toNNReal)] fun p : Ω × HistorySpace 1 1 =>
          stopHistory (fun _ => (t : ℝ).toNNReal) (killedHistory W VL VR ζ p.1) :=
      fun B hB => ⟨stopHistory (fun _ => (t : ℝ).toNNReal) ⁻¹' B, ⟨B, hB, rfl⟩, rfl⟩
    exact h.mono le_sup_left le_rfl
  · have h : Measurable[MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => p.2) (stopSigma (s : ℝ).toNNReal)]
        fun p : Ω × HistorySpace 1 1 => revStop s p.2 :=
      fun B hB => ⟨stopHistory (fun _ => (s : ℝ).toNNReal) ⁻¹' B, ⟨B, hB, rfl⟩, rfl⟩
    exact h.mono le_sup_right le_rfl

variable {p : Ω × HistorySpace 1 1}

theorem alphaY_stopData (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {u : ℝ} (hu : u ≤ t) :
    alphaY (stopData W VL VR ζ t s p) u = seedLine ζ W p.1 u := by
  rw [alphaY, stopData, seedLine, Aux50Hit.regPath_stopHistory hg]
  refine LP.traceAt_congr fun r hr => ?_
  have hrt : r ≤ (t : ℝ).toNNReal := hr.trans (Real.toNNReal_le_toNNReal hu)
  simp only [min_eq_left hrt, killedProc_of_eq_top hg.1]

theorem GY_stopData (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E) :
    GY s (stopData W VL VR ζ t s p) = negInv '' histHull s p.2 := by
  rw [GY, stopData, frzLine_revStop, (glueG_eq hs (hEg p hp)).1]

theorem gammaY_stopData (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {u : ℝ} (hu : u ≤ t) :
    gammaY s (stopData W VL VR ζ t s p) u = gCurve s ζ W E p u := by
  rw [gammaY, gCurve_of_mem hp, imgCurve, imgCurve, stopData, revDrv0_revStop, revDrv0_of_mem hs (hEg p hp).2.1]
  split_ifs
  · rfl
  · rw [← alphaY_stopData (s := s) hg hu]
    rfl

theorem mem_PcY_stopData_iff (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {u : ℝ} (hu : u ≤ t) :
    u ∈ PcY s (stopData W VL VR ζ t s p) ↔ u ∈ gPre s ζ W E p := by
  rw [PcY, gPre_of_mem hp, GY_stopData hs hEg hp, preContact, preContact, mem_ofPred_eq, mem_ofPred_eq]
  refine and_congr_right fun _ => forall₂_congr fun v hv => ?_
  rw [alphaY_stopData hg (hv.2.trans hu)]

theorem PY_stopData (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) :
    PY t s (stopData W VL VR ζ t s p) = gPre s ζ W E p ∩ Iio (t : ℝ) := by
  ext u
  simp only [PY, mem_inter_iff, mem_Iio]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_PcY_stopData_iff hs hEg hp hg h2.le).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_PcY_stopData_iff hs hEg hp hg h2.le).2 h1, h2⟩

theorem isKilledArc_gammaY_stopData (hs : 0 < s) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) :
    IsKilledArc (gammaY s (stopData W VL VR ζ t s p)) (PY t s (stopData W VL VR ζ t s p)) := by
  rw [PY_stopData hs hEg hp hg]
  exact ((isKilledArc_gCurve hs hEg p).inter_Iio (by exact_mod_cast ht)).congr
    fun u hu => (gammaY_stopData hs hEg hp hg hu.2.le).symm

theorem gXLY_stopData (hp : p ∈ E) : gXLY s (stopData W VL VR ζ t s p) = gXL s E p := by
  simp only [gXLY, gXL, hp, ↓reduceIte, stopData, frzVR_revStop]

theorem gXRY_stopData (hp : p ∈ E) : gXRY s (stopData W VL VR ζ t s p) = gXR s E p := by
  simp only [gXRY, gXR, hp, ↓reduceIte, stopData, frzVL_revStop]

end StopData

end InteractingSLE.WangWu
