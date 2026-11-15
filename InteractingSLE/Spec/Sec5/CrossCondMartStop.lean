/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMartPass
import InteractingSLE.WangWu.ImgChartConstMarks

/-!
# The image word read from the two stopped histories (general `κ`)

Packet PROVE-GLUECOND7 (Astra's E.2 and E.6: "`R` and a mapped stopped prefix recover its original geometric prefix …
The capacity clock is adapted"). The general-`κ` form of PROVE-WW-B19's stopped data (`WangWu/ImgChartConstStop`):
the flow history stopped at a rational forward time `t` and the counterflow history stopped at `s` determine the
image curve, its pre-contact times before `t` and the image marks.

* `Y49`, `stopD`: the space of the two stopped histories and the stopped-data map, measurable for `cfGlueMarks`;
* `alphaD`, `GD`, `gammaD`, `PcD`, `PD`, `gXLD`, `gXRD`: the flow line, the obstacle `R(K′_s)` (the filled counterflow
  hull, `cfHullQ`), the image curve, its pre-contact times, and the image marks, read from stopped data;
* on good samples they agree with the glued-space objects of `Word49` before `t` (`alphaD_stopD`, `GD_stopD`,
  `gammaD_stopD`, `mem_PcD_stopD_iff`, `PD_stopD`, `isKilledArc_gammaD_stopD`, `gXLD_stopD`, `gXRD_stopD`).

The generic killed-arc congruences (`capClock_congr`, `IsKilledArc.congr`, `kW_eq_of_eqOn`, …) are PROVE-WW-B19's.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open ImgDrv MartChar
open Sec7.Lemma71C (capClock)

namespace Word49

/-! ### Idempotence of the counterflow stop -/

section Idem

theorem cfStop_cfStop (s : ℝ≥0) (y : HistorySpace 0 0) : cfStop s (cfStop s y) = cfStop s y :=
  CrossCond.stopHistory_const_stopHistory_const s y

theorem cfDrv0_cfStop (s : ℝ≥0) (y : HistorySpace 0 0) : cfDrv0 s (cfStop s y) = cfDrv0 s y := by
  funext u
  simp only [cfDrv0, cfStop_cfStop]

theorem cfHullQ_cfStop (s : ℝ≥0) (y : HistorySpace 0 0) : cfHullQ s (cfStop s y) = cfHullQ s y := by
  have h : hullAt s (cfStop s y) = hullAt s y := by
    simp only [hullAt]
    exact congrArg Sec4.regHull (cfStop_cfStop s y)
  simp only [cfHullQ, h]

end Idem

/-! ### Stopped data -/

/-- The space of the two stopped histories. -/
abbrev Y49 (nL nR : ℕ) : Type := HistorySpace nL nR × HistorySpace 0 0

/-- **The two stopped histories** of a glued sample: the flow history stopped at `t`, the counterflow history stopped
at `s`. -/
def stopD {Ω : Type*} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (t : ℚ) (s : ℝ≥0) (p : Ω × HistorySpace 0 0) : Y49 nL nR :=
  (Sec4.stopHistory (fun _ => (t : ℝ).toNNReal) (killedHistory W VL VR ζ p.1), cfStop s p.2)

section Defs

variable {nL nR : ℕ}

/-- The flow line read from stopped data. -/
def alphaD (y : Y49 nL nR) (u : ℝ) : ℂ := LP.traceAt u.toNNReal (Sec4.regPath y.1)

/-- The obstacle `R(K′_s)` read from stopped data. -/
def GD (s : ℝ≥0) (y : Y49 nL nR) : Set ℂ := cfHullQ s y.2

/-- The image curve read from stopped data. -/
def gammaD (s : ℝ≥0) (y : Y49 nL nR) : ℝ → ℂ := imgCurve (cfDrv0 s y.2) s (alphaD y)

/-- The pre-contact times read from stopped data. -/
def PcD (s : ℝ≥0) (y : Y49 nL nR) : Set ℝ := preContact (alphaD y) (GD s y)

/-- The pre-contact times before `t`, read from stopped data. -/
def PD (t : ℚ) (s : ℝ≥0) (y : Y49 nL nR) : Set ℝ := PcD s y ∩ Iio (t : ℝ)

/-- The left image marks read from stopped data. -/
def gXLD (xL : Fin nL → ℝ) (s : ℝ≥0) (y : Y49 nL nR) : Fin (nL + 1) → ℝ :=
  Fin.snoc (fun i => psiL (cfDrv0 s y.2) s (xL i)) (junL (cfDrv0 s y.2) s)

/-- The right image marks read from stopped data. -/
def gXRD (xR : Fin nR → ℝ) (s : ℝ≥0) (y : Y49 nL nR) : Fin (nR + 1) → ℝ :=
  Fin.snoc (fun j => psiR (cfDrv0 s y.2) s (xR j)) (junR (cfDrv0 s y.2) s)

end Defs

section StopData

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t : ℚ}

theorem measurable_stopD [MeasurableSpace Ω] (t : ℚ) (s : ℝ≥0) :
    Measurable[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] (stopD W VL VR ζ t s) := by
  refine Measurable.prodMk ?_ ?_
  · have h : Measurable[MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1)
        (stopSigma (t : ℝ).toNNReal)] fun p : Ω × HistorySpace 0 0 =>
          Sec4.stopHistory (fun _ => (t : ℝ).toNNReal) (killedHistory W VL VR ζ p.1) :=
      fun B hB => ⟨Sec4.stopHistory (fun _ => (t : ℝ).toNNReal) ⁻¹' B, ⟨B, hB, rfl⟩, rfl⟩
    exact h.mono le_sup_left le_rfl
  · have h : Measurable[MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => p.2) (stopSigma s)]
        fun p : Ω × HistorySpace 0 0 => cfStop s p.2 :=
      fun B hB => ⟨Sec4.stopHistory (fun _ => s) ⁻¹' B, ⟨B, hB, rfl⟩, rfl⟩
    exact h.mono le_sup_right le_rfl

variable {p : Ω × HistorySpace 0 0}

theorem alphaD_stopD (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {u : ℝ} (hu : u ≤ t) :
    alphaD (stopD W VL VR ζ t s p) u = seedLine ζ W p.1 u := by
  rw [alphaD, stopD, seedLine, Aux50Hit.regPath_stopHistory hg]
  refine LP.traceAt_congr fun r hr => ?_
  have hrt : r ≤ (t : ℝ).toNNReal := hr.trans (Real.toNNReal_le_toNNReal hu)
  simp only [min_eq_left hrt, killedProc_of_eq_top hg.1]

theorem GD_stopD : GD s (stopD W VL VR ζ t s p) = cfHullQ s p.2 := by
  rw [GD, stopD, cfHullQ_cfStop]

theorem gammaD_stopD (hp : p ∈ E) (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {u : ℝ} (hu : u ≤ t) :
    gammaD s (stopD W VL VR ζ t s p) u = gCurve s ζ W E p u := by
  rw [gammaD, gCurve_of_mem hp, imgCurve, imgCurve, stopD, cfDrv0_cfStop]
  split_ifs
  · rfl
  · rw [← alphaD_stopD (s := s) hg hu]
    rfl

theorem mem_PcD_stopD_iff (hp : p ∈ E) (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {u : ℝ} (hu : u ≤ t) :
    u ∈ PcD s (stopD W VL VR ζ t s p) ↔ u ∈ gPre s ζ W E p := by
  rw [PcD, gPre_of_mem hp, GD_stopD, preContact, preContact, mem_ofPred_eq, mem_ofPred_eq]
  refine and_congr_right fun _ => forall₂_congr fun v hv => ?_
  rw [alphaD_stopD hg (hv.2.trans hu)]

theorem PD_stopD (hp : p ∈ E) (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) :
    PD t s (stopD W VL VR ζ t s p) = gPre s ζ W E p ∩ Iio (t : ℝ) := by
  ext u
  simp only [PD, mem_inter_iff, mem_Iio]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_PcD_stopD_iff hp hg h2.le).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_PcD_stopD_iff hp hg h2.le).2 h1, h2⟩

theorem isKilledArc_gammaD_stopD (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) :
    IsKilledArc (gammaD s (stopD W VL VR ζ t s p)) (PD t s (stopD W VL VR ζ t s p)) := by
  rw [PD_stopD hp hg]
  exact ((isKilledArc_gCurve hEg p).inter_Iio (by exact_mod_cast ht)).congr
    fun u hu => (gammaD_stopD hp hg hu.2.le).symm

theorem gXLD_stopD (xL : Fin nL → ℝ) (hp : p ∈ E) : gXLD xL s (stopD W VL VR ζ t s p) = gXL xL s E p := by
  simp only [gXLD, gXL, hp, ↓reduceIte, stopD, cfDrv0_cfStop]

theorem gXRD_stopD (xR : Fin nR → ℝ) (hp : p ∈ E) : gXRD xR s (stopD W VL VR ζ t s p) = gXR xR s E p := by
  simp only [gXRD, gXR, hp, ↓reduceIte, stopD, cfDrv0_cfStop]

end StopData

end Word49

end InteractingSLE.Sec5.CrossCond
