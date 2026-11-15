/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelLifeCut
import InteractingSLE.Spec.Sec5.CrossRestartKernelDrv
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Sec7.LocalExtEHist
import InteractingSLE.Spec.Exist.StagedLawStmt
import InteractingSLE.Spec.Supplement.CounterflowRange

/-!
# Theorem 1.4's walk pieces: the record of a piece read from its path, and the path from its record

Packet PROVE-T14-WALK (the launch-locality leaf `WalkLaw.WalkStageLaunchLocalStatement`). A launched ordinary piece of a
boundary walk has an infinite instruction time, so its retained record is `recOf ⊤ (W, ζ)`: the driver at the rational
times stopped at the lifetime `ζ`, the lifetime, and the flag `true`. Lemma 6.2's locality speaks about the **path** of
the piece (its trace frozen at `ζ`); the marks of the walk law are its **record**. This file proves, deterministically,
that the two determine each other through Borel maps:

* **path → record** (`readRec`, **`readRec_pathCoord`**): for the driver `W` of an integrated `SLE_κ(ρ)` path with a
  continuous generating trace `η` on `[0, ζ]`, the lifetime is read from the dyadic values of `η`
  (`Sec5.CrossRestart.lifeOf`, PROVE-CFRESTART), the killed driving code from the dyadic trace code
  (`Exist.Staged.dInv`, Lusin–Souslin on the good driver codes), and the record from the driver path of that code;
  only the **rational coordinates** of `η` are used (`ratExt`);
* **record → path** (`recDrv`, `recPath`, **`recPath_recOf_top`**): the driver is read from the record at the dyadic
  rationals decreasing to each time (right-continuity of the stopped driver), and the path is LP11's Borel
  reconstruction `LP.drivingTrace` of the recorded driving history: `t ↦ η(min t ζ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkLeaf

open Sec2.Assembly Exist.Staged Exist.StagedLaw Sec5.CrossRestart

/-! ### Paths from their rational coordinates -/

section Rat

/-- A path on `ℝ≥0` from its rational coordinates: the coordinate at a rational time, `0` at the other times. -/
def ratExt (c : ℚ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  haveI := Classical.propDecidable
  if h : ∃ q : ℚ≥0, (q : ℝ≥0) = t then c h.choose else 0

theorem measurable_ratExt : Measurable ratExt := by
  refine measurable_pi_iff.2 fun t => ?_
  by_cases h : ∃ q : ℚ≥0, (q : ℝ≥0) = t
  · have e : (fun c : ℚ≥0 → ℂ => ratExt c t) = fun c => c h.choose := funext fun c => dite_eq_left h
    rw [e]
    exact measurable_pi_apply _
  · have e : (fun c : ℚ≥0 → ℂ => ratExt c t) = fun _ => 0 := funext fun c => dite_eq_right h
    rw [e]
    exact measurable_const

theorem ratExt_coe (c : ℚ≥0 → ℂ) (q : ℚ≥0) : ratExt c (q : ℝ≥0) = c q := by
  have h : ∃ q' : ℚ≥0, (q' : ℝ≥0) = (q : ℝ≥0) := ⟨q, rfl⟩
  rw [ratExt, dite_eq_left h, NNRat.cast_injective h.choose_spec]

/-- The dyadic time `k / 2ⁿ` as a nonnegative rational. -/
def dyadR (n k : ℕ) : ℚ≥0 := (k : ℚ≥0) / 2 ^ n

theorem coe_dyadR (n k : ℕ) : ((dyadR n k : ℚ≥0) : ℝ≥0) = dyad n k := by
  simp [dyadR, dyad]

theorem ratExt_dyad (c : ℚ≥0 → ℂ) (n k : ℕ) : ratExt c (dyad n k) = c (dyadR n k) := by
  rw [← coe_dyadR, ratExt_coe]

theorem trCodeOf_ratExt (η : ℝ≥0 → ℂ) (r : ℝ≥0) : trCodeOf (ratExt (Sec6.pathCoord η)) r = trCodeOf η r := by
  refine Prod.ext rfl (funext fun n => funext fun k => ?_)
  change (if (dyad n k : ℝ≥0∞) < r then ratExt (Sec6.pathCoord η) (dyad n k) else 0) =
    (if (dyad n k : ℝ≥0∞) < r then η (dyad n k) else 0)
  rw [ratExt_dyad]
  simp only [Sec6.pathCoord, coe_dyadR]

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The lifetime test only reads dyadic coordinates. -/
theorem lifeOf_ratExt (η : ℝ≥0 → ℂ) :
    lifeOf a xL xR ρL ρR (ratExt (Sec6.pathCoord η)) = lifeOf a xL xR ρL ρR η := by
  unfold lifeOf
  refine iSup_congr fun n => iSup_congr fun k => ?_
  have hiff : ratExt (Sec6.pathCoord η) ∈ LiveSet a xL xR ρL ρR n k ↔ η ∈ LiveSet a xL xR ρL ρR n k := by
    change (0 < dyad n k ∧ LivesPast a xL xR ρL ρR _ (dyad n k)) ↔
      (0 < dyad n k ∧ LivesPast a xL xR ρL ρR η (dyad n k))
    unfold LivesPast
    rw [trCodeOf_ratExt]
  by_cases h : η ∈ LiveSet a xL xR ρL ρR n k
  · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.1 h)]

end Rat

/-! ### The record of a piece read from the rational coordinates of its path -/

section Read

variable {nL nR : ℕ} (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

/-- The lifetime read from the rational coordinates of a path. -/
def readLife (c : ℚ≥0 → ℂ) : ℝ≥0∞ := lifeOf a xL xR ρL ρR (ratExt c)

/-- The trace code read from the rational coordinates of a path: the lifetime and the dyadic values before it. -/
def readTr (c : ℚ≥0 → ℂ) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  (readLife a xL xR ρL ρR c, fun n k => if (dyad n k : ℝ≥0∞) < readLife a xL xR ρL ρR c then c (dyadR n k) else 0)

/-- The killed driving code read from the rational coordinates of a path. -/
def readCode (c : ℚ≥0 → ℂ) : DCode := dInv (readTr a xL xR ρL ρR c)

/-- **The record read from the rational coordinates of a path** (infinite instruction time: the flag is `true`). -/
def readRec (c : ℚ≥0 → ℂ) : RecData :=
  ((fun q : ℚ => drvPath (readCode a xL xR ρL ρR c) (q : ℝ).toNNReal), readLife a xL xR ρL ρR c, true)

variable {a}

theorem measurable_readLife (ha : 0 < a) : Measurable (readLife a xL xR ρL ρR) :=
  (measurable_lifeOf ha xL xR ρL ρR).comp measurable_ratExt

theorem measurable_readTr (ha : 0 < a) : Measurable (readTr a xL xR ρL ρR) := by
  have hL := measurable_readLife xL xR ρL ρR ha
  refine hL.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const hL) (measurable_pi_apply _) measurable_const

theorem measurable_readCode (ha : 0 < a) : Measurable (readCode a xL xR ρL ρR) :=
  measurable_dInv.comp (measurable_readTr xL xR ρL ρR ha)

theorem measurable_readRec (ha : 0 < a) : Measurable (readRec a xL xR ρL ρR) := by
  have hC := measurable_readCode xL xR ρL ρR ha
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_)
    ((measurable_readLife xL xR ρL ρR ha).prodMk measurable_const)
  exact (measurable_pi_apply _).comp (measurable_drvPath.comp hC)

end Read

section Correct

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The driver path of the killed code is the driver stopped at its lifetime**, for a driver continuous on `[0, ζ]`
with `w 0 = 0`. -/
theorem drvPath_killCode (hwc : ContinuousOn w {t | (t : ℝ≥0∞) ≤ ζ}) (hw0 : w 0 = 0) (s : ℝ≥0) :
    drvPath (killCode w ζ) s = w (min (s : ℝ≥0∞) ζ).toNNReal := by
  have hwlt : ContinuousOn w {t | (t : ℝ≥0∞) < ζ} :=
    hwc.mono fun t (ht : (t : ℝ≥0∞) < ζ) => (le_of_lt ht : (t : ℝ≥0∞) ≤ ζ)
  by_cases hs : (s : ℝ≥0∞) < ζ
  · rw [drvPath_of_lt (show (s : ℝ≥0∞) < (killCode w ζ).1 from hs), dec_killCode hwlt hs,
      min_eq_left hs.le, ENNReal.toNNReal_coe]
  have hζs : ζ ≤ s := not_lt.1 hs
  have hζ : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζs
  rw [min_eq_right hζs]
  -- `drvPath` takes the same value at every time from the lifetime on
  have hnot : ¬ ((ζ.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by rw [ENNReal.coe_toNNReal hζ]; exact lt_irrefl _
  have e : drvPath (killCode w ζ) s = drvPath (killCode w ζ) ζ.toNNReal := by
    simp only [drvPath, show ¬ (s : ℝ≥0∞) < (killCode w ζ).1 from hs,
      show ¬ ((ζ.toNNReal : ℝ≥0) : ℝ≥0∞) < (killCode w ζ).1 from hnot, ↓reduceIte]
  rw [e]
  rcases eq_or_ne ζ 0 with h0 | h0
  · -- zero lifetime: the code vanishes
    subst h0
    have hz : ∀ n, (killCode w 0).2 n 0 = 0 := fun n => by
      simp only [killCode, not_lt_zero, ↓reduceIte]
    simp only [drvPath, show (killCode w 0).1 = 0 from rfl, ENNReal.toNNReal_zero, zero_tsub,
      dec_zero_of_const hz, limsup_const, hw0, ite_self]
  · -- positive lifetime: the left limit
    have hpos : 0 < ζ := pos_iff_ne_zero.2 h0
    refine drvPath_eq_of_tendsto (z := killCode w ζ) hζ hpos ?_
    have hx : ((ζ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := ENNReal.coe_toNNReal_le_self
    have hsub : Iio ζ.toNNReal ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := fun t ht =>
      (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hx
    have hlim : Tendsto w (𝓝[<] ζ.toNNReal) (𝓝 (w ζ.toNNReal)) :=
      ((hwc _ hx).tendsto).mono_left (nhdsWithin_mono _ hsub)
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun t (ht : t ∈ Iio ζ.toNNReal) => ?_)
    have htζ : (t : ℝ≥0∞) < ζ := by
      rw [← ENNReal.coe_toNNReal hζ]; exact ENNReal.coe_lt_coe.2 ht
    rw [drvPath_of_lt (show (t : ℝ≥0∞) < (killCode w ζ).1 from htζ), dec_killCode hwlt htζ]

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}

/-- **The record of a piece is read from the rational coordinates of its path.** For an integrated `SLE_a(ρ)` path
`(w, vL, vR, b, ζ)` (`a > 0`) whose driver is continuous on `[0, ζ]`, and a generating trace `η` of `w` on `[0, ζ]`
(arbitrary after `ζ`), `readRec` of the rational coordinates of `η` is the record `recOf ⊤ (w, ζ)`. -/
theorem readRec_pathCoord (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hη : IsGeneratingTrace w ζ η) (hwc : ContinuousOn w {t | (t : ℝ≥0∞) ≤ ζ}) :
    readRec a xL xR ρL ρR (Sec6.pathCoord η) = recOf ⊤ (w, ζ) := by
  have hw0 : w 0 = 0 := hp.1
  have hwlt : ContinuousOn w {t | (t : ℝ≥0∞) < ζ} :=
    hwc.mono fun t (ht : (t : ℝ≥0∞) < ζ) => (le_of_lt ht : (t : ℝ≥0∞) ≤ ζ)
  have hL : readLife a xL xR ρL ρR (Sec6.pathCoord η) = ζ := by
    rw [readLife, lifeOf_ratExt, lifeOf_eq ha hp hη]
  have hT : readTr a xL xR ρL ρR (Sec6.pathCoord η) = dTrace (killCode w ζ) := by
    rw [dTrace_killCode hwlt hw0 hη]
    refine Prod.ext hL (funext fun n => funext fun k => ?_)
    change (if (dyad n k : ℝ≥0∞) < readLife a xL xR ρL ρR (Sec6.pathCoord η) then
      Sec6.pathCoord η (dyadR n k) else 0) = (if (dyad n k : ℝ≥0∞) < ζ then η (dyad n k) else 0)
    rw [hL]
    simp only [Sec6.pathCoord, coe_dyadR]
  have hC : readCode a xL xR ρL ρR (Sec6.pathCoord η) = killCode w ζ := by
    rw [readCode, hT, dInv_dTrace (killCode_mem_DSet hwlt hw0 hη)]
  change ((fun q : ℚ => drvPath (readCode a xL xR ρL ρR (Sec6.pathCoord η)) (q : ℝ).toNNReal),
      readLife a xL xR ρL ρR (Sec6.pathCoord η), true) =
    ((fun q : ℚ => w (min ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) (min ⊤ ζ)).toNNReal), min ⊤ ζ, decide (ζ ≤ ⊤))
  rw [hC, hL, min_top_left]
  simp only [le_top, decide_true, Prod.mk.injEq, and_true]
  exact funext fun q => drvPath_killCode hwc hw0 _

end Correct

/-! ### The path of a piece read from its record -/

section Path

/-- The driver read from a record at the dyadic rationals decreasing to each time. -/
def recDrv (r : RecData) (s : ℝ≥0) : ℝ := limsup (fun n => r.1 ((LocalExt.upDyad n s : ℚ≥0) : ℚ)) atTop

theorem measurable_recDrv : Measurable recDrv :=
  measurable_pi_iff.2 fun _ => Measurable.limsup fun _ => (measurable_pi_apply _).comp measurable_fst

/-- **The path read from a record**: LP11's Borel reconstruction of the recorded driving history. -/
def recPath (r : RecData) (t : ℝ≥0) : ℂ := (LP.drivingTrace (r.2.1, recDrv r)).2 t

theorem measurable_recPath (t : ℝ≥0) : Measurable fun r : RecData => recPath r t :=
  (measurable_pi_apply t).comp (measurable_snd.comp
    (LP.measurable_drivingTrace.comp ((measurable_fst.comp measurable_snd).prodMk measurable_recDrv)))

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The driver read from the record of a driver continuous on `[0, ζ]` is the driver stopped at `ζ`. -/
theorem recDrv_recOf_top (hwc : ContinuousOn w {t | (t : ℝ≥0∞) ≤ ζ}) (s : ℝ≥0) :
    recDrv (recOf ⊤ (w, ζ)) s = w (min (s : ℝ≥0∞) ζ).toNNReal := by
  have hg := CounterflowRange.continuous_stopped hwc
  have hsamp : ∀ n, (recOf ⊤ (w, ζ)).1 ((LocalExt.upDyad n s : ℚ≥0) : ℚ) =
      w (min (((LocalExt.upDyad n s : ℚ≥0) : ℝ≥0) : ℝ≥0∞) ζ).toNNReal := fun n => by
    change w (min ((((((LocalExt.upDyad n s : ℚ≥0) : ℚ) : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) (min ⊤ ζ)).toNNReal = _
    rw [toNNReal_ratCast_nnrat, min_top_left]
  have hlim := (hg.tendsto s).comp (LocalExt.tendsto_upDyad s)
  rw [recDrv, funext hsamp]
  exact hlim.limsup_eq

/-- A generating trace on `[0, ζ]` frozen at `ζ` is still a generating trace on `[0, ζ]`. -/
theorem isGeneratingTrace_frozen {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) :
    IsGeneratingTrace w ζ fun t => η (min (t : ℝ≥0∞) ζ).toNNReal := by
  have he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η (min (t : ℝ≥0∞) ζ).toNNReal = η t := fun t ht => by
    rw [min_eq_left ht, ENNReal.toNNReal_coe]
  refine ⟨?_, hη.2.1.congr fun t ht => he t ht, fun t ht => ?_⟩
  · change η (min ((0 : ℝ≥0) : ℝ≥0∞) ζ).toNNReal = 0
    rw [he 0 bot_le]
    exact hη.1
  have hi : (fun t : ℝ≥0 => η (min (t : ℝ≥0∞) ζ).toNNReal) '' Icc 0 t = η '' Icc 0 t :=
    image_congr fun s (hs : s ∈ Icc 0 t) => he s ((ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  rw [hi]
  exact hη.2.2 t ht

/-- **The path read from the record of a regular piece is its trace frozen at the lifetime.** -/
theorem recPath_recOf_top (hwc : ContinuousOn w {t | (t : ℝ≥0∞) ≤ ζ}) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ζ η) (t : ℝ≥0) :
    recPath (recOf ⊤ (w, ζ)) t = η (min (t : ℝ≥0∞) ζ).toNNReal := by
  have h2 : (recOf ⊤ (w, ζ)).2.1 = ζ := by
    change min (⊤ : ℝ≥0∞) ζ = ζ
    exact min_top_left ζ
  have hwlt : ContinuousOn w {t | (t : ℝ≥0∞) < ζ} :=
    hwc.mono fun t (ht : (t : ℝ≥0∞) < ζ) => (le_of_lt ht : (t : ℝ≥0∞) ≤ ζ)
  have hagree : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → recDrv (recOf ⊤ (w, ζ)) s = w s := fun s hs => by
    rw [recDrv_recOf_top hwc, min_eq_left hs.le, ENNReal.toNNReal_coe]
  unfold recPath
  rw [h2, LP.drivingTrace_eq hη hwlt hw0 hagree]

end Path

end InteractingSLE.Theorem14.WalkLeaf
