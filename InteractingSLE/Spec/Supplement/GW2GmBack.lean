/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmSlit
import InteractingSLE.Spec.Supplement.GW2RootJ31Joined
import InteractingSLE.Spec.Supplement.GW2RootG28Trace

/-!
# J31's joined record is the record of one trace-generating driver

Packet PROVE-GW2-GEOM2 (step R3 of PROVE-GW2-SWITCH's plan). J31 reads the switched prefix from one
record, `RootJ31.joinedRecord L R = recOfDriver (lastTime 0 L) (joinedRead L R)`, where `joinedRead`
concatenates the decoded drivers `rdrv (R j)` back-nested (Prop 5.13's `joinedDriver`). This file shows:

* **`exists_isGeneratingTrace_joinedDriver`**: a back-nested joined driver generates a trace on `[0, ∞)`
  when every piece's driver does (boundary hits allowed; the empty tail is the zero driver);
* `rdrv_recOf_eq`, **`exists_isGeneratingTrace_rdrv_recOf`**: the decoded driver of a piece stopped at
  `min t ζ` with a driver continuous on the closed stop interval is the frozen piece driver, and it
  generates a trace on `[0, ∞)` (from the trace on the stop horizon, `GW2GmSlit`);
* **`exists_isGeneratingTrace_joinedRead`**: hence `joinedRead L R` generates a trace on `[0, ∞)`;
* `recOfDriver_eq_recOf`, `rdrv_recOfDriver`, **`frozenTraceRead_recOfDriver`**: the joined record is
  `recOf (lastTime 0 L) (joinedRead L R, ⊤)`; its decoded driver and its frozen trace reader are the joined
  driver and its trace, frozen at the last time.

All statements are deterministic; no lifetime or boundary-avoidance hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart Sec5.Prop513TreeExtract Sec5.Prop513Schedule
  Sec7.StripSideHeightProb

/-- **The back-nested joined driver generates a trace on `[0, ∞)`**, boundary hits allowed, when every
piece's driver is continuous from `0` and generates a trace on `[0, ∞)`. -/
theorem exists_isGeneratingTrace_joinedDriver {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (ω : Ω) (hc : ∀ i, Continuous (E i ω).1 ∧ (E i ω).1 0 = 0)
    (htr : ∀ i, ∃ η, IsGeneratingTrace (E i ω).1 ⊤ η) :
    ∀ (L : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0),
      ∃ γ, IsGeneratingTrace (joinedDriver E j a L ω) ⊤ γ
  | [], j, a => by
    have h0 : joinedDriver E j a [] ω = fun _ => (0 : ℝ) := funext fun _ => rfl
    exact ⟨slitTrace, h0 ▸ isGeneratingTrace_zero_slit⟩
  | p :: L, j, a => by
    obtain ⟨γ₁, hγ₁⟩ := exists_isGeneratingTrace_joinedDriver E ω hc htr L (j + 1) p.2
    obtain ⟨η₀, hη₀⟩ := htr j
    obtain ⟨hc1, hz1⟩ := joinedDriver_continuous E ω (j + 1) p.2 L fun i _ _ => hc i
    exact ⟨LoewnerConcat.joinedTrace (E j ω).1 η₀ (p.2 - a) γ₁,
      LoewnerConcat.isGeneratingTrace_catPath_bdry (hc j).1 (hc j).2 hc1 hz1
        (hη₀.mono_horizon le_top) hγ₁⟩

/-- The decoded driver of a piece stopped at a finite `min t ζ`, continuous on the closed stop interval,
is the piece driver frozen at the stop. -/
theorem rdrv_recOf_eq {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hfin : min t e.2 ≠ ⊤) (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2}) (x : ℝ≥0) :
    rdrv (recOf t e) x = e.1 (min x (min t e.2).toNNReal) := by
  have hg := isDrvGood_of_continuousOn_le he hfin hc
  change LocalExt.histDrv (recHist (recOf t e)) (x : ℝ).toNNReal = _
  rw [Real.toNNReal_coe, histDrv_recHist he hg x]
  change e.1 (min (x : ℝ≥0∞) (min t e.2)).toNNReal = _
  rw [← ENNReal.coe_toNNReal hfin, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]

/-- **A decoded stopped piece generates a trace on `[0, ∞)`**, agreeing with the piece's trace up to the
stop, when the piece driver is continuous on the closed stop interval and generates a trace there. -/
theorem exists_isGeneratingTrace_rdrv_recOf {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (hfin : min t e.2 ≠ ⊤)
    (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2}) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace e.1 (min t e.2) η) :
    ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun x : ℝ≥0 => rdrv (recOf t e) x) ⊤ η' ∧
      ∀ u ≤ (min t e.2).toNNReal, η' u = η u := by
  set σ : ℝ≥0 := (min t e.2).toNNReal with hσ
  have hσe : ((σ : ℝ≥0) : ℝ≥0∞) = min t e.2 := ENNReal.coe_toNNReal hfin
  have hcI : ContinuousOn e.1 (Icc 0 σ) :=
    hc.mono fun s hs => by
      change (s : ℝ≥0∞) ≤ min t e.2
      rw [← hσe]
      exact ENNReal.coe_le_coe.2 hs.2
  obtain ⟨η', hη', hag⟩ := exists_isGeneratingTrace_frozen hcI he.2.1 (hσe ▸ hη)
  refine ⟨η', ?_, hag⟩
  have hfun : (fun x : ℝ≥0 => rdrv (recOf t e) x) = fun u => e.1 (min u σ) :=
    funext fun x => rdrv_recOf_eq he hfin hc x
  rw [hfun]
  exact hη'

/-- **J31's joined driver generates a trace on `[0, ∞)`** when every decoded record driver does. -/
theorem exists_isGeneratingTrace_joinedRead (L : List (ℝ × ℝ≥0)) (R : Fin L.length → RecData)
    (h : ∀ (i : ℕ) (hi : i < L.length),
      ∃ η, IsGeneratingTrace (fun x : ℝ≥0 => rdrv (R ⟨i, hi⟩) x) ⊤ η) :
    ∃ γ, IsGeneratingTrace (RootJ31.joinedRead L R) ⊤ γ := by
  refine exists_isGeneratingTrace_joinedDriver
    (fun j (R : Fin L.length → RecData) => (RootJ31.recordDriver R j, ⊤)) R
    (fun i => ⟨RootJ31.continuous_recordDriver R i, RootJ31.recordDriver_zero R i⟩)
    (fun i => ?_) L 0 0
  by_cases hi : i < L.length
  · obtain ⟨η, hη⟩ := h i hi
    refine ⟨η, ?_⟩
    have hrd : RootJ31.recordDriver R i = fun x : ℝ≥0 => rdrv (R ⟨i, hi⟩) x := by
      simp only [RootJ31.recordDriver, hi, ↓reduceDIte]
    change IsGeneratingTrace (RootJ31.recordDriver R i) ⊤ η
    rw [hrd]
    exact hη
  · refine ⟨slitTrace, ?_⟩
    have hrd : RootJ31.recordDriver R i = fun _ => (0 : ℝ) := by
      simp only [RootJ31.recordDriver, hi, ↓reduceDIte]
    change IsGeneratingTrace (RootJ31.recordDriver R i) ⊤ slitTrace
    rw [hrd]
    exact isGeneratingTrace_zero_slit

/-- A continuous driver from `0` with infinite lifetime is regular. -/
theorem isRegularDriver_top {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) :
    IsRegularDriver (W, ⊤) :=
  ⟨hW.continuousOn, hW0, fun _ ht => absurd ht (not_le.2 ENNReal.coe_lt_top),
    fun h => absurd rfl h⟩

/-- The record read off a driver at a cap is the record of that driver with infinite lifetime. -/
theorem recOfDriver_eq_recOf (q₀ : ℝ≥0) (W : ℝ≥0 → ℝ) :
    StagedEntrance.Strip.recOfDriver q₀ W = recOf (q₀ : ℝ≥0∞) (W, ⊤) := by
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ ?_)
  · change W (min ((q : ℝ)).toNNReal q₀) =
      W (min (((q : ℝ)).toNNReal : ℝ≥0∞) (min (q₀ : ℝ≥0∞) ⊤)).toNNReal
    rw [min_top_right, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  · change (q₀ : ℝ≥0∞) = min (q₀ : ℝ≥0∞) ⊤
    rw [min_top_right]
  · change false = decide ((⊤ : ℝ≥0∞) ≤ q₀)
    simp only [top_le_iff, ENNReal.coe_ne_top, decide_false]

/-- The decoded driver of a driver's record at a cap is the driver frozen at the cap. -/
theorem rdrv_recOfDriver {q₀ : ℝ≥0} {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (x : ℝ≥0) : rdrv (StagedEntrance.Strip.recOfDriver q₀ W) x = W (min x q₀) := by
  have he := isRegularDriver_top hW hW0
  have hfin : min (q₀ : ℝ≥0∞) (W, ⊤).2 ≠ ⊤ := by
    change min (q₀ : ℝ≥0∞) ⊤ ≠ ⊤
    rw [min_top_right]
    exact ENNReal.coe_ne_top
  rw [recOfDriver_eq_recOf, rdrv_recOf_eq he hfin (hW.continuousOn) x]
  change W (min x (min (q₀ : ℝ≥0∞) ⊤).toNNReal) = _
  rw [min_top_right, ENNReal.toNNReal_coe]

/-- **The frozen trace reader of a driver's record at a cap is the driver's trace frozen at the cap.** -/
theorem frozenTraceRead_recOfDriver {q₀ : ℝ≥0} {W : ℝ≥0 → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) :
    RootG28.frozenTraceRead q₀ (StagedEntrance.Strip.recOfDriver q₀ W) = fun t => γ (min t q₀) := by
  rw [recOfDriver_eq_recOf]
  exact RootG28.frozenTraceRead_recOf_eq (isRegularDriver_top hW hW0) hγ ENNReal.coe_lt_top

end InteractingSLE.Theorem14.GW2TipSystem.Gm
