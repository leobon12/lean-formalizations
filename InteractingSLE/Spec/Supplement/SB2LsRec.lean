/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LrRun

/-!
# Records and hits of a launch read from filled traces

Packet PROVE-T14-SB2LIFT (round 9; item 1 of handoff §R8.2). The frozen launch decides its new right record
`lRecR s ⊤ D` and its right hits (`lHit`) through the forward Loewner flow of the stopped driver. Here they are read
from filled traces:

* **`lRecR_eq_of_alive_iff`** (bookkeeping): if beyond the record aliveness at the stop is "off a set `F`", the new
  record is `sSup (insert recR {x > recR | x ∈ F})`. With `lAlive_run_iff`, `F` is the closure of the new filled
  prefix;
* **`aliveAt_iff_notMem_closure_fillH`**: at a time `r ∈ [0, T)` before the stop of a regular piece with a finite
  lifetime `T`, a real nonzero chart point is alive for the stopped driver iff it is off the closure of the filled
  trace up to `r` (Lemma 76E's criteria in closure form, `Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace`);
* **`lHit_iff_closure`**: a real nonzero chart point is hit at the stop iff it is off the closures of the filled
  traces up to every earlier time and on the closure of the filled closed trace.

All chart-coordinate statements here combine with `mem_closure_fillH_iff_of_chart` (and lemma (T) for the truncated
traces) into physical statements, as `lAlive_run_iff` does at the stop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

/-- **The new record from an aliveness characterization beyond the record.** -/
theorem lRecR_eq_of_alive_iff {s : ExplState} {t : ℝ≥0∞} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} {F : Set ℂ}
    (h : ∀ x : ℝ, stRecR s < x → (lAlive (stChart s) t d x ↔ (x : ℂ) ∉ F)) :
    lRecR s t d = sSup (insert (stRecR s) {x : ℝ | stRecR s < x ∧ (x : ℂ) ∈ F}) := by
  unfold lRecR
  congr 2
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hna⟩
    exact ⟨hx, by_contra fun hF => hna ((h x hx).2 hF)⟩
  · rintro ⟨hx, hF⟩
    exact ⟨hx, fun ha => (h x hx).1 ha hF⟩

/-- The stopped driver of a regular piece with a finite lifetime, read on `ℝ≥0`, generates the chosen trace up to the
lifetime; the stopped driver on `ℝ` is this driver composed with `toNNReal`. -/
theorem stopDrv_eq_and_isGeneratingTrace {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) :
    stopDrv ⊤ D = (fun s : ℝ => (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) s.toNNReal) ∧
      IsGeneratingTrace (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞)
        (trOf D) ∧ stopTime ⊤ D = ((D.2.toNNReal : ℝ≥0) : ℝ) := by
  have hmin : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  refine ⟨?_, ?_, ?_⟩
  · funext x
    simp only [stopDrv, retOf, hmin]
  · rw [ENNReal.coe_toNNReal hfin]
    exact CounterflowRange.isGeneratingTrace_stopped (isGeneratingTrace_trOf hP)
  · simp only [stopTime, hmin]

/-- **Aliveness before the stop** in closure form. -/
theorem aliveAt_iff_notMem_closure_fillH {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) {z : ℂ} (hre : (c.1 z).im = 0) (hne : c.1 z ≠ 0) {r : ℝ} (hr0 : 0 ≤ r)
    (hrT : r < stopTime ⊤ D) :
    (∃ u, IsForwardSol (stopDrv ⊤ D) (c.1 z) r u) ↔ c.1 z ∉ closure (fillH (trOf D '' Icc 0 r.toNNReal)) := by
  obtain ⟨hdrv, hαs, htime⟩ := stopDrv_eq_and_isGeneratingTrace hP hfin
  have hWc : Continuous (stopDrv ⊤ D) := by
    have h := hP.continuous_stoppedReal.1
    rw [hdrv]
    simpa only [min_eq_right (le_top : D.2 ≤ ⊤)] using h
  have hW0 : stopDrv ⊤ D 0 = 0 := by
    have h := hP.continuous_stoppedReal.2
    rw [hdrv]
    simpa only using h
  have hrT' : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0, ← htime]
    exact hrT
  have hhull : fwdHull (stopDrv ⊤ D) r = fillH (trOf D '' Icc 0 r.toNNReal) := by
    have h := Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hαs hrT'
    rw [Real.coe_toNNReal _ hr0] at h
    rw [hdrv]
    exact h
  have hy : c.1 z = (((c.1 z).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre])
  rw [← hhull]
  constructor
  · rintro ⟨u, hu⟩
    exact Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hWc hr0 hu
  · intro hcl
    have hne' : (c.1 z).re ≠ 0 := fun h => hne (by rw [hy, h, Complex.ofReal_zero])
    rw [hy] at hcl
    obtain ⟨v, hv⟩ := Aux10.exists_isForwardSol_of_notMem_closure hWc hW0 hr0 hne' hcl
    exact ⟨v, by rw [hy]; exact hv⟩

/-- A forward solution exists on an empty time interval. -/
theorem exists_isForwardSol_of_neg {W : ℝ → ℝ} {z : ℂ} {r : ℝ} (hr : r < 0) : ∃ u, IsForwardSol W z r u := by
  refine ⟨fun _ => 0, ?_, fun t ht => absurd (ht.1.trans ht.2) (not_le.2 hr)⟩
  rw [Icc_eq_empty (not_le.2 hr)]
  exact continuousOn_empty _

/-- **Hits at the stop** in closure form. -/
theorem lHit_iff_closure {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤)
    {z : ℂ} (hre : (c.1 z).im = 0) (hne : c.1 z ≠ 0) :
    lHit c ⊤ D z ↔ (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ D → c.1 z ∉ closure (fillH (trOf D '' Icc 0 r.toNNReal))) ∧
      c.1 z ∈ closure (fillH (trOf D '' Icc 0 D.2.toNNReal)) := by
  rw [lHit_iff hP hfin hre hne]
  refine and_congr_left' ⟨fun h r hr0 hrT => (aliveAt_iff_notMem_closure_fillH hP hfin hre hne hr0 hrT).1 (h r hrT),
    fun h r hrT => ?_⟩
  rcases lt_or_ge r 0 with hr | hr0
  · exact exists_isForwardSol_of_neg hr
  · exact (aliveAt_iff_notMem_closure_fillH hP hfin hre hne hr0 hrT).2 (h r hr0 hrT)

end InteractingSLE.Theorem14.SB.Lk
