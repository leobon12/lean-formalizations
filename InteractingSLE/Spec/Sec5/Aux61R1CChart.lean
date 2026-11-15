/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CGood

/-!
# R1's restart chart at every record: the good records and the two-stage retraction

Packet PROVE-AUX61-R1CHART. For a positive counterflow time `s` and a rational restart time `q`:

1. **Stage 1.** Read R1's data through the retraction onto the regular records (`RegRec`); then the target selector
   of R1 (`Aux61Restart.exists_measurable_original_target_component`) gives a measurable base point `selN s q y` of the
   original right-target component `tgtComp s q y` (the component of the retained domain with `1` in its closure).
2. **The good records** (`goodSet s q`): regular records with
   * **clearance** (`ClearRec`): the restart tip `η(q)` is at positive distance from R1's contact obstacle
     `retObs s y = (ℍ ∖ K_s)ᶜ` (equivalently, off `ℝ` and at positive distance from the counterflow hull);
   * **incidence** (`IncRec`): the current access at the tip — the points `F_q(i/(n+1))` of the own inverse map at
     `q` — eventually lies in the original right-target component (the source's restriction, Astra follow-up 4,
     Part (1), §1.1).
   The good records form a Borel set (`measurableSet_goodSet`).
3. **Stage 2.** Read R1's data through the retraction onto the good records (`finY`, `finU`, `finη`). When some
   record is good, **R1's restart chart exists** (`hasChart`, from the landed
   `Aux61Restart.has_original_target_restart_chart_of_protection`), and on the good records the data are the plain
   record readers (`finY_of_mem`, `finη_eqOn`), with the restart tip off the obstacle (`recTrace_notMem_retObs`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61R1C

open LawUnique Restart.FlowStopIdentG Aux61Restart Aux61Marks
open Aux61SlitW (rationalTime)

variable {nL nR : ℕ} (s : ℝ≥0) (q : ℚ)

/-- The dense sequence of base points. -/
abbrev baseSeq : ℕ → ℂ := TopologicalSpace.denseSeq ℂ

/-- The regular records, as a set. -/
def regSet : Set (Rec nL nR) := {y | RegRec s q y}

/-! ### Stage 1: the regular retraction and the target selector -/

/-- Stage-1 counterflow record. -/
def stY (y : Rec nL nR) : HistorySpace 0 0 := (retr (regSet s q) y).1

/-- Stage-1 own driver. -/
def stU (t : ℝ≥0) (y : Rec nL nR) : ℝ := recU q t (retr (regSet s q) y)

/-- Stage-1 own trace. -/
def stη (y : Rec nL nR) : ℝ → ℂ := recη q (retr (regSet s q) y)

variable {s q}

/-- The pointwise facts of the stage-1 data. -/
theorem stage1_facts (h : (regSet (nL := nL) (nR := nR) s q).Nonempty) :
    0 ≤ (q : ℝ) ∧ Measurable (retr (regSet (nL := nL) (nR := nR) s q)) ∧
      (∀ y : Rec nL nR, RegRec s q (retr (regSet s q) y)) ∧
      (Measurable fun y : Rec nL nR => GlueCond.cfStop s (stY s q y)) ∧
      (∀ t ∈ Icc (0 : ℝ) q, Measurable fun y : Rec nL nR => stη s q y t) := by
  have hreg : ∀ y : Rec nL nR, RegRec s q (retr (regSet s q) y) := retr_mem h
  have hm := measurable_retr (measurableSet_regRec (nL := nL) (nR := nR) s q)
  obtain ⟨y₀, hy₀⟩ := h
  have hqq : (0 : ℚ) ≤ q := hy₀.1.le
  exact ⟨by exact_mod_cast hqq, hm, hreg, (GlueCond.measurable_cfStop s).comp (measurable_fst.comp hm),
    fun t ht => (measurable_recη hqq ht.2).comp hm⟩

variable (s q)

/-- **R1's target selector on the stage-1 data.** -/
theorem exists_selector (h : (regSet (nL := nL) (nR := nR) s q).Nonempty) :
    ∃ N : Rec nL nR → ℕ, Measurable N ∧
      (∀ y, baseSeq (N y) ∈ retainedDomain (historyHull s (stY s q) y) (stη s q y) q) ∧
      ∀ y, (1 : ℂ) ∈ closure (connectedComponentIn (retainedDomain (historyHull s (stY s q) y) (stη s q y) q)
        (baseSeq (N y))) := by
  obtain ⟨hq, -, hreg, hY, hmeas⟩ := stage1_facts h
  have hc : ∀ y, ContinuousOn (stη s q y) (Icc 0 (q : ℝ)) := fun y => (hreg y).facts.2.2.2.2.2.2.1
  have hUm := measurableSet_closedBall_subset_historyDomain hq hY hc hmeas
  have htarget : ∀ y : Rec nL nR, ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆
      retainedDomain (historyHull s (stY s q) y) (stη s q y) q := fun y =>
    exists_original_right_target_collar (hc y) (hreg y).facts.2.2.2.2.2.2.2.1 (hreg y).facts.2.2.2.2.2.1
      (hreg y).facts.2.2.2.2.2.2.2.2
  obtain ⟨N, hN, hb, -, hcl⟩ := exists_measurable_original_target_component hUm htarget
    (TopologicalSpace.denseRange_denseSeq ℂ)
  exact ⟨N, hN, hb, hcl⟩

open Classical in
/-- **The measurable target base point** (stage 1). -/
def selN : Rec nL nR → ℕ :=
  if h : (regSet (nL := nL) (nR := nR) s q).Nonempty then Classical.choose (exists_selector s q h) else fun _ => 0

/-- **The original right-target component** of a record (stage 1). -/
def tgtComp (y : Rec nL nR) : Set ℂ :=
  connectedComponentIn (retainedDomain (recHull s (retr (regSet s q) y)) (recη q (retr (regSet s q) y)) q)
    (baseSeq (selN s q y))

variable {s q}

theorem selN_spec (h : (regSet (nL := nL) (nR := nR) s q).Nonempty) :
    Measurable (selN (nL := nL) (nR := nR) s q) ∧
      (∀ y : Rec nL nR, baseSeq (selN s q y) ∈ retainedDomain (historyHull s (stY s q) y) (stη s q y) q) ∧
      ∀ y : Rec nL nR, (1 : ℂ) ∈ closure (tgtComp s q y) := by
  have he : selN (nL := nL) (nR := nR) s q = Classical.choose (exists_selector s q h) := by
    unfold selN
    simp only [h, ↓reduceDIte]
  have hs := Classical.choose_spec (exists_selector s q h)
  rw [← he] at hs
  exact ⟨hs.1, hs.2.1, hs.2.2⟩

variable (s q)

/-- The access points `i/(n+1)` at the tip. -/
def accPt (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I

theorem accPt_im_pos (n : ℕ) : 0 < (accPt n).im := by
  simp only [accPt, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
    mul_zero, add_zero]
  positivity

theorem tendsto_accPt : Tendsto accPt atTop (𝓝[H] 0) := by
  refine tendsto_ofReal_mul_I_nhdsWithin_H.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · show (0 : ℝ) < 1 / ((n : ℝ) + 1)
    positivity

/-- **Clearance**: the restart tip is at positive distance from R1's contact obstacle. -/
def ClearRec (y : Rec nL nR) : Prop := 0 < infDist (recTrace y.2 q) (retObs s y)

/-- **Incidence**: the current access at the tip eventually lies in the original right-target component. -/
def IncRec (y : Rec nL nR) : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → fwdMapInv (Ito.rpath fun t => stU s q t y) (rationalTime q) (accPt n) ∈ tgtComp s q y

/-- **The good records.** -/
def goodSet : Set (Rec nL nR) := {y | RegRec s q y ∧ ClearRec s q y ∧ IncRec s q y}

theorem goodSet_subset_regSet : goodSet (nL := nL) (nR := nR) s q ⊆ regSet s q := fun _ hy => hy.1

/-- **The good records form a Borel set.** -/
theorem measurableSet_goodSet : MeasurableSet (goodSet (nL := nL) (nR := nR) s q) := by
  by_cases h : (regSet (nL := nL) (nR := nR) s q).Nonempty
  · obtain ⟨hq, hm, hreg, hY, hmeas⟩ := stage1_facts h
    obtain ⟨hN, hb, -⟩ := selN_spec h
    have hc : ∀ y, ContinuousOn (stη s q y) (Icc 0 (q : ℝ)) := fun y => (hreg y).facts.2.2.2.2.2.2.1
    have h0 : ∀ y, stη s q y 0 = 0 := fun y => (hreg y).facts.2.2.2.2.2.2.2.1
    have hprops := historyComponent_properties hq hY hc h0 hmeas hN hb
    have hUc : ∀ y, Continuous fun t => stU s q t y := fun y => (hreg y).facts.2.1
    have hU0 : ∀ y, stU s q 0 y = 0 := fun y => (hreg y).facts.2.2.1
    have hUm : ∀ t, Measurable (stU s q t) := fun t => (measurable_recU q t).comp hm
    have hdrive : ∀ y : Rec nL nR, QuantumZipper.drive 1 (stU s q) y = Ito.rpath fun t => stU s q t y := fun y => by
      funext t
      simp only [QuantumZipper.drive, Real.sqrt_one, one_mul, Ito.rpath]
    have hmem : ∀ n, MeasurableSet {y : Rec nL nR |
        fwdMapInv (Ito.rpath fun t => stU s q t y) (rationalTime q) (accPt n) ∈ tgtComp s q y} := by
      intro n
      have hx := QuantumZipper.RS.measurable_fwdMapInv_drive hUm hUc hU0 1 (rationalTime q).coe_nonneg
        (accPt_im_pos n)
      simp only [hdrive] at hx
      exact measurableSet_mem_of_closedBall (fun y => (hprops.1 y).1) hprops.2 hx
    refine (measurableSet_regRec s q).inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt measurable_const
        (measurable_infDist_retObs_comp s ((measurable_recTrace _).comp measurable_snd))
    · exact measurableSet_setOfPred.2 (Measurable.exists fun n₀ => Measurable.forall fun n =>
        Measurable.imp measurable_const (measurableSet_setOfPred.1 (hmem n)))
  · have he : goodSet (nL := nL) (nR := nR) s q = ∅ :=
      eq_empty_of_forall_notMem fun y hy => h ⟨y, hy.1⟩
    rw [he]
    exact MeasurableSet.empty

/-! ### Stage 2: the good retraction and R1's chart -/

/-- R1's counterflow record (stage 2). -/
def finY (y : Rec nL nR) : HistorySpace 0 0 := (retr (goodSet s q) y).1

/-- R1's own driver (stage 2). -/
def finU (t : ℝ≥0) (y : Rec nL nR) : ℝ := recU q t (retr (goodSet s q) y)

/-- R1's own global trace (stage 2). -/
def finη (y : Rec nL nR) : ℝ → ℂ := recη q (retr (goodSet s q) y)

variable {s q}

/-- The counterflow hull of a positive time is nonempty. -/
theorem recHull_nonempty (hs : 0 < s) (y : Rec nL nR) : (recHull s y).Nonempty :=
  (QuantumZipper.RS.fwdHull_nonempty_of_pos (CrossCond.Word49.continuous_cfDrv0 s _)
    (CrossCond.Word49.cfDrv0_zero s _) (by exact_mod_cast hs)).image _

/-- On a record with clearance the restart tip is off R1's obstacle. -/
theorem recTrace_notMem_retObs {y : Rec nL nR} (hy : ClearRec s q y) : recTrace y.2 q ∉ retObs s y :=
  fun hmem => by
    have h : 0 < infDist (recTrace y.2 q) (retObs s y) := hy
    rw [infDist_zero_of_mem hmem] at h
    exact lt_irrefl _ h

/-- Clearance gives a positive distance from the counterflow hull. -/
theorem infDist_recHull_pos (hs : 0 < s) {y : Rec nL nR} (hy : ClearRec s q y) :
    0 < infDist (recTrace y.2 q) (recHull s y) := by
  have hy' : 0 < infDist (recTrace y.2 q) (retObs s y) := hy
  have hsub : recHull s y ⊆ retObs s y := fun z hz hz' => hz'.2 hz
  exact lt_of_lt_of_le hy' (infDist_le_infDist_of_subset hsub (recHull_nonempty hs y))

theorem finY_of_mem {y : Rec nL nR} (hy : y ∈ goodSet s q) : finY s q y = y.1 := by
  rw [finY, retr_of_mem hy]

theorem finη_of_mem {y : Rec nL nR} (hy : y ∈ goodSet s q) : finη s q y = recη q y := by
  rw [finη, retr_of_mem hy]

/-- **On good records R1's trace is the plain record reader on `[0, q]`.** -/
theorem finη_eqOn {y : Rec nL nR} (hy : y ∈ goodSet s q) :
    EqOn (finη s q y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc 0 (q : ℝ)) := by
  intro t ht
  rw [finη_of_mem hy, recη_of_le hy.1.1.le y ht.2]
  rfl

/-- On regular records the target component is the component of the record's own retained domain. -/
theorem tgtComp_of_mem {y : Rec nL nR} (hy : y ∈ regSet s q) :
    tgtComp s q y = restartComponent (recHull s y) (recη q y) q (baseSeq (selN s q y)) := by
  rw [tgtComp, retr_of_mem hy]
  rfl

/-- **R1's restart chart exists at every record** once some record is good. -/
theorem hasChart (hs : 0 < s) (hG : (goodSet (nL := nL) (nR := nR) s q).Nonempty) :
    HasOriginalTargetRestartChart s (rationalTime q) q (finY (nL := nL) (nR := nR) s q) (finη s q) (finU s q)
      baseSeq := by
  have hgood : ∀ y : Rec nL nR, retr (goodSet s q) y ∈ goodSet s q := retr_mem hG
  have hreg : (regSet (nL := nL) (nR := nR) s q).Nonempty := hG.mono (goodSet_subset_regSet s q)
  have hm := measurable_retr (measurableSet_goodSet (nL := nL) (nR := nR) s q)
  obtain ⟨y₀, hy₀⟩ := hG
  have hq : (0 : ℝ) < q := hy₀.1.facts.1
  have hqq : (0 : ℚ) ≤ q := by exact_mod_cast hq.le
  obtain ⟨-, -, hcl⟩ := selN_spec hreg
  refine has_original_target_restart_chart_of_protection (coe_rationalTime hqq) hq
    ((GlueCond.measurable_cfStop s).comp (measurable_fst.comp hm)) (fun y => (hgood y).1.facts.2.1)
    (fun y => (hgood y).1.facts.2.2.1) (fun t _ => (measurable_recU q t).comp hm)
    (fun y => (hgood y).1.facts.2.2.2.1) (fun y => (hgood y).1.facts.2.2.2.2.1)
    (fun y => (hgood y).1.facts.2.2.2.2.2.1) (fun t ht => (measurable_recη hqq ht.2).comp hm) ?_
    (fun y => (hgood y).1.facts.2.2.2.2.2.2.2.2) ?_ (TopologicalSpace.denseRange_denseSeq ℂ)
  · intro y
    have h := infDist_recHull_pos hs (hgood y).2.1
    rwa [← recη_of_le hqq _ le_rfl] at h
  · intro y
    set z := retr (goodSet s q) y with hz
    have hzr : z ∈ regSet s q := (hgood y).1
    refine ⟨baseSeq (selN s q z), ?_, ?_⟩
    · have h := hcl z
      rwa [tgtComp_of_mem hzr] at h
    · obtain ⟨n₀, hn₀⟩ := (hgood y).2.2
      have hev : ∀ᶠ n in atTop, fwdMapInv (Ito.rpath fun t => finU s q t y) (rationalTime q) (accPt n) ∈
          restartComponent (historyHull s (finY s q) y) (finη s q y) q (baseSeq (selN s q z)) := by
        refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
        have h := hn₀ n hn
        rw [tgtComp_of_mem hzr] at h
        simp only [stU] at h
        rw [← hz, retr_of_mem hzr] at h
        exact h
      exact (tendsto_accPt).frequently hev.frequently

end InteractingSLE.Sec5.Aux61R1C
