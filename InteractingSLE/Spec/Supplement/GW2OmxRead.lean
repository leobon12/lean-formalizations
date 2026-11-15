/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxGap
import InteractingSLE.Spec.Supplement.GW2TjMarks
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Supplement.GB6RestartProofR1

/-!
# GW2's open lines: trace readers of the explored path and of the retained counterflow, measurable for the raw marks

Packet PROVE-GW2-STAGEMEAN, R120 round (localization). The physical no-contact event is read through measurable trace
readers (`LP.traceAt`):
* `explRead c r l a q ω`: the explored path's trace at `q`, read from `schedW` (measurable for RELDET's raw marks
  `kerMarks t` when `q ≤ T + t`, **`measurable_explRead_kerMarks`**);
* `cfRead c q ω`: the counterflow's trace at `q`, read from the record `gb6Rec` (measurable for `σ(gb6Rec)`, hence
  for `kerMarks t`, **`measurable_cfRead_kerMarks`**);
* the no-contact event `noContact c r l a t = gapEvent cfRead explRead s T` and **`measurableSet_noContact`**;
* **`explRead_eq_of_trace`**, **`cfRead_eq_of_trace`**: the readers are the generating traces where these exist.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd Supp8.GB6 Exist.StagedLaw

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The explored path's trace reader. -/
def explRead (ω : Ω) (q : ℝ≥0) : ℂ := LP.traceAt q (fun u => schedW c r l a u ω)

/-- The retained counterflow's trace reader, from the record. -/
def cfRead (ω : Ω) (q : ℝ≥0) : ℂ := LP.traceAt q (fun u : ℝ≥0 => rdrv (gb6Rec c.s c.W c.ζ ω) u)

/-- **The physical no-contact event** before the stage start (GB6's `prefixGap` form). -/
def noContact : Set Ω := gapEvent (cfRead c) (explRead c r l a) c.s (historyTime c r l)

theorem measurable_explRead_kerMarks (t : ℝ≥0) {q : ℝ≥0} (hq : q ≤ historyTime c r l + t) :
    Measurable[kerMarks c r l a t] (fun ω => explRead c r l a ω q) := by
  have hpath : Measurable[kerMarks c r l a t]
      (fun ω => LP.freezeAt (historyTime c r l + t) (fun u => schedW c r l a u ω)) :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (kerMarks c r l a t) _ _).2 fun u =>
      measurable_schedW_kerMarks c r l a t (min_le_right u _)
  have he : (fun ω => explRead c r l a ω q) =
      fun ω => LP.traceAt q (LP.freezeAt (historyTime c r l + t) (fun u => schedW c r l a u ω)) := by
    funext ω
    refine LP.traceAt_congr fun u hu => ?_
    show schedW c r l a u ω = schedW c r l a (min u (historyTime c r l + t)) ω
    rw [min_eq_left (hu.trans hq)]
  rw [he]
  exact (LP.measurable_traceAt q).comp hpath

theorem measurable_cfRead_kerMarks (t : ℝ≥0) (q : ℝ≥0) :
    Measurable[kerMarks c r l a t] (fun ω => cfRead c ω q) := by
  have hrec : Measurable[kerMarks c r l a t] (gb6Rec c.s c.W c.ζ) :=
    Measurable.of_comap_le (le_sup_left.trans le_sup_left)
  have hpath : Measurable fun y : RecData => fun u : ℝ≥0 => rdrv y u :=
    measurable_pi_iff.2 fun u => Exist.StagedLaw.measurable_rdrv_apply (u : ℝ)
  exact (LP.measurable_traceAt q).comp (hpath.comp hrec)

theorem measurableSet_noContact (t : ℝ≥0) : MeasurableSet[kerMarks c r l a t] (noContact c r l a) := by
  unfold noContact gapEvent gapAt
  refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ => ?_
  by_cases hq : 0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ c.s ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ historyTime c r l
  · have e : {ω | (0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ c.s ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ historyTime c r l) →
        1 / ((n : ℝ) + 1) ≤ ‖cfRead c ω (q₁ : ℝ).toNNReal * explRead c r l a ω (q₂ : ℝ).toNNReal + 1‖} =
        {ω | 1 / ((n : ℝ) + 1) ≤ ‖cfRead c ω (q₁ : ℝ).toNNReal * explRead c r l a ω (q₂ : ℝ).toNNReal + 1‖} := by
      ext ω
      simp only [mem_ofPred_eq, hq, and_self, true_implies]
    rw [e]
    have hle : (q₂ : ℝ).toNNReal ≤ historyTime c r l + t := by
      rw [Real.toNNReal_le_iff_le_coe]
      have := hq.2.2.2
      have h2 : (historyTime c r l : ℝ) ≤ ((historyTime c r l + t : ℝ≥0) : ℝ) := by
        exact_mod_cast le_add_of_nonneg_right zero_le
      linarith
    have hpair : Measurable[kerMarks c r l a t] (fun ω => (cfRead c ω (q₁ : ℝ).toNNReal,
        explRead c r l a ω (q₂ : ℝ).toNNReal)) :=
      (measurable_cfRead_kerMarks c r l a t _).prodMk (measurable_explRead_kerMarks c r l a t hle)
    have hcont : Continuous fun p : ℂ × ℂ => ‖p.1 * p.2 + 1‖ :=
      ((continuous_fst.mul continuous_snd).add continuous_const).norm
    exact (hcont.measurable.comp hpair) measurableSet_Ici
  · simp only [hq, false_implies, ofPred_true]
    exact MeasurableSet.univ

/-- The explored reader is the explored path's generating trace. -/
theorem explRead_eq_of_trace {ω : Ω} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ η) (hc : Continuous fun u => schedW c r l a u ω)
    (h0 : schedW c r l a 0 ω = 0) (q : ℝ≥0) : explRead c r l a ω q = η q :=
  LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top

/-- The counterflow reader is the counterflow's generating trace up to the retained time. -/
theorem cfRead_eq_of_trace {ω : Ω} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η)
    (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0) (hs : (c.s : ℝ≥0∞) < c.ζ ω) {q : ℝ≥0}
    (hq : q ≤ c.s) : cfRead c ω q = η q := by
  have e : cfRead c ω q = LP.traceAt q (fun u => c.W u ω) := by
    refine LP.traceAt_congr fun u hu => ?_
    have h := rdrv_recOf_cfE (s := c.s) (W := c.W) (ζ := c.ζ) (ω := ω) h0 hc.continuousOn hs
      (x := (u : ℝ)) (by exact_mod_cast hu.trans hq)
    simp only [Real.toNNReal_coe] at h
    exact h
  rw [e]
  exact LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top

end InteractingSLE.Theorem14.GW2Omx
