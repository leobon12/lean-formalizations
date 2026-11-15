/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NzVer

/-!
# A regular driver read off a record

Packet PROVE-SB2-LCMEAN, round 16 (D32: the root record). A record (`Exist.StagedLaw.RecData`: the stopped driver at the
rational times, the lifetime, the flag) determines, through its dyadic code, the regularized driver
(`StagedReg.regularize`, which reads a driver only through its dyadic code, its value at `0` and its lifetime):

* `ratOf`, `recPath`, **`recDrv`** (measurable in the record, regular at every record);
* `regularize_congr`: drivers with the same dyadic code, value at `0` and lifetime have the same regularization;
* **`recOf_recDrv`**: for a regular driver continuous up to its lifetime, the driver read off its record has its
  record.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nz

open Exist Exist.Staged Exist.StagedLaw Sec2.Assembly

open Classical in
/-- The rational equal to a time, if any (`0` otherwise). -/
def ratOf (s : ℝ≥0) : ℚ := if h : ∃ q : ℚ, (q : ℝ) = (s : ℝ) then h.choose else 0

theorem ratOf_spec {s : ℝ≥0} (h : ∃ q : ℚ, (q : ℝ) = (s : ℝ)) : ((ratOf s : ℚ) : ℝ) = (s : ℝ) := by
  classical
  unfold ratOf
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- The path read off a record at the rational times. -/
def recPath (r : RecData) : ℝ≥0 → ℝ := fun s => r.1 (ratOf s)

/-- **The regular driver read off a record.** -/
def recDrv (r : RecData) : (ℝ≥0 → ℝ) × ℝ≥0∞ := StagedReg.regularize ⊤ (recPath r, r.2.1)

theorem measurable_recDrv : Measurable recDrv := by
  refine (StagedReg.measurable_regularize ⊤).comp (Measurable.prodMk ?_ (measurable_fst.comp measurable_snd))
  exact measurable_pi_iff.2 fun s => (measurable_pi_apply (ratOf s)).comp measurable_fst

theorem isRegularDriver_recDrv (r : RecData) : IsRegularDriver (recDrv r) :=
  StagedReg.isRegularDriver_regularize ⊤ _

open Classical in
/-- **Drivers with the same dyadic code, value at `0` and lifetime have the same regularization.** -/
theorem regularize_congr (t : ℝ≥0∞) {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h1 : enc e.1 = enc e'.1) (h0 : e.1 0 = e'.1 0)
    (h2 : e.2 = e'.2) : StagedReg.regularize t e = StagedReg.regularize t e' := by
  unfold StagedReg.regularize StagedReg.GoodAll StagedReg.GoodTo
  rw [h1, h0, h2]

theorem exists_rat_dyad (n k : ℕ) : ∃ q : ℚ, (q : ℝ) = ((dyad n k : ℝ≥0) : ℝ) :=
  ⟨(k : ℚ) / 2 ^ n, by simp [dyad]⟩

/-- **The driver read off the record of a regular driver continuous up to its lifetime has its record.** -/
theorem recOf_recDrv {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min ⊤ e.2}) : recOf ⊤ (recDrv (recOf ⊤ e)) = recOf ⊤ e := by
  set es : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun s => e.1 (min (s : ℝ≥0∞) e.2).toNNReal, e.2) with hes
  have hval : ∀ s : ℝ≥0, (∃ q : ℚ, (q : ℝ) = (s : ℝ)) → recPath (recOf ⊤ e) s = es.1 s := by
    intro s hs
    have hq := ratOf_spec hs
    have hq' : ((ratOf s : ℝ)).toNNReal = s := by rw [hq, Real.toNNReal_coe]
    simp only [recPath, recOf, readRec, retOf, es, hq', min_eq_right le_top]
  have hcong : recDrv (recOf ⊤ e) = StagedReg.regularize ⊤ es := by
    refine regularize_congr ⊤ ?_ ?_ ?_
    · funext n k
      exact hval _ (exists_rat_dyad n k)
    · exact hval 0 ⟨0, by simp⟩
    · simp [recOf, readRec, retOf, es]
  have hes0 : es.1 0 = 0 := by
    simp only [es, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
    exact he.2.1
  have hesc : ContinuousOn es.1 {s | (s : ℝ≥0∞) < es.2} := by
    have hsub : {s : ℝ≥0 | (s : ℝ≥0∞) < es.2} ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ min ⊤ e.2} := fun s hs => by
      show (s : ℝ≥0∞) ≤ min ⊤ e.2
      rw [min_eq_right le_top]
      exact le_of_lt hs
    refine (hc.mono hsub).congr fun s hs => ?_
    show e.1 (min (s : ℝ≥0∞) e.2).toNNReal = e.1 s
    rw [min_eq_left (le_of_lt hs), ENNReal.toNNReal_coe]
  have hagree : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e.2 → (StagedReg.regularize ⊤ es).1 s = e.1 s := by
    intro s hs
    rw [StagedReg.regularize_eq_of_lt ⊤ hes0 hesc hs]
    show e.1 (min (s : ℝ≥0∞) e.2).toNNReal = e.1 s
    rw [min_eq_left (le_of_lt hs), ENNReal.toNNReal_coe]
  rw [hcong]
  unfold recOf
  rw [StagedDet.retOf_eq_of_agree he (StagedReg.isRegularDriver_regularize ⊤ es) hc
    (StagedReg.regularize_snd ⊤ es) hagree]

end InteractingSLE.Theorem14.SB.Nz
