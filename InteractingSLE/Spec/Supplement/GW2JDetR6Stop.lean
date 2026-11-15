/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Prefix
import InteractingSLE.Spec.Supplement.GW2JDetR3Level

/-! # The physical-capacity rule for an arbitrary matching relative driver -/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR6

open Restart Exist.StagedLaw GW2JDetR3 GW2JDetR4 Sec7.Lemma71I

/-- Reading the inverse clock on rational prefixes identifies the attained
physical-capacity stop. Later values of the candidate are irrelevant. -/
theorem physicalCapacityStop_eq_of_clock_prefix
    (s t : ℝ≥0) (r : RecData) (e : (ℝ≥0 → ℝ) × ℝ≥0∞)
    {a : ℝ≥0 → ℝ} (ha : IsClockOn a (t : ℝ≥0∞))
    (hf : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ capLife a t →
      prefixCapacity s q r (killedCode e) = (invClock a t q : ℝ≥0∞)) :
    physicalCapacityStop s (t : ℝ≥0∞) r e = ((a t).toNNReal : ℝ≥0∞) := by
  let v := (a t).toNNReal
  have hLife : capLife a (t : ℝ≥0∞) = (v : ℝ≥0∞) := by
    simp only [capLife, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.toNNReal_coe]
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (ha.nonneg le_rfl)]
  let I := invClock a (t : ℝ≥0∞)
  let g : ℝ≥0 → ℝ≥0∞ := fun u => (I (min u v) : ℝ≥0∞)
  have hmemb : ∀ u : ℝ≥0, ((min u v : ℝ≥0) : ℝ≥0∞) ≤ capLife a t := by
    intro u
    rw [hLife]
    exact ENNReal.coe_le_coe.mpr (min_le_right _ _)
  have hgc : Continuous g := ENNReal.continuous_coe.comp
    (ha.continuousOn_invClock.comp_continuous (continuous_id.min continuous_const) hmemb)
  have hgm : Monotone g := by
    intro u u' huu'
    exact ENNReal.coe_le_coe.mpr
      (ha.strictMonoOn_invClock.monotoneOn (hmemb u) (hmemb u') (min_le_min huu' le_rfl))
  have hIv : I v = t := ha.invClock_apply le_rfl
  have hgv : g v = (t : ℝ≥0∞) := by simp only [g, min_self, hIv]
  have hglt : ∀ u < v, g u < (t : ℝ≥0∞) := by
    intro u huv
    have huCap : (u : ℝ≥0∞) ≤ capLife a t := by
      rw [hLife]
      exact ENNReal.coe_le_coe.mpr huv.le
    have hvCap := hmemb v
    rw [min_self] at hvCap
    have h := ha.strictMonoOn_invClock huCap hvCap huv
    change I u < I v at h
    simpa only [g, min_eq_left huv.le, hIv] using ENNReal.coe_lt_coe.mpr h
  apply levelRule_eq_of_continuous_prefix hgc hgm hgv.ge hglt
  intro q hq
  have hqCap : ((q : ℝ≥0) : ℝ≥0∞) ≤ capLife a t := by
    rw [hLife]
    exact ENNReal.coe_le_coe.mpr hq
  rw [hf q hqCap]
  simp only [g, min_eq_left hq, I]

/-- The total inverse record uses only a selected rational prefix below the
given buffer. Capacity crossing and correctness of those prefixes suffice. -/
theorem inverseRecord_eq_of_prefix_reads (s t : ℝ≥0) (r : RecData)
    (U : ℝ≥0 → ℝ) (B : ℝ≥0∞) (v : ℝ≥0) (hvB : (v : ℝ≥0∞) < B)
    (R : RecData)
    (hcross : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < B →
      ((t : ℝ≥0∞) < prefixCapacity s q r (killedCode (U, B)) ↔ v < (q : ℝ≥0)))
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < B → v < (q : ℝ≥0) →
      physicalRecordRead s t (r, prefixRecord q (killedCode (U, B))) = R) :
    inverseRecord s t (r, (U, B)) = R := by
  let x : BufferInput := (r, killedCode (U, B), B)
  obtain ⟨b, hvb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hvB
  obtain ⟨q, hvq, hqb⟩ := exists_rat_btwn
    (NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp hvb))
  have hq0 : (0 : ℚ) ≤ q := by
    exact_mod_cast v.coe_nonneg.trans hvq.le
  let q' : ℚ≥0 := ⟨q, hq0⟩
  have hqB : ((q' : ℝ≥0) : ℝ≥0∞) < B :=
    (ENNReal.coe_le_coe.mpr (show (q' : ℝ≥0) ≤ b by exact_mod_cast hqb.le)).trans_lt hb
  have hex : ∃ q : ℚ≥0, IsBuffer s t x q :=
    ⟨q', hqB, (hcross q' hqB).mpr (by exact_mod_cast hvq)⟩
  have hbuf := isBuffer_bufferTime s t x hex
  exact hread _ hbuf.1 ((hcross _ hbuf.1).mp hbuf.2)

end InteractingSLE.Theorem14.GW2JDetR6
