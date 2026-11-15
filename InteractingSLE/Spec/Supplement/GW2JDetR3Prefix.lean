/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Stopping

/-!
# The causal rational capacity is the actual inverse-hull capacity

Before the relative lifetime, the frozen rational prefix has exactly the
original relative hull, including its endpoint. Thus the killed-path stopping
rule reads the same physical capacity as every later live buffered record.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR3

open Exist Exist.Staged Exist.StagedLaw Supp8.GB6 GW2TipSystem

/-- Rational samples through a live cutoff give the literal stopped record. -/
theorem prefixRecord_eq_recOf (q : ℚ≥0) (w : ℝ≥0 → ℝ) (c : ℚ≥0 → ℝ)
    (hc : ∀ r ≤ q, c r = w (r : ℝ≥0)) :
    prefixRecord q c = recOf (((q : ℝ≥0) : ℝ≥0∞)) (w, ⊤) := by
  apply Prod.ext
  · funext x
    change c (min x.toNNRat q) =
      w (min (((x : ℝ).toNNReal : ℝ≥0∞)) (min ((q : ℝ≥0) : ℝ≥0∞) ⊤)).toNNReal
    rw [min_top_right, ← ENNReal.coe_min, ENNReal.toNNReal_coe,
      ← coe_toNNRat_eq, ← NNRat.cast_min]
    exact hc _ (min_le_right _ _)
  · have hn : ¬ (⊤ : ℝ≥0∞) ≤ ((q : ℝ≥0) : ℝ≥0∞) :=
      not_le.mpr ENNReal.coe_lt_top
    simp only [prefixRecord, recOf, readRec, retOf, min_top_right, hn, decide_false]

/-- The decoder of a live rational prefix equals the original driver through
the cutoff. Continuity is required only before the original lifetime. -/
theorem rdrv_prefixRecord_killedCode {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2}) (h0 : e.1 0 = 0)
    {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < e.2) :
    EqOn (rdrv (prefixRecord q (killedCode e))) (Ito.rpath e.1) (Icc 0 (q : ℝ)) := by
  let w := LP.freezeAt (q : ℝ≥0) e.1
  have hw : Continuous w := LP.continuous_freezeAt
    (hc.mono fun t ht => (ENNReal.coe_le_coe.mpr ht).trans_lt hq)
  have hw0 : w 0 = 0 := by
    change e.1 (min 0 (q : ℝ≥0)) = 0
    rw [min_eq_left (show (0 : ℝ≥0) ≤ (q : ℝ≥0) from zero_le), h0]
  have hreg : IsRegularDriver (w, ⊤) :=
    ⟨hw.continuousOn, hw0,
      (fun t ht => (not_le.mpr ENNReal.coe_lt_top ht).elim), fun ht => (ht rfl).elim⟩
  have hrec : prefixRecord q (killedCode e) = recOf (((q : ℝ≥0) : ℝ≥0∞)) (w, ⊤) := by
    apply prefixRecord_eq_recOf
    intro r hr
    have hrq : (r : ℝ≥0) ≤ (q : ℝ≥0) := by exact_mod_cast hr
    have hrT := (ENNReal.coe_le_coe.mpr hrq).trans_lt hq
    simp only [killedCode, hrT, ↓reduceIte, w, LP.freezeAt, min_eq_left hrq]
  intro t ht
  rw [hrec]
  have hgood := isDrvGood_recOf_of_lt hreg
    (show (((q : ℝ≥0) : ℝ≥0∞)) < ⊤ from ENNReal.coe_lt_top)
  have htq : t.toNNReal ≤ (q : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr ht.2
  rw [rdrv_recOf_eq hreg hgood (by rw [min_top_right]; exact ENNReal.coe_ne_top)
    (by
      rw [rtime_recOf_coe, min_top_right, ENNReal.toNNReal_coe]
      exact_mod_cast ht.2)]
  exact congrArg e.1 (min_eq_left htq)

/-- A live causal prefix and any later live buffer have the same inverse-hull
capacity. This identifies the rational family used in the stopping rule. -/
theorem prefixCapacity_eq_buffer (s : ℝ≥0) (r : RecData)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2}) (h0 : e.1 0 = 0)
    {q : ℚ≥0} {b : ℝ≥0} (hqb : (q : ℝ≥0) < b) (hb : (b : ℝ≥0∞) < e.2) :
    prefixCapacity s q r (killedCode e) =
      ENNReal.ofReal (physicalCapacity s (q : ℝ≥0)
        (r, cfRec b (fun t (_ : Unit) => e.1 t) (fun _ => e.2) ())) := by
  have hqT : ((q : ℝ≥0) : ℝ≥0∞) < e.2 :=
    (ENNReal.coe_le_coe.mpr hqb.le).trans_lt hb
  have hprefix := rdrv_prefixRecord_killedCode hc h0 hqT
  have hbuf := GaugeE.record_prefix_eq (Wα := fun t (_ : Unit) => e.1 t)
    (ζα := fun _ => e.2) (ω := ()) b h0 hc hb
  have heq : EqOn (rdrv (prefixRecord q (killedCode e)))
      (rdrv (cfRec b (fun t (_ : Unit) => e.1 t) (fun _ => e.2) ()))
        (Icc 0 (q : ℝ)) := by
    intro t ht
    exact (hprefix ht).trans (hbuf ⟨ht.1, ht.2.trans (by exact_mod_cast hqb.le)⟩).symm
  have hK := LocalExt.fwdHull_congr_of_continuousOn
    (continuous_rdrv _).continuousOn (continuous_rdrv _).continuousOn
    (show (0 : ℝ) ≤ q by positivity) (show (q : ℝ) < b by exact_mod_cast hqb) heq
  have hcast : ((q : ℝ≥0) : ℝ) = (q : ℝ) := by norm_cast
  unfold prefixCapacity physicalCapacity inverseHull
  simp only [hcast]
  rw [hK]

end InteractingSLE.Theorem14.GW2JDetR3
