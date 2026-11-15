/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Read

/-! # Inverse hulls read from a live prefix of any continuous relative driver -/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR6

open Exist.StagedLaw Supp8.GB6 GW2JDetR3

/-- A literal rational prefix has the original driver's hull, including at
the prefix endpoint. Continuity is used on a slightly larger live interval. -/
theorem fwdHull_live_prefix {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2}) (h0 : e.1 0 = 0)
    {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < e.2) {u : ℝ≥0}
    (hu : u ≤ (q : ℝ≥0)) :
    fwdHull (rdrv (prefixRecord q (killedCode e))) u =
      fwdHull (Ito.rpath e.1) u := by
  obtain ⟨b, hqb, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hq
  have hub : (u : ℝ) < b := by
    exact_mod_cast hu.trans_lt (ENNReal.coe_lt_coe.mp hqb)
  apply LocalExt.fwdHull_congr_of_continuousOn (continuous_rdrv _).continuousOn
    ((hc.comp continuous_real_toNNReal.continuousOn
      (fun x hx => (ENNReal.coe_le_coe.mpr
        (Real.toNNReal_le_iff_le_coe.mpr hx.2)).trans_lt hb))) u.coe_nonneg hub
  intro x hx
  apply rdrv_prefixRecord_killedCode hc h0 hq
  exact ⟨hx.1, hx.2.trans (by exact_mod_cast hu)⟩

/-- The inverse hull of a live rational prefix is the inverse chart image of
the original driver's hull at every earlier time. -/
theorem inverseHull_live_prefix (s : ℝ≥0) (r : RecData)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2}) (h0 : e.1 0 = 0)
    {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < e.2) {u : ℝ≥0}
    (hu : u ≤ (q : ℝ≥0)) :
    inverseHull s u (r, prefixRecord q (killedCode e)) =
      relInv (rdrv r) s '' fwdHull (Ito.rpath e.1) u := by
  unfold inverseHull
  rw [fwdHull_live_prefix hc h0 hq hu]

/-- Exact physical capacity follows from the inverse-hull identity; no
regularized geometric driver must be selected jointly with the candidate. -/
theorem physicalCapacity_live_prefix (s : ℝ≥0) (r : RecData)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2}) (h0 : e.1 0 = 0)
    {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < e.2) {u t : ℝ≥0}
    (hu : u ≤ (q : ℝ≥0))
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {v | (v : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < T)
    (hinv : relInv (rdrv r) s '' fwdHull (Ito.rpath e.1) u =
      fwdHull (Ito.rpath w) t) :
    physicalCapacity s u (r, prefixRecord q (killedCode e)) = t := by
  unfold physicalCapacity
  rw [inverseHull_live_prefix s r hc h0 hq hu, hinv,
    hcapHit_fwdHull_of_live_trace hγ hw hw0 ht,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) t.coe_nonneg)]
  ring

end InteractingSLE.Theorem14.GW2JDetR6
