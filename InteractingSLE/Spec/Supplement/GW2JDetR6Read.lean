/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Contact

/-!
# Reading a physical record from one relative clock buffer

This exposes the deterministic clock calculation for an arbitrary buffer
record, so it applies to the canonical relative driver as well as the
geometric witness used in R4. The inverse and capacity operations are the
landed total Borel readers.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR6

open Exist.StagedLaw Supp8.GB6 GW2TipSystem GW2JDetR3 GW2JDetR4

/-- One live relative buffer reconstructs the physical record whenever its
inverse hulls have the physical clock's capacity. Only clock values inside
that buffer are used. -/
theorem physicalRecordRead_eq_of_clockBuffer
    (s : ℝ≥0) (p : RecData × RecData) {a : ℝ≥0 → ℝ} {S T : ℝ≥0∞}
    (ha0 : a 0 = 0) (hm : StrictMonoOn a {u | (u : ℝ≥0∞) < S})
    (hc : ContinuousOn a {u | (u : ℝ≥0∞) < S})
    {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (hST : S ≤ T) {b : ℝ≥0}
    (hb : (b : ℝ≥0∞) < ⨆ (u : ℝ≥0) (_ : (u : ℝ≥0∞) < S),
      ((a u).toNNReal : ℝ≥0∞))
    (hread : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S → (a u).toNNReal < b →
      inverseHull s (a u).toNNReal p = fwdHull (Ito.rpath w) u ∧
        physicalCapacity s (a u).toNNReal p = u)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < S) (htb : (a t).toNNReal < b) :
    physicalRecordRead s t p =
      cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  have hn : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S → 0 ≤ a u := by
    intro u hu
    have h := hm.monotoneOn (bot_le.trans_lt hu) hu (zero_le : (0 : ℝ≥0) ≤ u)
    simpa only [ha0] using h
  have hcut : ∀ u ≤ t, capacityCut s u p = ((a u).toNNReal : ℝ≥0∞) := by
    intro u hut
    have hu : (u : ℝ≥0∞) < S := (ENNReal.coe_le_coe.mpr hut).trans_lt ht
    have hub : (a u).toNNReal < b :=
      (Real.toNNReal_le_toNNReal (hm.monotoneOn hu ht hut)).trans_lt htb
    apply capacityCut_eq_of_local_inverse s u p hub
    intro q hqb
    have hqL := (ENNReal.coe_le_coe.mpr hqb.le).trans_lt hb
    obtain ⟨v, ⟨hv, hav⟩, _⟩ := existsUnique_time_of_lt_clockSup ha0 hm hc hqL
    have hcap := (hread v hv (by simpa only [hav, Real.toNNReal_coe] using hqb)).2
    rw [hav, Real.toNNReal_coe] at hcap
    rw [hcap]
    constructor
    · intro huv
      have h := hm hu hv (NNReal.coe_lt_coe.mp huv)
      rw [hav] at h
      apply NNReal.coe_lt_coe.mp
      rwa [Real.coe_toNNReal _ (hn u hu)]
    · intro hq
      have h := NNReal.coe_lt_coe.mpr hq
      rw [Real.coe_toNNReal _ (hn u hu), ← hav] at h
      exact NNReal.coe_lt_coe.mpr ((hm.lt_iff_lt hu hv).mp h)
  have hHull : ∀ u ≤ t, physicalHullRead s u p = fwdHull (Ito.rpath w) u := by
    intro u hut
    have hu : (u : ℝ≥0∞) < S := (ENNReal.coe_le_coe.mpr hut).trans_lt ht
    unfold physicalHullRead
    rw [hcut u hut, ENNReal.toNNReal_coe]
    exact (hread u hu
      ((Real.toNNReal_le_toNNReal (hm.monotoneOn hu ht hut)).trans_lt htb)).1
  apply physicalRecordRead_eq_cfRec s t p hw hw0 (ht.trans_le hST)
  obtain ⟨w', _, c, htc, hw', hw'0, _, hew, _⟩ :=
    RootF14.exists_complete_prefix_model hγ hw hw0 (ht.trans_le hST)
  intro u hut
  have huc : u < c := hut.trans_lt htc
  have he : physicalDriverRead s u p = Ito.rpath w' u := by
    apply hullDriverRead_eq_of_prefix (hw'.comp continuous_real_toNNReal)
      (by simpa only [Function.comp_def, Real.toNNReal_zero] using hw'0)
    intro v hvu
    exact (hHull v (hvu.trans hut)).trans
      (RootF14.fwdHull_eq_of_prefix_eq hew (hvu.trans_lt huc)).symm
  exact he.trans (by simpa only [Ito.rpath, Real.toNNReal_coe] using hew ⟨zero_le, huc.le⟩)

end InteractingSLE.Theorem14.GW2JDetR6
