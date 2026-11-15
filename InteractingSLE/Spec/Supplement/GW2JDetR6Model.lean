/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Stop

/-! # Physical record reconstruction for a driver with the correct inverse hulls -/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR6

open Restart Exist.StagedLaw Supp8.GB6 GW2JDetR3 GW2JDetR4 GW2TipSystem

/-- A continuous candidate's inverse hulls determine physical records through
the concrete capacity stop. No relative driver witness is selected. -/
theorem inverseRecord_capacityStop_of_inverse_hulls
    (s : ℝ≥0) (r : RecData) {a : ℝ≥0 → ℝ} {S T : ℝ≥0∞}
    (ha0 : a 0 = 0) (hm : StrictMonoOn a {u | (u : ℝ≥0∞) < S})
    (hc : ContinuousOn a {u | (u : ℝ≥0∞) < S})
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hec : ContinuousOn e.1 {u | (u : ℝ≥0∞) < e.2}) (he0 : e.1 0 = 0)
    {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hST : S ≤ T)
    (hlife : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S → ((a u).toNNReal : ℝ≥0∞) < e.2)
    (hinv : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S →
      relInv (rdrv r) s '' fwdHull (Ito.rpath e.1) (a u) = fwdHull (Ito.rpath w) u)
    {t d : ℝ≥0} (htd : t < d) (hd : (d : ℝ≥0∞) < S) :
    inverseRecord s t (r, (e.1, physicalCapacityStop s (d : ℝ≥0∞) r e)) =
      cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  let L := ⨆ (u : ℝ≥0) (_ : (u : ℝ≥0∞) < S), ((a u).toNNReal : ℝ≥0∞)
  have hn : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S → 0 ≤ a u := by
    intro u hu
    have h := hm.monotoneOn (bot_le.trans_lt hu) hu (zero_le : (0 : ℝ≥0) ≤ u)
    simpa only [ha0] using h
  have hL : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S → ((a u).toNNReal : ℝ≥0∞) < L := by
    intro u hu
    obtain ⟨v, huv, hv⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hu
    have huv' : u < v := ENNReal.coe_lt_coe.mp huv
    have ha := hm hu hv huv'
    have hnn : (a u).toNNReal < (a v).toNNReal := by
      apply NNReal.coe_lt_coe.mp
      simpa only [Real.coe_toNNReal _ (hn u hu), Real.coe_toNNReal _ (hn v hv)] using ha
    exact (ENNReal.coe_lt_coe.mpr hnn).trans_le
      ((le_iSup_of_le v (le_iSup_of_le hv le_rfl)))
  have hqLife : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < L →
      ((q : ℝ≥0) : ℝ≥0∞) < e.2 := by
    intro q hq
    obtain ⟨u, ⟨hu, hau⟩, _⟩ := existsUnique_time_of_lt_clockSup ha0 hm hc hq
    simpa only [hau, Real.toNNReal_coe] using hlife u hu
  have hcap : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < L →
      ∃ u : ℝ≥0, (u : ℝ≥0∞) < S ∧ a u = (q : ℝ≥0) ∧
        prefixCapacity s q r (killedCode e) = (u : ℝ≥0∞) := by
    intro q hq
    obtain ⟨u, ⟨hu, hau⟩, _⟩ := existsUnique_time_of_lt_clockSup ha0 hm hc hq
    refine ⟨u, hu, hau, ?_⟩
    unfold prefixCapacity
    rw [physicalCapacity_live_prefix s r hec he0 (hqLife q hq) le_rfl
      hγ hw hw0 (hu.trans_le hST) (by simpa only [hau] using hinv u hu),
      ENNReal.ofReal_coe_nnreal]
  have hstop : physicalCapacityStop s (d : ℝ≥0∞) r e = ((a d).toNNReal : ℝ≥0∞) := by
    have ha : IsClockOn a (d : ℝ≥0∞) :=
      ⟨ha0, hm.mono (fun u hu => hu.trans_lt hd), hc.mono (fun u hu => hu.trans_lt hd),
        fun h => (ENNReal.coe_ne_top h).elim⟩
    apply physicalCapacityStop_eq_of_clock_prefix s d r e ha
    intro q hq
    obtain ⟨hu, hau⟩ := ha.invClock_spec hq
    have huS := hu.trans_lt hd
    have hqL : ((q : ℝ≥0) : ℝ≥0∞) < L := by
      simpa only [hau, Real.toNNReal_coe] using hL _ huS
    obtain ⟨v, hv, hav, hcv⟩ := hcap q hqL
    have heq : v = invClock a d q := hm.injOn hv huS (hav.trans hau.symm)
    rwa [heq] at hcv
  rw [hstop]
  let B : ℝ≥0∞ := ((a d).toNNReal : ℝ≥0∞)
  have ht : (t : ℝ≥0∞) < S := (ENNReal.coe_lt_coe.mpr htd).trans hd
  have htB : ((a t).toNNReal : ℝ≥0∞) < B := by
    apply ENNReal.coe_lt_coe.mpr
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal _ (hn t ht), Real.coe_toNNReal _ (hn d hd)]
      using hm ht hd htd
  have hprefix : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < B →
      prefixRecord q (killedCode (e.1, B)) = prefixRecord q (killedCode e) := by
    intro q hq
    apply prefixRecord_congr
    intro v hv
    have hvB := (ENNReal.coe_le_coe.mpr (show (v : ℝ≥0) ≤ (q : ℝ≥0) by
      exact_mod_cast hv)).trans_lt hq
    have hve := hvB.trans (hlife d hd)
    simp only [killedCode, hvB, hve, ↓reduceIte]
  have hcross : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < B →
      ((t : ℝ≥0∞) < prefixCapacity s q r (killedCode (e.1, B)) ↔
        (a t).toNNReal < (q : ℝ≥0)) := by
    intro q hq
    change (t : ℝ≥0∞) < ENNReal.ofReal
      (physicalCapacity s q (r, prefixRecord q (killedCode (e.1, B)))) ↔ _
    rw [hprefix q hq]
    obtain ⟨u, hu, hau, hcu⟩ := hcap q (hq.trans (hL d hd))
    change (t : ℝ≥0∞) < prefixCapacity s q r (killedCode e) ↔ _
    rw [hcu, ENNReal.coe_lt_coe]
    constructor
    · intro htu
      apply NNReal.coe_lt_coe.mp
      simpa only [Real.coe_toNNReal _ (hn t ht), hau] using hm ht hu htu
    · intro hq'
      have h := NNReal.coe_lt_coe.mpr hq'
      rw [Real.coe_toNNReal _ (hn t ht), ← hau] at h
      exact (hm.lt_iff_lt ht hu).mp h
  apply inverseRecord_eq_of_prefix_reads s t r e.1 B (a t).toNNReal htB _ hcross
  intro q hq htq
  rw [hprefix q hq]
  apply physicalRecordRead_eq_of_clockBuffer s _ ha0 hm hc hγ hw hw0 hST
    (hq.trans (hL d hd)) ?_ ht htq
  intro u hu huq
  have hinv' : relInv (rdrv r) s '' fwdHull (Ito.rpath e.1) (a u).toNNReal =
      fwdHull (Ito.rpath w) u := by
    simpa only [Real.coe_toNNReal _ (hn u hu)] using hinv u hu
  exact ⟨(inverseHull_live_prefix s r hec he0 (hqLife q (hq.trans (hL d hd))) huq.le).trans
      hinv',
    physicalCapacity_live_prefix s r hec he0 (hqLife q (hq.trans (hL d hd))) huq.le
      hγ hw hw0 (hu.trans_le hST) hinv'⟩

end InteractingSLE.Theorem14.GW2JDetR6
