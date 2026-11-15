/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaPhysical
import Mathlib.Topology.LocallyConstant.Basic

/-! # GW4: physical clock facts for phase continuation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix.Frame

variable {F : Frame} (hF : F.IsOk) {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w)
include hF hw

/-- Positive relative capacity is attained strictly after entry. -/
theorem ent_lt_of_rcap_pos {t : ℝ≥0} (ht : 0 < F.rcap w t) : F.ent w < t := by
  by_contra h
  rw [rcap_eq_zero_of_le hF hw (not_lt.1 h)] at ht
  exact lt_irrefl 0 ht

/-- A finite positive version capacity has an actual physical time, with
exactly that capacity and strictly between entry and exit. -/
theorem exists_physical_time_of_capacity {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    {p : ℝ≥0} (hp : 0 < p) (he : ∃ s, fwdHull (fun r : ℝ => R r.toNNReal) p = F.hullAt w s) :
    ∃ s : ℝ≥0, F.ent w < s ∧ (s : ℝ≥0∞) < F.exit w ∧ (p : ℝ) = F.rcap w s := by
  obtain ⟨s, hs⟩ := he
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hsExit := lt_exit_of_isBounded hF hw (hs ▸ (isHPHull_fwdHull hRR p.coe_nonneg).2.1)
  have hps : (p : ℝ) = F.rcap w s := by
    rw [rcap, Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hRR hRR0 p.coe_nonneg hs]
    ring
  exact ⟨s, ent_lt_of_rcap_pos hF hw (hps ▸ NNReal.coe_pos.2 hp), hsExit, hps⟩

/-- The real-valued relative capacity is continuous before exit. -/
theorem continuousOn_rcap_real : ContinuousOn (F.rcap w) {t | (t : ℝ≥0∞) < F.exit w} := by
  intro t ht
  have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp (continuousOn_rcap hF hw t ht)
  rw [ENNReal.toReal_ofReal (rcap_nonneg hF hw ht)] at h
  exact h.congr' (eventually_nhdsWithin_of_forall fun u hu =>
    ENNReal.toReal_ofReal (rcap_nonneg hF hw hu))

/-- Before exit the relative capacity is monotone as a real number. -/
theorem monotoneOn_rcap_real : MonotoneOn (F.rcap w) {t | (t : ℝ≥0∞) < F.exit w} := by
  intro s hs t ht hst
  exact (ENNReal.ofReal_le_ofReal_iff (rcap_nonneg hF hw ht)).1 (monotoneOn_rcap hF hw hs ht hst)

/-- Strict capacity order forces the same strict physical-time order. -/
theorem lt_of_rcap_lt {s t : ℝ≥0} (hs : (s : ℝ≥0∞) < F.exit w) (ht : (t : ℝ≥0∞) < F.exit w)
    (h : F.rcap w s < F.rcap w t) : s < t := by
  by_contra hst
  exact (not_le_of_gt h) (monotoneOn_rcap_real hF hw ht hs (not_lt.1 hst))

/-- The physical times with positive capacity below a fixed version
lifetime form an interval. -/
theorem ordConnected_phase_times (V : ℝ≥0∞) :
    OrdConnected {t : ℝ≥0 | 0 < F.rcap w t ∧ (t : ℝ≥0∞) < F.exit w ∧
      ENNReal.ofReal (F.rcap w t) < V} := by
  constructor
  intro s hs t ht u hu
  have huExit := (ENNReal.coe_le_coe.2 hu.2).trans_lt ht.2.1
  exact ⟨hs.1.trans_le (monotoneOn_rcap_real hF hw hs.2.1 huExit hu.1), huExit,
    (monotoneOn_rcap hF hw huExit ht.2.1 hu.2).trans_lt ht.2.2⟩

end InteractingSLE.Theorem14.GW4Fix.Frame
