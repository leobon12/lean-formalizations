/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift
import InteractingSLE.Spec.Supplement.GB6RestartProofData
import InteractingSLE.Spec.Supplement.GW2GmBack
import InteractingSLE.Spec.Supplement.GW2RuStep

/-!
# The near structure (N3), step G: an interior tip puts both junctions strictly off the tip

Packet PROVE-GW2-SDE (round 18). The near clauses of (N3) ask the junctions of a stage word strictly off the tip
(`junctionL < 0 < junctionR`). A junction at the tip means the tip is on the real line, so an interior tip excludes it
(GB6's `baseR_pos_of_tip`, `baseL_neg_of_tip`). Deterministic:

* **`junctions_strict_of_trace`**: for a global Loewner trace with `η t ∈ ℍ`, `markPosL W t 0 < 0 < markPos W t 0`;
* **`junctions_strict_shift`**: the same for the shifted driver `W(a + ·) − W(a)` at `u` when `η(a + u)` is an interior
  point of `ℍ \ K_a` (GEOM2's `Gm.notMem_diff_of_shiftTip_notMem_H`);
* `markPos_zero_congr`: the junctions read the driver only on `[0, T]`;
* **`junctions_strict_recOf`**: a record `recOf b (R, ⊤)` whose driver generates a trace up to `b` with tip in `ℍ`;
* **`junctions_strict_stgRec`**: a stage piece `recOf (b − a) (R(a + ·) − R(a), ⊤)` whose tip `α b` is an interior
  point of `ℍ \ K_a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist.StagedLaw Supp8.GB6

/-- **An interior tip puts both junctions strictly off the tip.** -/
theorem junctions_strict_of_trace {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {t : ℝ} (ht : 0 ≤ t) (hH : η t ∈ H) :
    markPosL W t 0 < 0 ∧ 0 < markPos W t 0 := by
  have hB := hη.hasBdryLimits hW hW0 ht
  have htip := hη.tendsto_fwdMapInv_tip hW hW0 ht
  rw [markPosL_zero_eq_baseL hW hW0 ht, markPos_zero_eq_baseR hW hW0 ht]
  exact ⟨baseL_neg_of_tip hW hW0 ht hB hH htip, baseR_pos_of_tip hW hW0 ht hB hH htip⟩

/-- **A shifted tip over an interior point of `ℍ \ K_a` puts both junctions of the shifted driver off the tip.** -/
theorem junctions_strict_shift {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (hmem : η (a + u) ∈ H \ fwdHull W a) :
    markPosL (shiftDrive W a) u 0 < 0 ∧ 0 < markPos (shiftDrive W a) u 0 := by
  obtain ⟨hψ, -⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 ha
  have hHtip : loewnerTip (shiftDrive W a) u ∈ H := by
    by_contra h
    exact GW2TipSystem.Gm.notMem_diff_of_shiftTip_notMem_H hη hW hW0 ha hu h hmem
  exact junctions_strict_of_trace (QuantumZipper.RS.continuous_shiftDrive hW a)
    (QuantumZipper.RS.shiftDrive_zero W a) hψ hu hHtip

/-- **The junctions read the driver only on `[0, T]`.** -/
theorem markPos_zero_congr {w w' : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hw' : Continuous w')
    (hw'0 : w' 0 = 0) {T : ℝ} (hT : 0 ≤ T) (h : ∀ r ∈ Icc (0 : ℝ) T, w r = w' r) :
    markPosL w T 0 = markPosL w' T 0 ∧ markPos w T 0 = markPos w' T 0 := by
  rw [markPosL_zero_eq_baseL hw hw0 hT, markPosL_zero_eq_baseL hw' hw'0 hT, markPos_zero_eq_baseR hw hw0 hT,
    markPos_zero_eq_baseR hw' hw'0 hT]
  exact ⟨baseL_congr hw' hT h, baseR_congr hw' hT h⟩

/-- The record driver read through `toNNReal` is the record driver. -/
theorem rdrv_toNNReal (p : RecData) : (fun r : ℝ => rdrv p (r.toNNReal : ℝ)) = rdrv p := by
  funext r
  simp only [rdrv, Real.toNNReal_coe]

/-- **The frozen record of a driver generating a trace up to `b` has a global trace agreeing up to `b`.** -/
theorem exists_trace_recOf {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {b : ℝ≥0} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace R b α) :
    ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun x : ℝ≥0 => rdrv (recOf (b : ℝ≥0∞) (R, ⊤)) x) ⊤ η' ∧
      ∀ u ≤ b, η' u = α u := by
  have he := GW2TipSystem.Gm.isRegularDriver_top hR hR0
  have hmin : min (b : ℝ≥0∞) ((R, (⊤ : ℝ≥0∞)) : (ℝ≥0 → ℝ) × ℝ≥0∞).2 = b := min_top_right _
  have hfin : min (b : ℝ≥0∞) ((R, (⊤ : ℝ≥0∞)) : (ℝ≥0 → ℝ) × ℝ≥0∞).2 ≠ ⊤ := by
    rw [hmin]; exact ENNReal.coe_ne_top
  have hη : IsGeneratingTrace (R, (⊤ : ℝ≥0∞)).1 (min (b : ℝ≥0∞) (R, (⊤ : ℝ≥0∞)).2) α := by
    rw [hmin]; exact hα
  obtain ⟨η', hη', hηη'⟩ := GW2TipSystem.Gm.exists_isGeneratingTrace_rdrv_recOf he hfin
    hR.continuousOn hη
  refine ⟨η', hη', fun u hu => hηη' u ?_⟩
  rw [hmin, ENNReal.toNNReal_coe]
  exact hu

/-- The frozen record driver is the driver up to `b`. -/
theorem rdrv_recOf_top_eq {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {b u : ℝ≥0} (hu : u ≤ b) :
    rdrv (recOf (b : ℝ≥0∞) (R, ⊤)) u = R u := by
  have he := GW2TipSystem.Gm.isRegularDriver_top hR hR0
  have hfin : min (b : ℝ≥0∞) ((R, (⊤ : ℝ≥0∞)) : (ℝ≥0 → ℝ) × ℝ≥0∞).2 ≠ ⊤ := by
    rw [min_top_right]; exact ENNReal.coe_ne_top
  rw [GW2TipSystem.Gm.rdrv_recOf_eq he hfin hR.continuousOn u]
  simp only [min_top_right, ENNReal.toNNReal_coe, min_eq_left hu]

/-- **A record of a driver generating a trace up to `b`, with tip in `ℍ`, has both junctions off the tip.** -/
theorem junctions_strict_recOf {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {b : ℝ≥0} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace R b α) (hH : α b ∈ H) :
    markPosL (rdrv (recOf (b : ℝ≥0∞) (R, ⊤))) (rtime (recOf (b : ℝ≥0∞) (R, ⊤))) 0 < 0 ∧
      0 < markPos (rdrv (recOf (b : ℝ≥0∞) (R, ⊤))) (rtime (recOf (b : ℝ≥0∞) (R, ⊤))) 0 := by
  set p := recOf (b : ℝ≥0∞) (R, ⊤) with hp
  obtain ⟨η', hη', hηη'⟩ := exists_trace_recOf hR hR0 hα
  have hL := isLoewnerTrace_of_isGeneratingTrace hη'
  rw [rdrv_toNNReal p] at hL
  have ht : rtime p = (b : ℝ) := by
    rw [hp, rtime_recOf_coe, min_top_right, ENNReal.toNNReal_coe]
  rw [ht]
  refine junctions_strict_of_trace (continuous_rdrv p) (rdrv_zero p) hL b.coe_nonneg ?_
  simp only [Real.toNNReal_coe]
  rw [hηη' b le_rfl]
  exact hH

/-- **A stage piece whose tip is an interior point of `ℍ \ K_a` has both junctions off the tip.** -/
theorem junctions_strict_stgRec {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {a b : ℝ≥0} (hab : a < b)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace R b α) (hmem : α b ∈ H \ fwdHull (fun r : ℝ => R r.toNNReal) a) :
    markPosL (rdrv (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤)))
        (rtime (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤))) 0 < 0 ∧
      0 < markPos (rdrv (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤)))
        (rtime (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤))) 0 := by
  set p := recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤) with hp
  set q := recOf (b : ℝ≥0∞) (R, ⊤) with hq
  obtain ⟨η', hη', hηη'⟩ := exists_trace_recOf hR hR0 hα
  have hL := isLoewnerTrace_of_isGeneratingTrace hη'
  rw [rdrv_toNNReal q] at hL
  have hqc := continuous_rdrv q
  have hq0 := rdrv_zero q
  have hab' : (a : ℝ) < b := hab
  -- the frozen driver is `R` on `[0, b]`
  have hqR : ∀ r ∈ Icc (0 : ℝ) b, rdrv q r = R r.toNNReal := fun r hr => by
    rw [← rdrv_toNNReal q]
    exact rdrv_recOf_top_eq hR hR0 (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hK : fwdHull (rdrv q) a = fwdHull (fun r : ℝ => R r.toNNReal) a :=
    fwdHull_eq_of_eqOn a.coe_nonneg hab' hqR
  have hba : ((a : ℝ) + ((b - a : ℝ≥0) : ℝ)) = b := by
    rw [NNReal.coe_sub hab.le]; ring
  have hmem' : (fun r : ℝ => η' r.toNNReal) ((a : ℝ) + ((b - a : ℝ≥0) : ℝ)) ∈ H \ fwdHull (rdrv q) a := by
    rw [hba, hK]
    simp only [Real.toNNReal_coe]
    rw [hηη' b le_rfl]
    exact hmem
  have hsh := junctions_strict_shift hqc hq0 hL a.coe_nonneg (b - a).coe_nonneg hmem'
  have ht : rtime p = ((b - a : ℝ≥0) : ℝ) := by
    rw [hp, rtime_recOf_coe, min_top_right, ENNReal.toNNReal_coe]
  rw [ht]
  -- the piece driver is the shifted frozen driver on `[0, b − a]`
  have hsc : Continuous (shiftDrive (rdrv q) a) := QuantumZipper.RS.continuous_shiftDrive hqc a
  have hagree : ∀ r ∈ Icc (0 : ℝ) ((b - a : ℝ≥0) : ℝ), rdrv p r = shiftDrive (rdrv q) a r := by
    intro r hr
    have hr' : r.toNNReal ≤ b - a := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hpe : rdrv p r = GW2Rd.stgDrv R a r.toNNReal := by
      rw [show rdrv p r = rdrv p (r.toNNReal : ℝ) from (congrFun (rdrv_toNNReal p) r).symm]
      have he := GW2TipSystem.Gm.isRegularDriver_top (GW2Rd.continuous_stgDrv hR a) (GW2Rd.stgDrv_zero R a)
      have hfin : min ((b - a : ℝ≥0) : ℝ≥0∞) ((fun u => GW2Rd.stgDrv R a u, (⊤ : ℝ≥0∞)) :
          (ℝ≥0 → ℝ) × ℝ≥0∞).2 ≠ ⊤ := by
        rw [min_top_right]; exact ENNReal.coe_ne_top
      rw [GW2TipSystem.Gm.rdrv_recOf_eq he hfin (GW2Rd.continuous_stgDrv hR a).continuousOn]
      simp only [min_top_right, ENNReal.toNNReal_coe, min_eq_left hr']
    have hle : a + r.toNNReal ≤ b := by
      have := add_le_add_right hr' a
      rwa [add_tsub_cancel_of_le hab.le] at this
    have hab2 : (a : ℝ) + r ≤ b := by
      have := NNReal.coe_le_coe.2 hle
      push_cast at this
      rwa [Real.coe_toNNReal r hr.1] at this
    have e1 : ((a : ℝ) + r).toNNReal = a + r.toNNReal := by
      rw [Real.toNNReal_add a.coe_nonneg hr.1, Real.toNNReal_coe]
    rw [hpe]
    simp only [GW2Rd.stgDrv, QuantumZipper.RS.shiftDrive]
    rw [hqR _ ⟨add_nonneg a.coe_nonneg hr.1, hab2⟩, hqR _ ⟨a.coe_nonneg, hab'.le⟩, e1, Real.toNNReal_coe]
  obtain ⟨hL', hR'⟩ := markPos_zero_congr (continuous_rdrv p) (rdrv_zero p) hsc
    (QuantumZipper.RS.shiftDrive_zero _ a) (b - a).coe_nonneg hagree
  rw [hL', hR']
  exact hsh

end InteractingSLE.Theorem14.GW2Sds
