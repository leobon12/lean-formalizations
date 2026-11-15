/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SkFilt
import InteractingSLE.Spec.Supplement.GB6LineL4

/-!
# GW2's stage identity: the stage safe events are physical

Packet PROVE-GW2-RELDET, ruling R106. The line data of `GW2Rd.hasRelSafe_of_lines_rec` at a stage include the safe
events `hSψ`, `hSb`: `{a(t) < V ∧ D ∩ K_{a(t)} = ∅}` for the stage clock, the stage stop and the stage relative
driver, with `D` a test support or a finite union of closed balls, must lie in the stage filtration
(`physFilt (T + t)`). This is GB6's `Supp8.GB6LineL.hasGB6SafeMeas_of` at the stage:

* the first conjunct is `{m(T+t) < V}` (GB6's line clock at `T + t`), or the stage start is `⊤`. GB6's own safe
  event with the empty set gives `{m(T+t) < V}`;
* the stage driver frozen at the stage clock, `u ↦ R(S + min(u, a)) − R(S)`, reads `R` only at random times below
  `m(T + t)`, so each value is physical (`Supp8.GB6LineL.measurable_apply_randTime`). The stage hull at `a` is the
  hull of
  this frozen driver, whose avoidance of `D` is physical (`Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand`).

**`measurableSet_stgSafe`** (every closed `D`); **`hasStgSafeMeas`**: the two forms `hSψ`, `hSb` exactly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull drive)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.RelSafeS

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

omit mΩ in
include hGT in
/-- The stage start plus the frozen stage time is below the line clock at `T + t`. -/
theorem coe_stgStart_add_min_le (T t u : ℝ≥0) (ω : Ω) :
    ((stgStart s W Wα ζα GT V T ω + min u (stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
      min (physClock s W Wα ζα GT (T + t) ω) (V ω) := by
  have hle := stgStartM_le hGT (V := V) T t ω
  set M := min (physClock s W Wα ζα GT (T + t) ω) (V ω) with hM
  by_cases htop : stgStartM s W Wα ζα GT V T ω = ⊤
  · rw [htop, top_le_iff] at hle
    rw [hle]
    exact le_top
  · have hS : ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartM s W Wα ζα GT V T ω :=
      ENNReal.coe_toNNReal htop
    rw [ENNReal.coe_add, hS]
    by_cases hMt : M = ⊤
    · rw [hMt]
      exact le_top
    · have hc : ((stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ≥0∞) = stgClock s W Wα ζα GT V T t ω :=
        ENNReal.coe_toNNReal (ne_top_of_le_ne_top hMt tsub_le_self)
      calc stgStartM s W Wα ζα GT V T ω + (min u (stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ≥0)
          ≤ stgStartM s W Wα ζα GT V T ω + (stgClock s W Wα ζα GT V T t ω).toNNReal := by
            gcongr
            exact_mod_cast min_le_right _ _
        _ = M := by rw [hc]; exact add_tsub_cancel_of_le hle

variable (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r))

include hGT in
/-- **The stage safe events are physical**, for every closed set. -/
theorem measurableSet_stgSafe (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T t : ℝ≥0) {D : Set ℂ} (hD : IsClosed D) :
    MeasurableSet[shiftFilt (physFilt hrec hWm P) T t]
      {ω | stgClock s W Wα ζα GT V T t ω < V ω - stgStart s W Wα ζα GT V T ω ∧
        Disjoint D (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) r.toNNReal)
          (stgClock s W Wα ζα GT V T t ω).toNNReal)} := by
  have hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT :=
    measurableSet_goodSet_physFilt hrec hWm hGTm hGTae
  have hv := hver.1
  have hTt : physFilt hrec hWm P T ≤ physFilt hrec hWm P (T + t) := (physFilt hrec hWm P).mono le_self_add
  have hSM : Measurable[physFilt hrec hWm P (T + t)] (stgStartM s W Wα ζα GT V T) :=
    (measurable_stgStartM hGT hrec hWm hGTp hver T).mono hTt le_rfl
  have hS : Measurable[physFilt hrec hWm P (T + t)] (stgStart s W Wα ζα GT V T) :=
    ENNReal.measurable_toNNReal.comp hSM
  have ha : Measurable[physFilt hrec hWm P (T + t)] fun ω => (stgClock s W Wα ζα GT V T t ω).toNNReal :=
    ENNReal.measurable_toNNReal.comp (measurable_stgClock hGT hrec hWm hGTp hver T t)
  -- the first conjunct: GB6's line safe event with the empty set
  have hlt : MeasurableSet[physFilt hrec hWm P (T + t)]
      {ω | min (physClock s W Wα ζα GT (T + t) ω) (V ω) < V ω} := by
    have h := (Supp8.GB6LineL.hasGB6SafeMeas_of hGT hrec hWm hGTm hGTae hver).2 ∅ (T + t)
    have e : Coupling.ballsK (∅ : Finset (ℚ × ℚ × ℚ)) = ∅ := by
      simp only [Coupling.ballsK, Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    simp only [e, Set.empty_disjoint, and_true] at h
    exact h
  -- the frozen stage driver
  set Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    R (stgStart s W Wα ζα GT V T ω + min u (stgClock s W Wα ζα GT V T t ω).toNNReal) ω -
      R (stgStart s W Wα ζα GT V T ω) ω with hZdef
  have hRa : ∀ (d : ℝ≥0) {B : Set ℝ}, MeasurableSet B → MeasurableSet[physFilt hrec hWm P (T + t)]
      ({ω | (d : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT (T + t) ω) (V ω)} ∩ R d ⁻¹' B) := fun d _ hB =>
    measurableSet_le_min_inter_drv hGT hrec hWm hGTp hver (T + t) le_rfl hB
  have hZm : ∀ u, Measurable[physFilt hrec hWm P (T + t)] (Z u) := fun u => by
    refine Measurable.sub ?_ ?_
    · exact Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P (T + t)) hv.2.1
        (hS.add (measurable_const.min ha)) (fun ω => coe_stgStart_add_min_le hGT T t u ω) hRa
    · refine Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P (T + t)) hv.2.1 hS (fun ω => ?_) hRa
      exact (ENNReal.coe_le_coe.2 le_self_add).trans (coe_stgStart_add_min_le hGT T t 0 ω)
  have hZc : ∀ ω, Continuous fun u => Z u ω := fun ω =>
    ((hv.2.1 ω).comp (continuous_const.add (continuous_id.min continuous_const))).sub continuous_const
  have hDis : MeasurableSet[physFilt hrec hWm P (T + t)]
      {ω | Disjoint D (fwdHull (drive 1 Z ω) ((stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ))} :=
    Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hZc hZm (measurable_coe_nnreal_real.comp ha)
      (fun ω => NNReal.coe_nonneg _) hD
  -- the stage hull is the hull of the frozen driver
  have hhull : ∀ ω, fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) r.toNNReal)
      ((stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ) =
      fwdHull (drive 1 Z ω) ((stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ) := fun ω => by
    refine LocalExt.fwdHull_congr_of_continuousOn
      ((continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal).continuousOn
      (QuantumZipper.NonSwallow.continuous_drive_ns hZc 1 ω).continuousOn (NNReal.coe_nonneg _) (lt_add_one _) ?_
    intro r hr
    simp only [drive, Real.sqrt_one, one_mul, hZdef, stgDrv]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  -- the first conjunct
  have hfirst : ∀ ω, stgClock s W Wα ζα GT V T t ω < V ω - stgStart s W Wα ζα GT V T ω ↔
      (stgStartM s W Wα ζα GT V T ω = ⊤ ∨ min (physClock s W Wα ζα GT (T + t) ω) (V ω) < V ω) := fun ω => by
    have hle := stgStartM_le hGT (V := V) T t ω
    by_cases htop : stgStartM s W Wα ζα GT V T ω = ⊤
    · have hV : V ω = ⊤ := top_le_iff.1 (htop ▸ min_le_right _ _)
      have hM : min (physClock s W Wα ζα GT (T + t) ω) (V ω) = ⊤ := top_le_iff.1 (htop ▸ hle)
      have h0 : stgClock s W Wα ζα GT V T t ω = 0 := by
        unfold stgClock
        rw [hM, htop, tsub_self]
      have h1 : V ω - stgStart s W Wα ζα GT V T ω = ⊤ := by
        rw [hV]
        exact ENNReal.top_sub_coe
      rw [h0, h1]
      simp only [htop, true_or, iff_true]
      exact ENNReal.zero_lt_top
    · have hS : ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartM s W Wα ζα GT V T ω :=
        ENNReal.coe_toNNReal htop
      rw [hS]
      simp only [htop, false_or, stgClock]
      constructor
      · intro h
        by_contra hc
        exact (not_le.2 h) (tsub_le_tsub_right (le_of_not_gt hc) _)
      · intro h
        exact ((ENNReal.cancel_of_ne htop).tsub_lt_tsub_iff_right hle).2 h
  have hTop : MeasurableSet[physFilt hrec hWm P (T + t)] {ω | stgStartM s W Wα ζα GT V T ω = ⊤} :=
    hSM (measurableSet_singleton ⊤)
  have e : {ω | stgClock s W Wα ζα GT V T t ω < V ω - stgStart s W Wα ζα GT V T ω ∧
        Disjoint D (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) r.toNNReal)
          (stgClock s W Wα ζα GT V T t ω).toNNReal)} =
      ({ω | stgStartM s W Wα ζα GT V T ω = ⊤} ∪ {ω | min (physClock s W Wα ζα GT (T + t) ω) (V ω) < V ω}) ∩
        {ω | Disjoint D (fwdHull (drive 1 Z ω) ((stgClock s W Wα ζα GT V T t ω).toNNReal : ℝ))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_union, hfirst, hhull]
  rw [shiftFilt_apply, e]
  exact (hTop.union hlt).inter hDis

include hGT in
/-- **The stage safe events `hSψ`, `hSb`** of `GW2Rd.hasRelSafe_of_lines_rec`. -/
theorem hasStgSafeMeas (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0) :
    (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[shiftFilt (physFilt hrec hWm P) T t]
      {ω | stgClock s W Wα ζα GT V T t ω < V ω - stgStart s W Wα ζα GT V T ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) r.toNNReal)
          (stgClock s W Wα ζα GT V T t ω).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[shiftFilt (physFilt hrec hWm P) T t]
      {ω | stgClock s W Wα ζα GT V T t ω < V ω - stgStart s W Wα ζα GT V T ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) r.toNNReal)
          (stgClock s W Wα ζα GT V T t ω).toNNReal)} :=
  ⟨fun ψ t => measurableSet_stgSafe hGT hrec hWm hGTm hGTae hver T t (isClosed_tsupport ψ),
    fun Fb t => measurableSet_stgSafe hGT hrec hWm hGTm hGTae hver T t (Coupling.isCompact_ballsK Fb).isClosed⟩

end Safe

end InteractingSLE.Theorem14.GW2Rd
