/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeRead
import InteractingSLE.Spec.Supplement.GB6LineL4

/-!
# BW1's safe events are physical ((L4) for BW1)

Packet PROVE-BW1-SAFELAW. GB6's `GB6LineL4.hasGB6SafeMeas_of` with BW1's physical clock: for a closed set `D`, the
event `{a(t) < V, D ∩ K̃_{a(t)} = ∅}` (`a = min(bClock, V)`, `K̃` the relative hull of the version) agrees almost
surely with an event of the record, of the version's driver frozen at `a(t)` (physical:
`Supp8.GB6LineL.measurable_apply_randTime` with `measurableSet_le_min_inter_drv`) and of `a(t)` (physical:
`measurable_min_bClock`): `V ≤ a(t)` iff the path rule of the frozen driver is `≤ a(t)`, and the hull at `a(t)` only
sees the frozen driver (`GB6LineL.measurableSet_disjoint_fwdHull_rand`). Hence **`bw1SafeMeas`**: both safe-event
inputs `hSψ`, `hSb` of K2's lines.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull tamedZ drive)
open LQGMetric (TestOn)

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.StagedLaw Supp8.GB6 Supp8.RelSafe BW1Ver

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ}
  {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **BW1's safe events are physical**, for every closed set: `{a(t) < V, D ∩ K̃_{a(t)} = ∅} ∈ physFilt t`. -/
theorem measurableSet_safe_bw (hGT : ∀ ω ∈ GT, BGood rec W ω) (hrec : Measurable rec)
    (hWm : ∀ r, Measurable (W r)) (hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)
    (hv : IsBVer P rec W GT R V) (D : Set ℂ) (hD : IsClosed D) (t : ℝ≥0) :
    MeasurableSet[physFilt hrec hWm P t]
      {ω | min (bClock rec W GT t ω) (V ω) < V ω ∧ Disjoint D
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)} := by
  have ha := measurable_min_bClock hGT hrec hWm hGTp hv t
  obtain ⟨ρ, hρm, hρ, hVρ⟩ := hv.rule
  have ha' : Measurable[physFilt hrec hWm P t] fun ω => (min (bClock rec W GT t ω) (V ω)).toNNReal :=
    ENNReal.measurable_toNNReal.comp ha
  -- the version's driver frozen at the clock is physical
  have hY : ∀ u, Measurable[physFilt hrec hWm P t]
      (fun ω => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω) := fun u =>
    Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P t) hv.cont
      (a := fun ω => min (bClock rec W GT t ω) (V ω)) (measurable_const.min ha')
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self)
      (fun d B hB => measurableSet_le_min_inter_drv hGT hrec hWm hGTp hv t le_rfl hB)
  have hYc : ∀ ω, Continuous fun u => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω :=
    fun ω => (hv.cont ω).comp (continuous_id.min continuous_const)
  -- the disjointness event of the frozen driver is physical
  have hDis : MeasurableSet[physFilt hrec hWm P t] {ω | Disjoint D
      (fwdHull (drive 1 (fun u ω => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω) ω)
        ((min (bClock rec W GT t ω) (V ω)).toNNReal : ℝ))} :=
    Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hYc hY (measurable_coe_nnreal_real.comp ha')
      (fun ω => NNReal.coe_nonneg _) hD
  have hhull : ∀ ω, fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal =
      fwdHull (drive 1 (fun u ω => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω) ω)
        ((min (bClock rec W GT t ω) (V ω)).toNNReal : ℝ) := fun ω => by
    refine LocalExt.fwdHull_congr_of_continuousOn ((hv.cont ω).comp continuous_real_toNNReal).continuousOn
      (QuantumZipper.NonSwallow.continuous_drive_ns hYc 1 ω).continuousOn (NNReal.coe_nonneg _) (lt_add_one _) ?_
    intro r hr
    simp only [drive, Real.sqrt_one, one_mul]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  -- the stop: `V ≤ a(t)` iff the path rule of the frozen driver is `≤ a(t)`
  have hrecp := measurable_rec_physFilt' (P := P) hrec hWm t
  have hpath : Measurable[physFilt hrec hWm P t]
      fun ω => fun u => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (physFilt hrec hWm P t) _ _).2 hY
  have hStop : MeasurableSet[physFilt hrec hWm P t] {ω | ρ (rec ω,
      fun u => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω) ≤ min (bClock rec W GT t ω) (V ω)} :=
    measurableSet_le (hρm.comp (hrecp.prodMk hpath)) ha
  have hiff : ∀ᵐ ω ∂P, (min (bClock rec W GT t ω) (V ω) < V ω ↔
      ¬ ρ (rec ω, fun u => R (min u (min (bClock rec W GT t ω) (V ω)).toNNReal) ω) ≤
        min (bClock rec W GT t ω) (V ω)) := by
    filter_upwards [hVρ] with ω hV
    set a := min (bClock rec W GT t ω) (V ω) with hadef
    rw [← not_le]
    refine not_congr ?_
    by_cases htop : a = ⊤
    · rw [htop]
      simp only [le_top]
    · have hcoe : ((a.toNNReal : ℝ≥0) : ℝ≥0∞) = a := ENNReal.coe_toNNReal htop
      constructor
      · intro hVa
        have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (rec ω, fun u => R u ω) →
            R u ω = R (min u a.toNNReal) ω := fun u hu => by
          have h1 : (u : ℝ≥0∞) ≤ ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcoe]
            exact (hu.trans (le_of_eq hV.symm)).trans hVa
          rw [min_eq_left (ENNReal.coe_le_coe.1 h1)]
        rw [hρ _ _ _ hag, ← hV]
        exact hVa
      · intro hρa
        have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (rec ω, fun u => R (min u a.toNNReal) ω) →
            R (min u a.toNNReal) ω = R u ω := fun u hu => by
          have h1 : (u : ℝ≥0∞) ≤ ((a.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [hcoe]
            exact hu.trans hρa
          rw [min_eq_left (ENNReal.coe_le_coe.1 h1)]
        rw [hV, hρ _ _ _ hag]
        exact hρa
  have hEm : MeasurableSet {ω | min (bClock rec W GT t ω) (V ω) < V ω ∧ Disjoint D
      (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)} := by
    have h1 : MeasurableSet {ω | min (bClock rec W GT t ω) (V ω) < V ω} :=
      measurableSet_lt (ha.mono ((physFilt hrec hWm P).le t) le_rfl) hv.measV
    have h2 := (physFilt hrec hWm P).le t _ hDis
    simp only [← hhull] at h2
    exact h1.inter h2
  refine measurableSet_of_ae_eq ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t) hEm
    (hStop.compl.inter hDis) ?_
  filter_upwards [hiff] with ω hω
  show (ω ∈ {ω | _}) = (ω ∈ _ ∩ _)
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, hhull ω, hω]

/-- **(L4) for BW1**: both safe-event inputs of K2's lines (test supports and finite families of rational closed
balls). -/
theorem bw1SafeMeas (hGT : ∀ ω ∈ GT, BGood rec W ω) (hrec : Measurable rec)
    (hWm : ∀ r, Measurable (W r)) (hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)
    (hv : IsBVer P rec W GT R V) :
    (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (bClock rec W GT t ω) (V ω) < V ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (bClock rec W GT t ω) (V ω) < V ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)} :=
  ⟨fun ψ t => measurableSet_safe_bw hGT hrec hWm hGTp hv _ (isClosed_tsupport ψ) t,
    fun Fb t => measurableSet_safe_bw hGT hrec hWm hGTp hv _ (Coupling.isCompact_ballsK Fb).isClosed t⟩

end Safe

end InteractingSLE.Theorem14.BW1Safe
