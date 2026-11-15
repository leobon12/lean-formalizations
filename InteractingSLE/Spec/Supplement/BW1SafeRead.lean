/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeDrv

/-!
# BW1's relative driver read in the physical history, part 3: the versions are physically adapted

Packet PROVE-BW1-SAFELAW. GB6's `RelSafeGB6Read` with the retained time read from the record. For a version in
R-form with hull identities (`IsBVer`: the stop a measurable path rule of (record, path), and almost surely on the
good event GB6's range and hull clauses), with the relative clock `a = min(bClock, V)` and the physical filtration
`RelSafe.physFilt` (record ∨ physical driver up to `t` ∨ null sets):

* **`ae_eq_bDrv_of_isBVer`**: the version is the physical relative driver below the clock and the stop;
* **`measurable_min_bClock`**, `measurableSet_le_min_inter_drv`, `measurableSet_le_min_inter_stop`: the stopped
  clock, the traced driver and the traced stop events are in `physFilt t`;
* **`measurableSet_inter_le_min_of_canonFilt`**: the relative filtration on the canonical space pulled back through
  `(record, relVar Hc R V)`, traced on `{q ≤ a(t)}`, is in `physFilt t` (the hypothesis `h𝓗'` of K2's lines);
* the clock for the lines: continuous, monotone, `0` at `0` for every sample; every level below the stop is reached
  (`reach_min_bClock`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.ReadD Supp8.RelSafe Sec7.Lemma71C Sec7.PocketTraversal
  BW1Ver

/-- **A BW1 relative version in R-form with hull identities, for one index** (the clauses of `IsBW1RelVersion` and
`IsBW1VersionHulls` used for the physical readability, with the physical driver `W` and the good event `GT`). -/
structure IsBVer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ)
    (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop where
  meas : ∀ s, Measurable (R s)
  cont : ∀ ω, Continuous fun s => R s ω
  zero : ∀ ω, R 0 ω = 0
  frozen : ∀ ω (s : ℝ≥0), V ω ≤ s → R s ω = R (V ω).toNNReal ω
  measV : Measurable V
  rule : ∃ ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable ρ ∧ HullId.IsPathRule ρ ∧
    ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω)
  ae : ∀ᵐ ω ∂P, ω ∈ GT → 0 < V ω ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < bTc rec W ω ∧ (u : ℝ) < rclk (rec ω) (W · ω) t) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < bTc rec W ω → ENNReal.ofReal (rclk (rec ω) (W · ω) t) ≤ V ω →
      fwdHull (Ito.rpath (R · ω)) (rclk (rec ω) (W · ω) t) =
        relMap (rdrv (rec ω)) (recS (rec ω)) '' fwdHull (Ito.rpath (W · ω)) t

section Version

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ}
  {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, BGood rec W ω)

include hGT in
/-- **A version is the physical relative driver** below the physical clock and the stop. -/
theorem ae_eq_bDrv_of_isBVer (hv : IsBVer P rec W GT R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < bClock rec W GT t ω → (u : ℝ≥0∞) ≤ V ω →
      R u ω = bDrv rec W GT t u ω := by
  filter_upwards [hv.ae] with ω hω u hu huV
  exact eq_bDrv_of_version hGT (fun hωG => ⟨hv.cont ω, hv.zero ω, (hω hωG).2.2⟩) t u hu huV

variable (hrec : Measurable rec) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

theorem measurable_rec_physFilt' (t : ℝ≥0) : Measurable[physFilt hrec hWm P t] rec :=
  (measurable_rec_physSigma _ W t).mono (physSigma_le_physFilt hrec hWm P t) le_rfl

theorem measurable_W_physFilt' {r t : ℝ≥0} (hr : r ≤ t) : Measurable[physFilt hrec hWm P t] (W r) :=
  (measurable_physSigma_apply hr).mono (physSigma_le_physFilt hrec hWm P t) le_rfl

include hGT hGTm in
theorem measurable_bClock_physFilt (t : ℝ≥0) : Measurable[physFilt hrec hWm P t] (bClock rec W GT t) :=
  measurable_bClock hGT (measurable_rec_physFilt' hrec hWm t) (fun _ hr => measurable_W_physFilt' hrec hWm hr)
    (hGTm t)

include hGT hGTm in
theorem measurable_bDrv_physFilt (t u : ℝ≥0) : Measurable[physFilt hrec hWm P t] (bDrv rec W GT t u) :=
  measurable_bDrv hGT (measurable_rec_physFilt' hrec hWm t) (fun _ hr => measurable_W_physFilt' hrec hWm hr)
    (hGTm t) u

include hGT hGTm in
/-- **The relative clock stopped at the version stop is physically adapted.** -/
theorem measurable_min_bClock (hv : IsBVer P rec W GT R V) (t : ℝ≥0) :
    Measurable[physFilt hrec hWm P t] fun ω => min (bClock rec W GT t ω) (V ω) := by
  obtain ⟨ρ, hρm, hρ, hVρ⟩ := hv.rule
  exact measurable_min_stop ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t)
    (measurable_rec_physFilt' hrec hWm t) hρm hρ hv.measV hVρ
    (measurable_bClock_physFilt hGT hrec hWm hGTm t) (measurable_bDrv_physFilt hGT hrec hWm hGTm t)
    (ae_eq_bDrv_of_isBVer hGT hv t)

include hGT hGTm in
/-- **The version's driver, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_drv (hv : IsBVer P rec W GT R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[physFilt hrec hWm P t]
      ({ω | (q : ℝ≥0∞) ≤ min (bClock rec W GT t ω) (V ω)} ∩ R u ⁻¹' B) := by
  refine measurableSet_le_inter_of_le ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t) hv.meas
    hv.cont hv.zero (measurable_min_bClock hGT hrec hWm hGTm hv t)
    (measurable_bDrv_physFilt hGT hrec hWm hGTm t) ?_ huq hB
  filter_upwards [ae_eq_bDrv_of_isBVer hGT hv t] with ω hω u hu
  exact hω u (hu.trans_le (min_le_left _ _)) (hu.trans_le (min_le_right _ _)).le

include hGT hGTm in
/-- **The version's stop, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_stop (hv : IsBVer P rec W GT R V) (t : ℝ≥0) {u q : ℝ≥0} (huq : u ≤ q) :
    MeasurableSet[physFilt hrec hWm P t]
      ({ω | (q : ℝ≥0∞) ≤ min (bClock rec W GT t ω) (V ω)} ∩ {ω | V ω ≤ u}) := by
  obtain ⟨ρ, hρm, hρ, hVρ⟩ := hv.rule
  have hL : MeasurableSet[physFilt hrec hWm P t] {ω | (q : ℝ≥0∞) ≤ min (bClock rec W GT t ω) (V ω)} :=
    measurableSet_le measurable_const (measurable_min_bClock hGT hrec hWm hGTm hv t)
  have hreg := ae_eq_leftReg hv.cont hv.zero (ae_eq_bDrv_of_isBVer hGT hv t)
  refine measurableSet_inter_stop_le ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t)
    (measurable_rec_physFilt' hrec hWm t) hρm hρ hv.measV hVρ
    (measurable_leftReg (measurable_bDrv_physFilt hGT hrec hWm hGTm t)) hL u ?_
  filter_upwards [hreg] with ω hω hωL v hvu hvV
  exact hω v (((ENNReal.coe_le_coe.2 (hvu.trans huq)).trans hωL).trans (min_le_left _ _)) hvV

include hGT hGTm in
/-- **The relative filtration (Q3.2), traced on `{q ≤ a(t)}`, is in the physical filtration** — the hypothesis
`h𝓗'` of K2's lines for BW1's canonical relative space, with the clock `a(t) = min(bClock t, V)`. -/
theorem measurableSet_inter_le_min_of_canonFilt (hv : IsBVer P rec W GT R V)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc) (q : ℝ≥0) {D : Set Ω}
    (hD : MeasurableSet[Coupling.filtrationComap Supp8.Q3Stop.canonFilt
      (hrec.prodMk (measurable_relVar hHc hv.meas hv.measV)) q] D) (t : ℝ≥0) :
    MeasurableSet[physFilt hrec hWm P t] (D ∩ {ω | (q : ℝ≥0∞) ≤ min (bClock rec W GT t ω) (V ω)}) := by
  rw [inter_comm]
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt _
    (measurableSet_le measurable_const (measurable_min_bClock hGT hrec hWm hGTm hv t))
    (fun A hA => ?_) (fun u hu B hB => ?_) (fun u hu => ?_) hD
  · exact (measurableSet_le measurable_const (measurable_min_bClock hGT hrec hWm hGTm hv t)).inter
      (measurable_rec_physFilt' hrec hWm t hA)
  · have e : (fun ω => Supp8.Q3Stop.canonDrv u (rec ω, relVar Hc R V ω)) ⁻¹' B = R u ⁻¹' B := by
      ext ω
      simp only [mem_preimage, Supp8.Q3Stop.canonDrv, relDrv_relVar (hv.cont ω) (hv.zero ω)]
    rw [e]
    exact measurableSet_le_min_inter_drv hGT hrec hWm hGTm hv t hu hB
  · exact measurableSet_le_min_inter_stop hGT hrec hWm hGTm hv t hu

end Version

/-! ### The relative clock `a = min(bClock, V)` for K2's lines -/

section LineClock

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ}
  {GT : Set Ω} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, BGood rec W ω)

omit mΩ in
include hGT in
theorem continuous_min_bClock (ω : Ω) : Continuous fun t => min (bClock rec W GT t ω) (V ω) :=
  (continuous_bClock hGT ω).min continuous_const

omit mΩ in
include hGT in
theorem monotone_min_bClock (ω : Ω) : Monotone fun t => min (bClock rec W GT t ω) (V ω) := fun _ _ hst =>
  min_le_min_right _ (monotone_bClock hGT ω hst)

omit mΩ in
include hGT in
theorem min_bClock_zero (ω : Ω) : min (bClock rec W GT 0 ω) (V ω) = 0 := by
  rw [bClock_zero hGT ω, zero_min]

include hGT in
/-- **Below the stop every relative level is reached** (K2's `hreach` for the lines), on every event almost surely
inside the good event. -/
theorem reach_min_bClock {R : ℝ≥0 → Ω → ℝ} (hv : IsBVer P rec W GT R V) {F : Set Ω}
    (hF : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ GT) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ min (bClock rec W GT t ω) (V ω) := by
  filter_upwards [hv.ae, hF] with ω hω hFω hωF hqV
  have hωG : ω ∈ GT := hFω hωF
  obtain ⟨t, ht, hqt⟩ := (hω hωG).2.1 q hqV
  refine ⟨t, le_min ?_ hqV.le⟩
  rw [bClock_eq_rclk hGT hωG ht, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hqt.le

end LineClock

end InteractingSLE.Theorem14.BW1Safe
