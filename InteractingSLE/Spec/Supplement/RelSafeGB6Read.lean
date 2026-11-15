/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeGB6Clock
import InteractingSLE.Spec.Supplement.Q3StopTransfer

/-!
# GB6's relative driver read in the physical history, part 4: the versions are physically adapted

Packet PROVE-GB6-RELSAFE (the shared core, GB6 instance). PROVE-Q3-REL4 §5.1 named the missing proposition: the
versions' relative driver and stop, traced on `{q ≤ a(t)}`, must be events of `σ(record) ∨ σ(W_r, r ≤ t) ∨ 𝒩_P`.
Proved here for every R-form version (`HullId.IsGB6RelVersionR`; the announced versions of `Q3Stop` are such), with
the relative clock `a = min(physClock, V)`:

* **`exists_goodSet`**: a measurable good event `GT`, almost surely equal to the record event, on which `PhysGood`
  holds; `measurableSet_goodSet_physFilt`: it is an event of every `physFilt t`;
* the physical clock is continuous, nondecreasing, `0` at `0` for every sample, and equals `gb6Clock` before the first
  contact (`continuous_physClock`, `monotone_physClock`, `physClock_zero`, `physClock_eq_gb6Clock`);
* **`ae_eq_physDrv_of_isGB6RelVersion`**: a version is the physical relative driver below the clock and the stop;
* **`measurable_min_physClock`**, **`measurableSet_le_min_inter_drv`**, **`measurableSet_le_min_inter_stop`**: the
  stopped clock, the traced driver and the traced stop events are in `physFilt t`;
* **`measurableSet_inter_le_min_of_canonFilt`**: the relative filtration (Q3.2) on the canonical space pulled back
  through `(record, relVar Hc R V)`, traced on `{q ≤ a(t)}`, is in `physFilt t` — exactly the hypothesis `h𝓗'` of
  `Aux79.hasSafeLaw_of_lineKernel` / `BW1Lines.hasSafeLaw_life_of_lineKernel` for GB6.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Supp8.RelSafe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Sec7.Lemma71C Sec7.PocketTraversal

section Good

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

/-- **The good event**: measurable, almost surely the record event, and `PhysGood` on it. -/
theorem exists_goodSet [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (s : ℝ≥0) :
    ∃ GT : Set Ω, (∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) ∧ MeasurableSet GT ∧
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) := by
  have hall : ∀ᵐ ω ∂P,
      (Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
      (Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω} ∧
        IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) ∧
      ((s : ℝ≥0∞) < ζα ω → GB6RecGood s Wα ζα α ω) ∧
      ((s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        Tendsto (QuantumZipper.fwdMapInv (rdrv (gb6Rec s Wα ζα ω)) s) (𝓝[H] 0) (𝓝 (α ω s))) := by
    filter_upwards [hW, ae_driver_zero_continuousOn hfl, hα, ae_gb6RecGood hfl hα s,
      GaugeE.ae_retainedChart_record hκ hκ4 hfl hα s] with ω h1 h2 h3 h4 h5
    exact ⟨h1, ⟨h2.1, h2.2, h3⟩, h4, fun hs hsH => (h5 hs hsH).2⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hall
  have hrec : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  refine ⟨G ∩ gb6Rec s Wα ζα ⁻¹' gb6TS s, fun ω hω => ?_, hGm.inter (hrec (measurableSet_gb6TS s)), ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hG ω hω.1
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff h3).2 hω.2
    exact ⟨h1, h2, hs, hsH, h3 hs, h4 hs hsH⟩
  · filter_upwards [hGae] with ω hω
    exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

/-- The good event is an event of every physical σ-algebra. -/
theorem measurableSet_goodSet_physFilt {GT : Set Ω} {s : ℝ≥0} (hrec : Measurable (gb6Rec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGm : MeasurableSet GT)
    (hGae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) (t : ℝ≥0) :
    MeasurableSet[physFilt hrec hWm P t] GT := by
  refine measurableSet_of_ae_eq ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t) hGm
    (physSigma_le_physFilt hrec hWm P t _ (measurable_rec_physSigma _ W t (measurableSet_gb6TS s))) ?_
  filter_upwards [hGae] with ω hω
  exact propext hω

end Good

section ClockProps

variable {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

include hGT in
theorem physClock_props {ω : Ω} (hω : ω ∈ GT) :
    ContinuousOn (fun t => ENNReal.ofReal (gb6Clock s W Wα ω t)) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      MonotoneOn (fun t => ENNReal.ofReal (gb6Clock s W Wα ω t)) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      ENNReal.ofReal (gb6Clock s W Wα ω 0) = 0 := by
  obtain ⟨⟨hWc, hW0, hγ⟩, ⟨h0, hc, hα⟩, hs, hsH, -⟩ := hGT ω hω
  obtain ⟨ha0, hsm, hac⟩ := relClock_props_of_traces hα hc h0 hs hsH hγ hWc hW0
  refine ⟨ENNReal.continuous_ofReal.comp_continuousOn hac, fun x hx y hy hxy =>
    ENNReal.ofReal_le_ofReal (hsm.monotoneOn hx hy hxy), ?_⟩
  show ENNReal.ofReal (relClock _ _ _ ((0 : ℝ≥0) : ℝ)) = 0
  rw [NNReal.coe_zero, ha0, ENNReal.ofReal_zero]

include hGT in
theorem physClock_zero (ω : Ω) : physClock s W Wα ζα GT 0 ω = 0 := by
  by_cases hω : ω ∈ GT
  · rw [physClock_eq_iSup hGT hω, supBelow_zero]
  · exact physClock_eq_zero_of_notMem hω

include hGT in
theorem monotone_physClock (ω : Ω) : Monotone fun t => physClock s W Wα ζα GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [physClock_eq_iSup hGT hω]
    exact monotone_supBelow
  · simp only [physClock_eq_zero_of_notMem hω]
    exact monotone_const

include hGT in
theorem continuous_physClock (ω : Ω) : Continuous fun t => physClock s W Wα ζα GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [physClock_eq_iSup hGT hω]
    obtain ⟨h1, h2, h3⟩ := physClock_props hGT hω
    exact continuous_supBelow h1 h2 h3
  · simp only [physClock_eq_zero_of_notMem hω]
    exact continuous_const

include hGT in
/-- Before the first contact the physical clock is GB6's relative clock. -/
theorem physClock_eq_gb6Clock {ω : Ω} (hω : ω ∈ GT) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < gb6Tc s γ α ω) :
    physClock s W Wα ζα GT t ω = ENNReal.ofReal (gb6Clock s W Wα ω t) := by
  obtain ⟨h1, h2, h3⟩ := physClock_props hGT hω
  rw [physClock_eq_iSup hGT hω]
  exact supBelow_eq_of_lt h1 h2 h3 ht

end ClockProps

section Version

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

include hGT in
/-- **A version is the physical relative driver** below the physical clock and the stop. -/
theorem ae_eq_physDrv_of_isGB6RelVersion (hver : IsGB6RelVersion s P W Wα ζα γ α R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < physClock s W Wα ζα GT t ω → (u : ℝ≥0∞) ≤ V ω →
      R u ω = physDrv s W Wα ζα GT t u ω := by
  filter_upwards [hver.2.2.2.2.2.2] with ω hω u hu huV
  refine eq_physDrv_of_version hGT (fun hωG => ?_) t u hu huV
  obtain ⟨-, -, hs, hsH, -⟩ := hGT ω hωG
  exact ⟨hver.2.1 ω, hver.2.2.1 ω, (hω hs hsH).2.2⟩

variable (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

theorem measurable_rec_physFilt (t : ℝ≥0) : Measurable[physFilt hrec hWm P t] (gb6Rec s Wα ζα) :=
  (measurable_rec_physSigma _ W t).mono (physSigma_le_physFilt hrec hWm P t) le_rfl

theorem measurable_W_physFilt {r t : ℝ≥0} (hr : r ≤ t) : Measurable[physFilt hrec hWm P t] (W r) :=
  (measurable_physSigma_apply hr).mono (physSigma_le_physFilt hrec hWm P t) le_rfl

include hGT hGTm in
theorem measurable_physClock_physFilt (t : ℝ≥0) :
    Measurable[physFilt hrec hWm P t] (physClock s W Wα ζα GT t) :=
  measurable_physClock hGT (measurable_rec_physFilt hrec hWm t)
    (fun _ hr => measurable_W_physFilt hrec hWm hr) (hGTm t)

include hGT hGTm in
theorem measurable_physDrv_physFilt (t u : ℝ≥0) :
    Measurable[physFilt hrec hWm P t] (physDrv s W Wα ζα GT t u) :=
  measurable_physDrv hGT (measurable_rec_physFilt hrec hWm t)
    (fun _ hr => measurable_W_physFilt hrec hWm hr) (hGTm t) u

include hGT hGTm in
/-- **The relative clock stopped at the version stop is physically adapted.** -/
theorem measurable_min_physClock (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (t : ℝ≥0) :
    Measurable[physFilt hrec hWm P t] fun ω => min (physClock s W Wα ζα GT t ω) (V ω) := by
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  exact measurable_min_stop ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t)
    (measurable_rec_physFilt hrec hWm t) hρm hρ hv.2.2.2.2.1 hVρ
    (measurable_physClock_physFilt hGT hrec hWm hGTm t) (measurable_physDrv_physFilt hGT hrec hWm hGTm t)
    (ae_eq_physDrv_of_isGB6RelVersion hGT hv t)

include hGT hGTm in
/-- **The version's driver, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_drv (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[physFilt hrec hWm P t]
      ({ω | (q : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω)} ∩ R u ⁻¹' B) := by
  have hv := hver.1
  refine measurableSet_le_inter_of_le ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t) hv.1
    hv.2.1 hv.2.2.1 (measurable_min_physClock hGT hrec hWm hGTm hver t)
    (measurable_physDrv_physFilt hGT hrec hWm hGTm t) ?_ huq hB
  filter_upwards [ae_eq_physDrv_of_isGB6RelVersion hGT hv t] with ω hω u hu
  exact hω u (hu.trans_le (min_le_left _ _)) (hu.trans_le (min_le_right _ _)).le

include hGT hGTm in
/-- **The version's stop, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_stop (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) :
    MeasurableSet[physFilt hrec hWm P t]
      ({ω | (q : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω)} ∩ {ω | V ω ≤ u}) := by
  have hver' := hver
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver'
  have hL : MeasurableSet[physFilt hrec hWm P t]
      {ω | (q : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω)} :=
    measurableSet_le measurable_const (measurable_min_physClock hGT hrec hWm hGTm hver t)
  have hreg := ae_eq_leftReg hv.2.1 hv.2.2.1 (ae_eq_physDrv_of_isGB6RelVersion hGT hv t)
  refine measurableSet_inter_stop_le ((physFilt hrec hWm P).le t) (nullSets_le_physFilt hrec hWm P t)
    (measurable_rec_physFilt hrec hWm t) hρm hρ hv.2.2.2.2.1 hVρ
    (measurable_leftReg (measurable_physDrv_physFilt hGT hrec hWm hGTm t)) hL u ?_
  filter_upwards [hreg] with ω hω hωL v hvu hvV
  exact hω v (((ENNReal.coe_le_coe.2 (hvu.trans huq)).trans hωL).trans (min_le_left _ _)) hvV

include hGT hGTm in
/-- **The relative filtration (Q3.2), traced on `{q ≤ a(t)}`, is in the physical filtration** — the hypothesis
`h𝓗'` of `Aux79.hasSafeLaw_of_lineKernel` for GB6's canonical relative space, with the clock
`a(t) = min(physClock t, V)`. -/
theorem measurableSet_inter_le_min_of_canonFilt (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc) (q : ℝ≥0) {D : Set Ω}
    (hD : MeasurableSet[Coupling.filtrationComap Q3Stop.canonFilt
      (hrec.prodMk (measurable_relVar hHc hver.1.1 hver.1.2.2.2.2.1)) q] D) (t : ℝ≥0) :
    MeasurableSet[physFilt hrec hWm P t]
      (D ∩ {ω | (q : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω)}) := by
  rw [inter_comm]
  refine Q3Stop.measurableSet_inter_of_canonFilt _
    (measurableSet_le measurable_const (measurable_min_physClock hGT hrec hWm hGTm hver t))
    (fun A hA => ?_) (fun u hu B hB => ?_) (fun u hu => ?_) hD
  · exact (measurableSet_le measurable_const (measurable_min_physClock hGT hrec hWm hGTm hver t)).inter
      (measurable_rec_physFilt hrec hWm t hA)
  · have e : (fun ω => Q3Stop.canonDrv u (gb6Rec s Wα ζα ω, relVar Hc R V ω)) ⁻¹' B = R u ⁻¹' B := by
      ext ω
      simp only [mem_preimage, Q3Stop.canonDrv, relDrv_relVar (hver.1.2.1 ω) (hver.1.2.2.1 ω)]
    rw [e]
    exact measurableSet_le_min_inter_drv hGT hrec hWm hGTm hver t hu hB
  · exact measurableSet_le_min_inter_stop hGT hrec hWm hGTm hver t hu

end Version

/-! ### The relative clock `a = min(physClock, V)` for K2's lines -/

section LineClock

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

omit mΩ in
include hGT in
theorem continuous_min_physClock (ω : Ω) :
    Continuous fun t => min (physClock s W Wα ζα GT t ω) (V ω) :=
  (continuous_physClock hGT ω).min continuous_const

omit mΩ in
include hGT in
theorem monotone_min_physClock (ω : Ω) :
    Monotone fun t => min (physClock s W Wα ζα GT t ω) (V ω) := fun _ _ hst =>
  min_le_min_right _ (monotone_physClock hGT ω hst)

omit mΩ in
include hGT in
theorem min_physClock_zero (ω : Ω) : min (physClock s W Wα ζα GT 0 ω) (V ω) = 0 := by
  rw [physClock_zero hGT ω, zero_min]

include hGT in
/-- **Below the stop every relative level is reached** (K2's `hreach` for the lines), on every event inside the
record event. -/
theorem reach_min_physClock {R : ℝ≥0 → Ω → ℝ} (hver : IsGB6RelVersion s P W Wα ζα γ α R V)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) {F : Set Ω}
    (hF : ∀ᵐ ω ∂P, ω ∈ F → gb6Rec s Wα ζα ω ∈ gb6TS s) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω) := by
  filter_upwards [hver.2.2.2.2.2.2, hGTae, hF] with ω hω hG hFω hωF hqV
  have hωG : ω ∈ GT := hG.2 (hFω hωF)
  obtain ⟨-, -, hs, hsH, -⟩ := hGT ω hωG
  obtain ⟨t, ht, hqt⟩ := (hω hs hsH).2.1 q hqV
  refine ⟨t, le_min ?_ hqV.le⟩
  rw [physClock_eq_gb6Clock hGT hωG ht, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hqt.le

end LineClock

end InteractingSLE.Supp8.RelSafe
