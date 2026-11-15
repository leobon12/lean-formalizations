/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzPhys


/-!
# GW2 at a root `x`: the versions are physically adapted (decision D8, layer 3, continued)

Packet PROVE-GW2-ROOTX, round 3. GB6's `RelSafeGB6Read` at a root `x`: for every root-`x` R-form version
(`GW2Rz.IsRelVersionXR`) and the relative clock `a = min(physClockX, V)`, the relative driver and stop traced on
`{q ≤ a(t)}` are events of the physical filtration `σ(record) ∨ σ(w_r, r ≤ t) ∨ 𝒩_P` (the same filtration at every
root):

* **`ae_eq_physDrvX_of_isRelVersionX`**; `measurableSet_goodSetX_physFilt`, `measurable_rec_physFiltX`,
  `measurable_w_physFiltX`, `measurable_physClockX_physFilt`, `measurable_physDrvX_physFilt`;
* **`measurable_min_physClockX`**, `measurableSet_le_min_inter_drvX`, `measurableSet_le_min_inter_stopX`,
  **`measurableSet_inter_le_min_of_canonFiltX`** (the hypothesis `h𝓗'` of K2's lines at a root `x`);
* `continuous_min_physClockX`, `monotone_min_physClockX`, `min_physClockX_zero`, **`reach_min_physClockX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.RelDrv GW2TipSystem
open Supp8.RelSafe (physSigma physFilt measurable_rec_physSigma measurable_physSigma_apply physSigma_le_physFilt
  nullSets_le_physFilt measurableSet_of_ae_eq measurable_min_stop measurableSet_le_inter_of_le
  measurableSet_inter_stop_le ae_eq_leftReg measurable_leftReg)

/-! ### A root-`x` version is the physical relative driver -/

section Version

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hs : 0 < s) (hx : 0 ≤ x)

include hGT hs hx in
/-- **A root-`x` version is the root-`x` physical relative driver** below the physical clock and the stop. -/
theorem ae_eq_physDrvX_of_isRelVersionX (hver : IsRelVersionX x s P W' ζ' w γ α R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < physClockX x s W' ζ' w GT t ω → (u : ℝ≥0∞) ≤ V ω →
      R u ω = physDrvX x s W' ζ' w GT t u ω := by
  filter_upwards [hver.2.2.2.2.2.2] with ω hω u hu huV
  refine eq_physDrvX_of_version hGT hs hx (fun hωG => ?_) t u hu huV
  exact ⟨hver.2.1 ω, hver.2.2.1 ω, (hω (hGT ω hωG).2.2.2.2).2.2⟩

variable (hrec : Measurable (cfRec s W' ζ')) (hwm : ∀ r, Measurable (w r))

/-- The good event is an event of every physical σ-algebra. -/
theorem measurableSet_goodSetX_physFilt (hGm : MeasurableSet GT)
    (hGae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s W' ζ' ω ∈ goodX x s) (t : ℝ≥0) :
    MeasurableSet[physFilt hrec hwm P t] GT := by
  refine measurableSet_of_ae_eq ((physFilt hrec hwm P).le t) (nullSets_le_physFilt hrec hwm P t) hGm
    (physSigma_le_physFilt hrec hwm P t _ (measurable_rec_physSigma _ w t (measurableSet_goodX x s))) ?_
  filter_upwards [hGae] with ω hω
  exact propext hω

theorem measurable_rec_physFiltX (t : ℝ≥0) : Measurable[physFilt hrec hwm P t] (cfRec s W' ζ') :=
  (measurable_rec_physSigma _ w t).mono (physSigma_le_physFilt hrec hwm P t) le_rfl

theorem measurable_w_physFiltX {r t : ℝ≥0} (hr : r ≤ t) : Measurable[physFilt hrec hwm P t] (w r) :=
  (measurable_physSigma_apply hr).mono (physSigma_le_physFilt hrec hwm P t) le_rfl

variable (hGTm : ∀ t, MeasurableSet[physFilt hrec hwm P t] GT)

include hGT hGTm in
theorem measurable_physClockX_physFilt (t : ℝ≥0) :
    Measurable[physFilt hrec hwm P t] (physClockX x s W' ζ' w GT t) :=
  measurable_physClockX hGT (measurable_rec_physFiltX hrec hwm t)
    (fun _ hr => measurable_w_physFiltX hrec hwm hr) (hGTm t)

include hGT hGTm in
theorem measurable_physDrvX_physFilt (t u : ℝ≥0) :
    Measurable[physFilt hrec hwm P t] (physDrvX x s W' ζ' w GT t u) :=
  measurable_physDrvX hGT (measurable_rec_physFiltX hrec hwm t)
    (fun _ hr => measurable_w_physFiltX hrec hwm hr) (hGTm t) u

include hGT hs hx hGTm in
/-- **The root-`x` relative clock stopped at the version stop is physically adapted.** -/
theorem measurable_min_physClockX (hver : IsRelVersionXR x s P W' ζ' w γ α R V) (t : ℝ≥0) :
    Measurable[physFilt hrec hwm P t] fun ω => min (physClockX x s W' ζ' w GT t ω) (V ω) := by
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  exact measurable_min_stop ((physFilt hrec hwm P).le t) (nullSets_le_physFilt hrec hwm P t)
    (measurable_rec_physFiltX hrec hwm t) hρm hρ hv.2.2.2.2.1 hVρ
    (measurable_physClockX_physFilt hGT hrec hwm hGTm t) (measurable_physDrvX_physFilt hGT hrec hwm hGTm t)
    (ae_eq_physDrvX_of_isRelVersionX hGT hs hx hv t)

include hGT hs hx hGTm in
/-- **The version's driver, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_drvX (hver : IsRelVersionXR x s P W' ζ' w γ α R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[physFilt hrec hwm P t]
      ({ω | (q : ℝ≥0∞) ≤ min (physClockX x s W' ζ' w GT t ω) (V ω)} ∩ R u ⁻¹' B) := by
  have hv := hver.1
  refine measurableSet_le_inter_of_le ((physFilt hrec hwm P).le t) (nullSets_le_physFilt hrec hwm P t) hv.1
    hv.2.1 hv.2.2.1 (measurable_min_physClockX hGT hs hx hrec hwm hGTm hver t)
    (measurable_physDrvX_physFilt hGT hrec hwm hGTm t) ?_ huq hB
  filter_upwards [ae_eq_physDrvX_of_isRelVersionX hGT hs hx hv t] with ω hω u hu
  exact hω u (hu.trans_le (min_le_left _ _)) (hu.trans_le (min_le_right _ _)).le

include hGT hs hx hGTm in
/-- **The version's stop, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_stopX (hver : IsRelVersionXR x s P W' ζ' w γ α R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) :
    MeasurableSet[physFilt hrec hwm P t]
      ({ω | (q : ℝ≥0∞) ≤ min (physClockX x s W' ζ' w GT t ω) (V ω)} ∩ {ω | V ω ≤ u}) := by
  have hver' := hver
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver'
  have hL : MeasurableSet[physFilt hrec hwm P t]
      {ω | (q : ℝ≥0∞) ≤ min (physClockX x s W' ζ' w GT t ω) (V ω)} :=
    measurableSet_le measurable_const (measurable_min_physClockX hGT hs hx hrec hwm hGTm hver t)
  have hreg := ae_eq_leftReg hv.2.1 hv.2.2.1 (ae_eq_physDrvX_of_isRelVersionX hGT hs hx hv t)
  refine measurableSet_inter_stop_le ((physFilt hrec hwm P).le t) (nullSets_le_physFilt hrec hwm P t)
    (measurable_rec_physFiltX hrec hwm t) hρm hρ hv.2.2.2.2.1 hVρ
    (measurable_leftReg (measurable_physDrvX_physFilt hGT hrec hwm hGTm t)) hL u ?_
  filter_upwards [hreg] with ω hω hωL v hvu hvV
  exact hω v (((ENNReal.coe_le_coe.2 (hvu.trans huq)).trans hωL).trans (min_le_left _ _)) hvV

include hGT hs hx hGTm in
/-- **The relative filtration (Q3.2), traced on `{q ≤ a(t)}`, is in the physical filtration at a root `x`** (the
hypothesis `h𝓗'` of K2's lines, with the root-`x` clock `a(t) = min(physClockX t, V)`). -/
theorem measurableSet_inter_le_min_of_canonFiltX (hver : IsRelVersionXR x s P W' ζ' w γ α R V)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc) (q : ℝ≥0) {D : Set Ω}
    (hD : MeasurableSet[Coupling.filtrationComap Supp8.Q3Stop.canonFilt
      (hrec.prodMk (measurable_relVar hHc hver.1.1 hver.1.2.2.2.2.1)) q] D) (t : ℝ≥0) :
    MeasurableSet[physFilt hrec hwm P t]
      (D ∩ {ω | (q : ℝ≥0∞) ≤ min (physClockX x s W' ζ' w GT t ω) (V ω)}) := by
  rw [inter_comm]
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt _
    (measurableSet_le measurable_const (measurable_min_physClockX hGT hs hx hrec hwm hGTm hver t))
    (fun A hA => ?_) (fun u hu B hB => ?_) (fun u hu => ?_) hD
  · exact (measurableSet_le measurable_const (measurable_min_physClockX hGT hs hx hrec hwm hGTm hver t)).inter
      (measurable_rec_physFiltX hrec hwm t hA)
  · have e : (fun ω => Supp8.Q3Stop.canonDrv u (cfRec s W' ζ' ω, relVar Hc R V ω)) ⁻¹' B = R u ⁻¹' B := by
      ext ω
      simp only [mem_preimage, Supp8.Q3Stop.canonDrv, relDrv_relVar (hver.1.2.1 ω) (hver.1.2.2.1 ω)]
    rw [e]
    exact measurableSet_le_min_inter_drvX hGT hs hx hrec hwm hGTm hver t hu hB
  · exact measurableSet_le_min_inter_stopX hGT hs hx hrec hwm hGTm hver t hu

end Version

/-! ### The relative clock `a = min(physClockX, V)` for K2's lines -/

section LineClock

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hs : 0 < s) (hx : 0 ≤ x)

omit mΩ in
include hGT hs hx in
theorem continuous_min_physClockX (ω : Ω) :
    Continuous fun t => min (physClockX x s W' ζ' w GT t ω) (V ω) :=
  (continuous_physClockX hGT hs hx ω).min continuous_const

omit mΩ in
include hGT hs hx in
theorem monotone_min_physClockX (ω : Ω) :
    Monotone fun t => min (physClockX x s W' ζ' w GT t ω) (V ω) := fun _ _ hst =>
  min_le_min_right _ (monotone_physClockX hGT hs hx ω hst)

omit mΩ in
include hGT hs hx in
theorem min_physClockX_zero (ω : Ω) : min (physClockX x s W' ζ' w GT 0 ω) (V ω) = 0 := by
  rw [physClockX_zero hGT hs hx ω, zero_min]

include hGT hs hx in
/-- **Below the stop every relative level is reached** (K2's `hreach` for the lines), on every event inside the
good records. -/
theorem reach_min_physClockX {R : ℝ≥0 → Ω → ℝ} (hver : IsRelVersionX x s P W' ζ' w γ α R V)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s W' ζ' ω ∈ goodX x s) {F : Set Ω}
    (hF : ∀ᵐ ω ∂P, ω ∈ F → cfRec s W' ζ' ω ∈ goodX x s) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ min (physClockX x s W' ζ' w GT t ω) (V ω) := by
  filter_upwards [hver.2.2.2.2.2.2, hGTae, hF] with ω hω hG hFω hωF hqV
  have hm := hFω hωF
  have hωG : ω ∈ GT := hG.2 hm
  obtain ⟨t, ht, hqt⟩ := (hω hm).2.1 q hqV
  refine ⟨t, le_min ?_ hqV.le⟩
  rw [physClockX_eq_clockX hGT hs hx hωG ht, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hqt.le

end LineClock

end InteractingSLE.Theorem14.GW2Rz
