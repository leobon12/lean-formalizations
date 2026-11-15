/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixPhysRead

/-!
# GW4's relative filtration inside the physical filtration: K2's line hypotheses

Packet PROVE-T14-GW4FIX (continuation). The consumer-facing results of PROVE-GB6-RELSAFE (`RelSafeGB6Read`) for GW4,
in a frame `F` with a measurable driver `Wd` (a version of the counterflow driver), a measurable co-null good set `GT`,
the constant record `gw4Rec`, the physical filtration `physFilt` (`Supp8.RelSafe`: the driver up to `t` and the null
sets), and a path-rule version `(R, V)` of the relative traversal (`IsGW4RelVersionR`), with the relative clock
`a(t) = min(physClockG t, V)`:

* **`measurableSet_inter_le_min_of_canonFilt`** — the hypothesis `h𝓗'` of `Aux79.hasSafeLaw_of_lineKernel` /
  `BW1Lines.hasSafeLaw_life_of_lineKernel` for GW4's canonical space `(gw4Rec, relVar Hc R V)`;
* `measurable_min_physClockG` (`haa`), `continuous_min_physClockG` (`hac`), `monotone_min_physClockG` (`ham`),
  `min_physClockG_zero` (`ha0`), **`reach_min_physClockG`** (`hreach`);
* `measurableSet_le_min_inter_drv`, `measurableSet_le_min_inter_stop` (the traced driver and stop events).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GW4Rel Supp8.RelSafe Supp8.GB6.RelDrv

namespace Frame

variable {F : Frame} {Ω : Type*} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} {Wd : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
  (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)

theorem measurable_gw4Rec : Measurable fun _ : Ω => gw4Rec := measurable_const

/-! ### The physical filtration -/

include hGTm hGTae in
theorem measurableSet_goodSet_physFilt (t : ℝ≥0) :
    MeasurableSet[physFilt measurable_gw4Rec hWm ν t] GT := by
  refine measurableSet_of_ae_eq ((physFilt measurable_gw4Rec hWm ν).le t)
    (nullSets_le_physFilt measurable_gw4Rec hWm ν t) hGTm MeasurableSet.univ ?_
  exact ae_eq_univ.2 (ae_iff.1 hGTae)

theorem measurable_W_physFilt {r t : ℝ≥0} (hr : r ≤ t) : Measurable[physFilt measurable_gw4Rec hWm ν t] (Wd r) :=
  (measurable_physSigma_apply hr).mono (physSigma_le_physFilt measurable_gw4Rec hWm ν t) le_rfl

include hF hGT hGTm hGTae in
theorem measurable_physClockG_physFilt (t : ℝ≥0) :
    Measurable[physFilt measurable_gw4Rec hWm ν t] (F.physClockG Wd GT t) :=
  measurable_physClockG hF hGT (fun _ hr => measurable_W_physFilt hWm hr)
    (measurableSet_goodSet_physFilt hWm hGTm hGTae t)

include hF hGT hGTm hGTae in
theorem measurable_physDrvG_physFilt (t u : ℝ≥0) :
    Measurable[physFilt measurable_gw4Rec hWm ν t] (F.physDrvG Wd GT t u) :=
  measurable_physDrvG hF hGT (fun _ hr => measurable_W_physFilt hWm hr)
    (measurableSet_goodSet_physFilt hWm hGTm hGTae t) u

include hF hGT in
/-- **A version is the physical relative driver** below the physical clock and up to its stop. -/
theorem ae_eq_physDrvG (hver : IsGW4RelVersion ν Wd F.c F.C R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂ν, ∀ u : ℝ≥0, (u : ℝ≥0∞) < F.physClockG Wd GT t ω → (u : ℝ≥0∞) ≤ V ω →
      R u ω = F.physDrvG Wd GT t u ω := by
  filter_upwards [hver.2.2.2.2] with ω hω u hu huV
  exact eq_physDrvG_of_version hF hGT (hver.2.1 ω) (hver.2.2.1 ω) hω t u hu huV

/-! ### The relative clock and the traced events -/

include hF hGT hGTm hGTae in
/-- **The relative clock stopped at the version stop is physically adapted.** -/
theorem measurable_min_physClockG (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0) :
    Measurable[physFilt measurable_gw4Rec hWm ν t] fun ω => min (F.physClockG Wd GT t ω) (V ω) := by
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  exact measurable_min_stop ((physFilt measurable_gw4Rec hWm ν).le t)
    (nullSets_le_physFilt measurable_gw4Rec hWm ν t) (measurable_const (a := gw4Rec))
    (ρ := fun x => ρ x.2) (hρm.comp measurable_snd) (fun _ w w' h => hρ w w' h) hv.1.2.2.2.1 hVρ
    (measurable_physClockG_physFilt hF hGT hWm hGTm hGTae t) (measurable_physDrvG_physFilt hF hGT hWm hGTm hGTae t)
    (ae_eq_physDrvG hF hGT hv.1 t)

include hF hGT hGTm hGTae in
/-- **The version's driver, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_drv (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[physFilt measurable_gw4Rec hWm ν t]
      ({ω | (q : ℝ≥0∞) ≤ min (F.physClockG Wd GT t ω) (V ω)} ∩ R u ⁻¹' B) := by
  have hv := hver.1
  refine measurableSet_le_inter_of_le ((physFilt measurable_gw4Rec hWm ν).le t)
    (nullSets_le_physFilt measurable_gw4Rec hWm ν t) hv.1.1 hv.1.2.1 hv.1.2.2.1
    (measurable_min_physClockG hF hGT hWm hGTm hGTae hver t)
    (measurable_physDrvG_physFilt hF hGT hWm hGTm hGTae t) ?_ huq hB
  filter_upwards [ae_eq_physDrvG hF hGT hv.1 t] with ω hω u hu
  exact hω u (hu.trans_le (min_le_left _ _)) (hu.trans_le (min_le_right _ _)).le

include hF hGT hGTm hGTae in
/-- **The version's stop, traced on `{q ≤ a(t)}`, is physically adapted** (`u ≤ q`). -/
theorem measurableSet_le_min_inter_stop (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0)
    {u q : ℝ≥0} (huq : u ≤ q) :
    MeasurableSet[physFilt measurable_gw4Rec hWm ν t]
      ({ω | (q : ℝ≥0∞) ≤ min (F.physClockG Wd GT t ω) (V ω)} ∩ {ω | V ω ≤ u}) := by
  have hver' := hver
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver'
  have hL : MeasurableSet[physFilt measurable_gw4Rec hWm ν t]
      {ω | (q : ℝ≥0∞) ≤ min (F.physClockG Wd GT t ω) (V ω)} :=
    measurableSet_le measurable_const (measurable_min_physClockG hF hGT hWm hGTm hGTae hver t)
  have hreg := ae_eq_leftReg hv.1.2.1 hv.1.2.2.1 (ae_eq_physDrvG hF hGT hv.1 t)
  refine measurableSet_inter_stop_le ((physFilt measurable_gw4Rec hWm ν).le t)
    (nullSets_le_physFilt measurable_gw4Rec hWm ν t) (measurable_const (a := gw4Rec))
    (ρ := fun x => ρ x.2) (hρm.comp measurable_snd) (fun _ w w' h => hρ w w' h) hv.1.2.2.2.1 hVρ
    (measurable_leftReg (measurable_physDrvG_physFilt hF hGT hWm hGTm hGTae t)) hL u ?_
  filter_upwards [hreg] with ω hω hωL v hvu hvV
  exact hω v (((ENNReal.coe_le_coe.2 (hvu.trans huq)).trans hωL).trans (min_le_left _ _)) hvV

include hF hGT hGTm hGTae in
/-- **The relative filtration (Q3.2), traced on `{q ≤ a(t)}`, is in the physical filtration** — the hypothesis
`h𝓗'` of `Aux79.hasSafeLaw_of_lineKernel` for GW4's canonical relative space, with the clock
`a(t) = min(physClockG t, V)`. -/
theorem measurableSet_inter_le_min_of_canonFilt (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc) (q : ℝ≥0) {D : Set Ω}
    (hD : MeasurableSet[Coupling.filtrationComap Supp8.Q3Stop.canonFilt
      ((measurable_const (a := gw4Rec)).prodMk (measurable_relVar hHc hver.1.1.1 hver.1.1.2.2.2.1)) q] D)
    (t : ℝ≥0) :
    MeasurableSet[physFilt measurable_gw4Rec hWm ν t]
      (D ∩ {ω | (q : ℝ≥0∞) ≤ min (F.physClockG Wd GT t ω) (V ω)}) := by
  rw [inter_comm]
  have hL : MeasurableSet[physFilt measurable_gw4Rec hWm ν t]
      {ω | (q : ℝ≥0∞) ≤ min (F.physClockG Wd GT t ω) (V ω)} :=
    measurableSet_le measurable_const (measurable_min_physClockG hF hGT hWm hGTm hGTae hver t)
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt _ hL (fun A hA => ?_) (fun u hu B hB => ?_)
    (fun u hu => ?_) hD
  · exact hL.inter ((measurable_const (a := gw4Rec)) hA)
  · have e : (fun ω => Supp8.Q3Stop.canonDrv u (gw4Rec, relVar Hc R V ω)) ⁻¹' B = R u ⁻¹' B := by
      ext ω
      simp only [mem_preimage, Supp8.Q3Stop.canonDrv, relDrv_relVar (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)]
    rw [e]
    exact measurableSet_le_min_inter_drv hF hGT hWm hGTm hGTae hver t hu hB
  · exact measurableSet_le_min_inter_stop hF hGT hWm hGTm hGTae hver t hu

omit mΩ in
include hF hGT in
theorem continuous_min_physClockG (ω : Ω) : Continuous fun t => min (F.physClockG Wd GT t ω) (V ω) :=
  (continuous_physClockG hF hGT ω).min continuous_const

omit mΩ in
include hF hGT in
theorem monotone_min_physClockG (ω : Ω) : Monotone fun t => min (F.physClockG Wd GT t ω) (V ω) :=
  fun _ _ hst => min_le_min_right _ (monotone_physClockG hF hGT ω hst)

omit mΩ in
include hF hGT in
theorem min_physClockG_zero (ω : Ω) : min (F.physClockG Wd GT 0 ω) (V ω) = 0 := by
  rw [physClockG_zero hF hGT ω, zero_min]

include hF hGT hGTae in
/-- **Below the stop every relative level is reached** (K2's `hreach` for the lines). -/
theorem reach_min_physClockG (hver : IsGW4RelVersion ν Wd F.c F.C R V) (q : ℝ≥0) :
    ∀ᵐ ω ∂ν, (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ min (F.physClockG Wd GT t ω) (V ω) := by
  filter_upwards [hver.2.2.2.2, hGTae] with ω hω hωG hqV
  have hw := hGT ω hωG
  obtain ⟨t₃, ht₃⟩ := hω q hqV
  have hRc : Continuous fun r : ℝ => R r.toNNReal ω := (hver.2.1 ω).comp continuous_real_toNNReal
  have hR0 : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hver.2.2.1 ω]
  have hcap := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hRc hR0 q.coe_nonneg ht₃
  have hb : Bornology.IsBounded (relHullFam F.c F.C (fun u => Wd u ω) t₃) :=
    ht₃ ▸ (isHPHull_fwdHull hRc q.coe_nonneg).2.1
  have hlt := lt_exit_of_isBounded hF hw (t := t₃) hb
  have hrc : F.rcap (fun r => Wd r ω) t₃ = q := by
    simp only [rcap]
    change ConformalImage.hcapSet (relHullFam F.c F.C (fun r => Wd r ω) t₃) / 2 = q
    rw [hcap]
    ring
  refine ⟨t₃ + 1, le_min ?_ hqV.le⟩
  rw [physClockG_eq_supBelow hF hGT hωG]
  refine le_trans ?_ (le_iSup₂_of_le (f := fun (t' : ℝ≥0) (_ : t' < t₃ + 1 ∧ (t' : ℝ≥0∞) < F.exit _) =>
    ENNReal.ofReal (F.rcap (fun r => Wd r ω) t')) t₃ ⟨lt_add_one t₃, hlt⟩ le_rfl)
  rw [hrc, ENNReal.ofReal_coe_nnreal]

end Frame

/-! ### Versions for the given driver are versions for its measurable version -/

theorem IsGW4RelVersion.of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {Wd W' : ℝ≥0 → Ω → ℝ}
    {c : Chart} {C : Set ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (h : IsGW4RelVersion ν W' c C R V)
    (hVW : ∀ᵐ ω ∂ν, ∀ t, Wd t ω = W' t ω) : IsGW4RelVersion ν Wd c C R V := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  filter_upwards [h.2.2.2.2, hVW] with ω hω he
  have e : (fun u => Wd u ω) = fun u => W' u ω := funext he
  rw [e]
  exact hω

theorem IsGW4RelVersionR.of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {Wd W' : ℝ≥0 → Ω → ℝ}
    {c : Chart} {C : Set ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (h : IsGW4RelVersionR ν W' c C R V)
    (hVW : ∀ᵐ ω ∂ν, ∀ t, Wd t ω = W' t ω) : IsGW4RelVersionR ν Wd c C R V :=
  ⟨⟨IsGW4RelVersion.of_ae_eq h.1.1 hVW, h.1.2⟩, h.2⟩

end InteractingSLE.Theorem14.GW4Fix
