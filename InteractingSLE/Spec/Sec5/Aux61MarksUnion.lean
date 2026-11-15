/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksNull
import InteractingSLE.Spec.Sec5.Aux61ChLocCore
import InteractingSLE.Spec.Sec5.Aux61RestartInstHistory
import InteractingSLE.Spec.Sec5.GlueCondHit
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssemblyMean
import InteractingSLE.WangWu.Prop418Side

/-!
# The marked set of the restart chart and the union containment at the glued stop

Packet PROVE-AUX61-MARKS. CHARTLOC's geometry fixes the physical marked set on the live event:
`ℍ ∖ A = c⁻¹(ℍ ∖ K_r)` (`c` the restart chart, `K_r` the chart hull of the code at fibre time `r`). Here:

* the **chart set** `chartSet c K = ℍ ∖ c⁻¹(ℍ ∖ K)`: inside `ℍ`, its complement is the chart pullback
  (`H_diff_chartSet`, the geometry), relatively closed (`isOpen_H_diff_chartSet`), monotone in the hull
  (`chartSet_mono`);
* **containment** (`subset_chartSet`): a set whose points in the chart domain are mapped into `K` lies in the chart set;
* **the union at the glued stop is contained in the live chart set** (`ae_unionAt_subset_liveSet_chartSet`): UNIONLOC's
  `ℍ ∩ (K_s ∪ K̃_T)` (`K_s` the counterflow hull at `s`, `K̃_T` the flow's Loewner hull at the glued stop `T`) is
  almost surely contained in `liveSet S (chartSet c K)` once, on the live event `S`, `T` is finite, the chart domain
  avoids the counterflow hull, and the flow hull's points in the chart domain are mapped into the chart hull;
* the two geometric inputs from the structure of R1's chart and the flow line: the **retained component avoids the
  counterflow hull and the own prefix** (`cfHullQ_disjoint_restartComponent`, `image_disjoint_restartComponent`, on
  good counterflow histories), and for a **simple flow line** the flow hull is
  the trace (`WangWu.fwdHull_eq_image_Ioc`),
  so the flow hull's points in the domain are mapped into the chart hull as soon as the restarted path is
  (`flowHull_mapsTo_of_properArc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc
open Aux61ChLoc (liveSet liveSet_of_mem liveSet_of_notMem)

/-! ### The chart set -/

section ChartSet

/-- **The chart set** of a chart and a hull: `ℍ` minus the chart pullback of the complement of the hull. -/
def chartSet (c : Chart) (K : Set ℂ) : Set ℂ := H \ c.2.1 '' (H \ K)

theorem chartSet_subset_H (c : Chart) (K : Set ℂ) : chartSet c K ⊆ H := sdiff_subset

/-- **The geometry of the chart set**: inside `ℍ` its complement is the chart pullback of the complement of the hull. -/
theorem H_diff_chartSet {c : Chart} (hc : c.IsConformal) (K : Set ℂ) : H \ chartSet c K = c.2.1 '' (H \ K) := by
  have hsub : c.2.1 '' (H \ K) ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact hc.2.1 hw.1
  rw [chartSet, sdiff_sdiff_cancel_left hsub]

/-- The chart set is relatively closed when the hull is. -/
theorem isOpen_H_diff_chartSet {c : Chart} (hc : c.IsConformal) {K : Set ℂ} (hK : IsOpen (H \ K)) :
    IsOpen (H \ chartSet c K) := by
  rw [H_diff_chartSet hc]
  exact SmallGammaGeodesics.CC.isOpen_image_conf hK (hc.1.mono sdiff_subset) (hc.injOn.mono sdiff_subset)

/-- The chart set is monotone in the hull. -/
theorem chartSet_mono (c : Chart) {K K' : Set ℂ} (h : K ⊆ K') : chartSet c K ⊆ chartSet c K' :=
  sdiff_subset_sdiff_right (image_mono (sdiff_subset_sdiff_right h))

/-- **Containment in the chart set**: a set whose points in the chart domain are mapped into the hull lies, inside `ℍ`,
in the chart set. -/
theorem subset_chartSet {c : Chart} (hc : c.IsConformal) {K S : Set ℂ}
    (hS : ∀ z ∈ S, z ∈ (c.dom : Set ℂ) → c.1 z ∈ K) : H ∩ S ⊆ chartSet c K := by
  rintro z ⟨hzH, hzS⟩
  refine ⟨hzH, ?_⟩
  rintro ⟨w, hw, rfl⟩
  have hdom : c.2.1 w ∈ (c.dom : Set ℂ) := by
    rw [hc.coe_dom]
    exact mem_image_of_mem _ hw.1
  have hK := hS _ hzS hdom
  rw [hc.2.2 w hw.1] at hK
  exact hw.2 hK

end ChartSet

/-! ### The union at the glued stop -/

section Union

variable {X : Type*}

/-- **The union at a finite stop is in the chart set** when the chart domain avoids the counterflow hull and the
flow hull's points in the domain are mapped into the chart hull. -/
theorem unionAt_subset_chartSet {A₂ : X → Set ℂ} {Kf : ℝ≥0 → X → Set ℂ} {T : X → ℝ≥0∞} {c : Chart}
    {K : Set ℂ} {x : X} (hc : c.IsConformal) (hT : T x < ⊤)
    (hcf : ∀ z ∈ A₂ x, z ∉ (c.dom : Set ℂ))
    (hflow : ∀ z ∈ Kf (T x).toNNReal x, z ∈ (c.dom : Set ℂ) → c.1 z ∈ K) :
    unionAt A₂ Kf T x ⊆ chartSet c K := by
  simp only [unionAt, hT, ↓reduceIte]
  refine subset_chartSet hc fun z hz hzd => ?_
  rcases hz with hz | hz
  · exact absurd hzd (hcf z hz)
  · exact hflow z hz hzd

variable [MeasurableSpace X] {μ : Measure X}

/-- **The union at the glued stop is almost surely in the live chart set** (UNIONLOC's containment for the marked set
fixed by CHARTLOC's geometry): on the live event `S` the stop is finite, the chart is conformal, the chart domain avoids
the counterflow hull and the flow hull's points in the domain are mapped into the chart hull; off `S` the live set is
`ℍ`. -/
theorem ae_unionAt_subset_liveSet_chartSet {S : Set X} {A₂ : X → Set ℂ} {Kf : ℝ≥0 → X → Set ℂ}
    {T : X → ℝ≥0∞} {c : X → Chart} {K : X → Set ℂ}
    (hgood : ∀ᵐ x ∂μ, x ∈ S → (c x).IsConformal ∧ T x < ⊤ ∧ (∀ z ∈ A₂ x, z ∉ ((c x).dom : Set ℂ)) ∧
      ∀ z ∈ Kf (T x).toNNReal x, z ∈ ((c x).dom : Set ℂ) → (c x).1 z ∈ K x) :
    ∀ᵐ x ∂μ, unionAt A₂ Kf T x ⊆ liveSet S (fun x => chartSet (c x) (K x)) x := by
  classical
  filter_upwards [hgood] with x hx
  by_cases hxS : x ∈ S
  · rw [liveSet_of_mem hxS]
    obtain ⟨hc, hT, hcf, hflow⟩ := hx hxS
    exact unionAt_subset_chartSet hc hT hcf hflow
  · rw [liveSet_of_notMem hxS]
    by_cases hT : T x < ⊤
    · simp only [unionAt, hT, ↓reduceIte]
      exact inter_subset_left
    · simp only [unionAt, hT, ↓reduceIte, subset_refl]

end Union

/-! ### The geometric inputs -/

section Geometry

open Aux61Restart GlueCond WangWu CfRegQ

/-- **The retained component avoids the retained hull and the own prefix.** -/
theorem restartComponent_subset {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b : ℂ} :
    restartComponent K η r b ⊆ H \ (K ∪ η '' Icc 0 r) :=
  connectedComponentIn_subset _ _

/-- The retained component avoids the own prefix through the restart time. -/
theorem image_disjoint_restartComponent {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b : ℂ} {u : ℝ} (hu : u ∈ Icc 0 r) :
    η u ∉ restartComponent K η r b := fun h =>
  (restartComponent_subset h).2 (Or.inr (mem_image_of_mem η hu))

/-- **The retained component avoids the counterflow hull** on a good counterflow history: there the counterflow hull of
the glued record is the history hull read from the stopped record (`cfHullQ_eq_of_mem_goodCfSet`,
`CrossCond.Word49.fwdHull_cfDrv0`). -/
theorem cfHullQ_disjoint_restartComponent {s : ℝ≥0} {q : ℚ} {Ω : Type*} {Y : Ω → LawUnique.HistorySpace 0 0}
    {η : Ω → ℝ → ℂ} {b : Ω → ℂ} {ω : Ω} (hy : Y ω ∈ goodCfSet) {z : ℂ} (hz : z ∈ cfHullQ s (Y ω)) :
    z ∉ historyComponent s q Y η b ω := by
  intro hzD
  have hK : z ∈ historyHull s Y ω := by
    rw [historyHull, CrossCond.Word49.fwdHull_cfDrv0 hy s, ← cfHullQ_eq_of_mem_goodCfSet hy]
    exact hz
  exact (restartComponent_subset hzD).2 (Or.inl hK)

/-- **For a simple flow line the flow hull's points in the chart domain are mapped into the chart hull** as soon as the
domain avoids the prefix through the restart time `t₀` and the restarted path through the stop `T` is mapped into
the chart hull. -/
theorem flowHull_mapsTo_of_properArc {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hγ : IsProperArc η)
    {t₀ T : ℝ} (hT : 0 ≤ T) {c : Chart} {K : Set ℂ}
    (hpre : ∀ u ∈ Icc 0 t₀, η u ∉ (c.dom : Set ℂ))
    (hpost : ∀ u ∈ Ioc t₀ T, η u ∈ (c.dom : Set ℂ) → c.1 (η u) ∈ K) :
    ∀ z ∈ fwdHull W T, z ∈ (c.dom : Set ℂ) → c.1 z ∈ K := by
  rw [fwdHull_eq_image_Ioc hη hγ hT]
  rintro _ ⟨u, hu, rfl⟩ hd
  by_cases hut : u ≤ t₀
  · exact absurd hd (hpre u ⟨hu.1.le, hut⟩)
  · exact hpost u ⟨not_le.1 hut, hu.2⟩ hd

end Geometry

end InteractingSLE.Sec5.Aux61Marks
