/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWNull
import InteractingSLE.Spec.Sec5.Aux61MarksHull

/-! # The physical union is contained in the built live marked set -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61ULoc Aux61ChLoc Aux61FibData Aux61GInst Aux61UnionK
open Restart.FlowStopIdentG

universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {D : MarksData μ}

/-- The physical geometry uniquely identifies a marked subset of `H` with
the chart set. -/
theorem chartSet_eq_of_geometry {c : Chart} {K A : Set ℂ} (hA : A ⊆ H)
    (hgeo : H \ A = c.2.1 '' (H \ K)) : chartSet c K = A := by
  rw [chartSet, ← hgeo, sdiff_sdiff_cancel_left hA]

/-- R1's initial chart, causal capacity rule, and the simple physical flow
give the union containment required by the null-completed wiring. The set
is identified from `MarksFacts.geometry`; no extra chart-set identity is assumed. -/
theorem ae_unionAt_subset_liveSets_of_capacityRule
    (hF : MarksFacts μ D) {Y : Type*} [MeasurableSpace Y] {nL nR : ℕ}
    (c : D.ι → Y × LawUnique.HistorySpace nL nR → Chart) (r : D.ι → ℝ≥0)
    (Y₀ : X → Y) (R₀ : X → LawUnique.HistorySpace nL nR)
    (A₂ : X → Set ℂ) (Wf : X → ℝ → ℝ) (η : X → ℝ → ℂ)
    (hflow : ∀ᵐ x ∂μ, IsLoewnerTrace (Wf x) (η x) ∧ WangWu.IsProperArc (η x))
    (hchart : ∀ i, ∀ᵐ x ∂μ, x ∈ D.event i → D.chart i x = c i (Y₀ x, stopRec (r i) (R₀ x)))
    (hread : ∀ i, ∀ᵐ x ∂μ, x ∈ D.event i → ∀ u : ℝ≥0, 0 < u →
      u < exitNN (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) x →
      D.path i x u = histTrace 0 (R₀ x) (r i + u))
    (hrestart : ∀ i, ∀ᵐ x ∂μ, x ∈ D.event i → ∀ u : ℝ≥0, 0 < u →
      u < exitNN (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) x →
      D.path i x u = η x ((r i : ℝ) + u))
    (hpre : ∀ i, ∀ᵐ x ∂μ, x ∈ D.event i →
      ∀ u ∈ Icc (0 : ℝ) (r i), η x u ∉ (D.chart i x).dom)
    (hcf : ∀ i, ∀ᵐ x ∂μ, x ∈ D.event i → ∀ z ∈ A₂ x, z ∉ (D.chart i x).dom) :
    ∀ i t, ∀ᵐ x ∂μ, unionAt A₂ (fun v x => fwdHull (Wf x) (v : ℝ))
      (fun x => capacityRule (c i) (r i) t (Y₀ x, R₀ x)) x ⊆ D.liveSets i t x := by
  intro i t
  filter_upwards [hflow, hchart i, hread i, hrestart i, hpre i, hcf i, hF.geometry i t]
    with x hη hc hr hρ hp hK hg
  by_cases hx : x ∈ liveEv (D.Z i) (D.B i) (D.code i) t
  · have hxE := (mem_exitEv_of_lt_accessLife hx.2).1.1
    have htime : capacityRule (c i) (r i) t (Y₀ x, R₀ x) =
        ((r i + accessTime (E := D.event i) (c := D.chart i) (ρ := D.path i)
          (T := D.life i) (V := D.window i) x t : ℝ≥0) : ℝ≥0∞) := by
      by_cases ht : t = 0
      · subst t
        rw [capacityRule_zero, accessTime_zero (hF.spec i) (hF.open_window i) (hF.zero_window i)
          (hF.landing i) (hF.injective_path i) hx.2, add_zero]
      · exact capacityRule_eq_accessTime (hF.spec i) (hF.open_window i) (hF.zero_window i)
          (hF.landing i) (hF.injective_path i) (hc hxE) (hr hxE) (pos_iff_ne_zero.2 ht) hx.2
    have hτ := (accessTime_spec (hF.spec i) (hF.open_window i) (hF.zero_window i)
      (hF.landing i) (hF.injective_path i) hx.2).1
    rw [show D.liveSets i t x = D.baseSets i t x from liveSet_of_mem hx,
      ← chartSet_eq_of_geometry (hF.baseSets_closed i t x).1 (hg hx.1 hx.2)]
    apply unionAt_subset_chartSet ((hF.spec i).conf x hxE)
      (htime ▸ ENNReal.coe_lt_top) (hK hxE)
    rw [htime, ENNReal.toNNReal_coe]
    exact fwdHull_mapsTo_chartHull_of_access (hF.spec i) (hF.open_window i) (hF.zero_window i)
      (hF.landing i) (hF.injective_path i) (D.data i) (hF.data_window i) (hF.data_clearance i)
      hx.2 hη.1 hη.2 (fun u hu hule => hρ hxE u hu (hule.trans_lt hτ)) (hp hxE)
  · rw [show D.liveSets i t x = H from liveSet_of_notMem hx]
    by_cases hT : capacityRule (c i) (r i) t (Y₀ x, R₀ x) < ⊤
    · simp only [unionAt, hT, ↓reduceIte]
      exact inter_subset_left
    · simp only [unionAt, hT, ↓reduceIte, subset_refl]

end InteractingSLE.Sec5.Aux61SlitW
