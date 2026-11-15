/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Prefix
import InteractingSLE.Spec.Sec5.Aux61SlitWRead
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYFillMeas
import InteractingSLE.Spec.Sec7.SideHeightRange

/-!
# Borel filled hulls from the actual relative trace observations

Packet PROVE-T14-GW2ROOT2. Reuse the clamped dyadic prefix code and the
total measurable filling reader. On every continuous generating prefix
the reader is exactly its Loewner hull, including real boundary visits.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootB23

open Restart LawUnique Restart.FlowStopIdentCMI Supp8.GB6

/-- The filled visible part of the closed dyadic prefix code. This is
a total Borel hull reader on the complete product path space. -/
def traceHullRead (γ : ℝ≥0 → ℂ) (u : ℝ≥0) : Set ℂ :=
  hullFillReader (closure (range fun j : ℕ × ℕ => γ (min (dyadicTime j) u)) ∩ H)

theorem measurable_traceHullRead (u : ℝ≥0) :
    Measurable[_, hittingSigma] (fun γ : ℝ≥0 → ℂ => traceHullRead γ u) := by
  have hc := Sec5.Aux61SlitW.measurable_closure_range
    (f := fun (γ : ℝ≥0 → ℂ) (j : ℕ × ℕ) => γ (min (dyadicTime j) u))
    (fun j : ℕ × ℕ => measurable_pi_apply (min (dyadicTime j) u))
  apply measurable_hullFillReader.comp
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have he : (fun γ : ℝ≥0 → ℂ =>
      closure (range fun j : ℕ × ℕ => γ (min (dyadicTime j) u)) ∩ H) ⁻¹'
      {A : Set ℂ | (A ∩ U).Nonempty} =
      (fun γ : ℝ≥0 → ℂ =>
        closure (range fun j : ℕ × ℕ => γ (min (dyadicTime j) u))) ⁻¹'
          {A : Set ℂ | (A ∩ U).Nonempty} := by
    ext γ
    constructor
    · rintro ⟨z, ⟨hz, _⟩, hzU⟩
      exact ⟨z, hz, hzU⟩
    · rintro ⟨z, hz, hzU⟩
      exact ⟨z, ⟨hz, hUH hzU⟩, hzU⟩
  rw [he]
  exact hc (LocalSets.measurableSet_hitting hU hUH)

/-- Closing the dyadic code and filling its visible part recovers the
full continuous prefix's filling. Real visits are retained correctly. -/
theorem traceHullRead_eq_fillH {γ : ℝ≥0 → ℂ} {u : ℝ≥0}
    (hc : ContinuousOn γ (Icc 0 u)) : traceHullRead γ u = fillH (γ '' Icc 0 u) := by
  have hK := isCompact_Icc.image_of_continuousOn hc
  unfold traceHullRead
  rw [Sec5.Aux61SlitW.closure_range_clamped_dyadic hc,
    hullFillReader_eq_fillH inter_subset_right (hK.isBounded.subset inter_subset_left),
    Sec7.SideHeight.fillH_inter_H]

/-- A live original generating trace identifies the total reader with
its actual hull; no hull identity or Borel trace selection is assumed. -/
theorem traceHullRead_eq_fwdHull {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < T) :
    traceHullRead γ u = QuantumZipper.fwdHull (Ito.rpath w) u := by
  have hc : ContinuousOn γ (Icc 0 u) :=
    hγ.2.1.mono fun _ ht => (ENNReal.coe_le_coe.mpr ht.2).trans hu.le
  have hK := isCompact_Icc.image_of_continuousOn hc
  obtain ⟨w', _, b, hub, hw', _, _, hew, _⟩ :=
    RootF14.exists_complete_prefix_model hγ hw hw0 hu
  have hhull : QuantumZipper.fwdHull (Ito.rpath w') u =
      QuantumZipper.fwdHull (Ito.rpath w) u := RootF14.fwdHull_eq_of_prefix_eq hew hub
  have hKH : QuantumZipper.fwdHull (Ito.rpath w) u ⊆ H := by
    rw [← hhull]
    exact (isHPHull_fwdHull (hw'.comp continuous_real_toNNReal) u.coe_nonneg).1
  rw [traceHullRead_eq_fillH hc]
  exact ((fillH_eq_iff_isFilling_of_isClosed hK.isBounded hK.isClosed hKH).mp
    (hγ.2.2 u hu)).symm

end InteractingSLE.Theorem14.GW2TipSystem.RootB23
