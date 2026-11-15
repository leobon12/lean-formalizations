/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Hull

/-!
# A Borel normalized driver read directly from the relative trace

Packet PROVE-T14-GW2ROOT2. Apply the landed hull-to-driver reconstruction
to the filled dyadic trace prefixes. A live generating trace proves the
identity with its original driver and the entire trace predicate.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootB23

open Restart Supp8.GB6

/-- The normalized Loewner driver read from the curve's filled prefixes. -/
def traceDriverRead (γ : ℝ≥0 → ℂ) (u : ℝ≥0) : ℝ :=
  GW2JDetR4.hullDriverRead (traceHullRead γ) u

theorem measurable_traceDriverRead (u : ℝ≥0) :
    Measurable (fun γ : ℝ≥0 → ℂ => traceDriverRead γ u) :=
  GW2JDetR4.measurable_hullDriverRead measurable_traceHullRead u

theorem traceDriverRead_zero (γ : ℝ≥0 → ℂ) : traceDriverRead γ 0 = 0 := by
  simp only [traceDriverRead, GW2JDetR4.hullDriverRead, ↓reduceIte]

/-- The total Borel reader recovers the original driver at every live
capacity time, using only the original generating trace and regularity. -/
theorem traceDriverRead_eq {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < T) :
    traceDriverRead γ u = w u := by
  obtain ⟨w', _, b, hub, hw', hw'0, _, hew, _⟩ :=
    RootF14.exists_complete_prefix_model hγ hw hw0 hu
  have hh : traceDriverRead γ u = Ito.rpath w' u := by
    apply GW2JDetR4.hullDriverRead_eq_of_prefix (hw'.comp continuous_real_toNNReal)
      (by simpa only [Ito.rpath, Function.comp_apply, Real.toNNReal_zero] using hw'0)
    intro r hru
    exact (traceHullRead_eq_fwdHull hγ hw hw0
      ((ENNReal.coe_le_coe.mpr hru).trans_lt hu)).trans
        (RootF14.fwdHull_eq_of_prefix_eq hew (hru.trans_lt hub)).symm
  have hh' : traceDriverRead γ u = w' u := by
    simpa only [Ito.rpath, Real.toNNReal_coe] using hh
  exact hh'.trans (hew ⟨zero_le, hub.le⟩)

theorem continuousOn_traceDriverRead {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) : ContinuousOn (traceDriverRead γ) {t | (t : ℝ≥0∞) < T} :=
  hw.congr fun _ ht => traceDriverRead_eq hγ hw hw0 ht

theorem continuousAt_traceDriverRead {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < T) :
    ContinuousAt (traceDriverRead γ) u :=
  (continuousOn_traceDriverRead hγ hw hw0).continuousAt
    ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hu)

/-- The reconstructed driver generates the very same original trace,
through its closed endpoint, without choosing a measurable driver witness. -/
theorem isGeneratingTrace_traceDriverRead {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) : IsGeneratingTrace (traceDriverRead γ) T γ := by
  refine ⟨hγ.1, hγ.2.1, ?_⟩
  intro u hu
  obtain ⟨b, hub, hbT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hu
  have he : EqOn (traceDriverRead γ) w (Icc 0 b) := by
    intro r hr
    exact traceDriverRead_eq hγ hw hw0 ((ENNReal.coe_le_coe.mpr hr.2).trans_lt hbT)
  rw [RootF14.fwdHull_eq_of_prefix_eq he (ENNReal.coe_lt_coe.mp hub)]
  exact hγ.2.2 u hu

end InteractingSLE.Theorem14.GW2TipSystem.RootB23
