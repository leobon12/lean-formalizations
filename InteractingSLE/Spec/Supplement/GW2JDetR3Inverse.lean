/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ16Chain
import InteractingSLE.Spec.Supplement.GW2RootF14Extension
import InteractingSLE.Spec.Supplement.GB6GaugeEClock
import InteractingSLE.Spec.Coupling.WholeField2Cap

/-!
# Inverting the actual GW2 relative hulls

The inverse relative chart recovers each physical hull before first contact.
Its half-plane capacity recovers the original physical time. Both assertions
are derived from generating traces with their original finite lifetimes.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR3

open Supp8.GB6 GW2TipSystem

/-- Half-plane capacity reads the original time from every live physical hull,
even when the driver is continuous only before its finite lifetime. -/
theorem hcapHit_fwdHull_of_live_trace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    WholeField.hcapHit (fwdHull (Ito.rpath w) t) = ENNReal.ofReal (2 * (t : ℝ)) := by
  obtain ⟨w', _, b, htb, hw', hw'0, _, he, _⟩ :=
    RootF14.exists_complete_prefix_model hγ hw hw0 ht
  have hK : fwdHull (Ito.rpath w') t = fwdHull (Ito.rpath w) t :=
    RootF14.fwdHull_eq_of_prefix_eq he htb
  rw [← hK]
  exact WholeField.hcapHit_fwdHull (hw'.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_def, Real.toNNReal_zero] using hw'0) t.coe_nonneg

/-- Inverting the relative image recovers a physical hull on the chart domain.
This is set-theoretic read-back, with no boundary landing assumption. -/
theorem relInv_image_relMap_hull {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {K : Set ℂ} (hKH : K ⊆ H)
    (hK : ∀ z ∈ K, -z⁻¹ ∉ fwdHull U s) :
    relInv U s '' (relMap U s '' K) = K := by
  rw [image_image]
  calc
    (fun z => relInv U s (relMap U s z)) '' K = id '' K := by
      apply image_congr
      intro z hz
      exact relInv_relMap hU hU0 hs (hKH hz) (hK z hz)
    _ = K := image_id K

/-- Before first contact the actual chart inverse recovers the physical hull.
The domain condition is proved from the two generating traces. -/
theorem relInv_image_relMap_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T) :
    relInv (Exist.StagedLaw.rdrv (cfRec s W ζ ω)) s ''
      (relMap (Exist.StagedLaw.rdrv (cfRec s W ζ ω)) s '' fwdHull (Ito.rpath w) t) =
        fwdHull (Ito.rpath w) t := by
  let U := Exist.StagedLaw.rdrv (cfRec s W ζ ω)
  have hU : Continuous U := Exist.StagedLaw.continuous_rdrv _
  have hU0 : U 0 = 0 := Exist.StagedLaw.rdrv_zero _
  have hUK : fwdHull U s = fwdHull (Ito.rpath (regW s W ζ · ω)) s := by
    exact (GaugeE.record_hull_eq s hW0 hW hs).trans
      (RootG15.regW_fwdHull_eq W ζ ω hW hW0 hs).symm
  apply relInv_image_relMap_hull hU hU0 s.coe_nonneg
  · obtain ⟨w', _, b, htb, hw', _, _, hew, _⟩ :=
      RootF14.exists_complete_prefix_model hγ hw hw0 (lt_min_iff.mp ht).2
    have hK : fwdHull (Ito.rpath w') t = fwdHull (Ito.rpath w) t :=
      RootF14.fwdHull_eq_of_prefix_eq hew htb
    rw [← hK]
    exact (isHPHull_fwdHull (hw'.comp continuous_real_toNNReal) t.coe_nonneg).1
  · intro z hz
    rw [hUK]
    exact RootG15.inv_notMem_regW_fwdHull_before_contact
      W ζ ω hα hW hW0 hs hγ hw hw0 t ht z hz

end InteractingSLE.Theorem14.GW2JDetR3
