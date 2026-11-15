/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Read

/-!
# The actual physical tips are safe for the retained boundary chart

Packet PROVE-T14-GW2ROOT2. The two original finite traces imply closed-hull
separation before contact. The existing complete-prefix extension permits
direct reuse of GB6's boundary safety theorem, including real visits.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB

/-- All original trace points through a live pre-contact cutoff are safe
for the actual recorded chart, including the seed and real contacts. -/
theorem trace_mem_record_relSafe_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    {t : ℝ≥0} (htv : t ≤ v) : γ t ∈ relSafe (rdrv (cfRec s W ζ ω)) s := by
  obtain ⟨wc, γc, b, hvb, hwc, hwc0, hγc, hew, heγ⟩ :=
    RootF14.exists_complete_prefix_model hγ he.1 he.2.1 (lt_min_iff.mp hv).2
  have hd := disjoint_closure_fwdHull_of_lt_firstContactTime
    hα hW hW0 hγ he.1 he.2.1 hs (lt_min_iff.mp hv).2 (lt_min_iff.mp hv).1
  have hrecord : QuantumZipper.fwdHull (rdrv (cfRec s W ζ ω)) s =
      QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) s :=
    GaugeE.record_hull_eq s hW0 hW hs
  rw [← hrecord,
    ← RootF14.fwdHull_eq_of_prefix_eq hew hvb] at hd
  have hsafe := trace_mem_relSafe (continuous_rdrv _) s.coe_nonneg hwc hwc0 hγc
    (Q3Rel.disjoint_closure_invHull (continuous_rdrv _) s.coe_nonneg hd) htv
  rwa [heγ ⟨zero_le, htv.trans hvb.le⟩] at hsafe

/-- The boundary extension along the actual protected physical trace is
continuous through the prescribed cutoff. -/
theorem continuousOn_record_relBdry_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    ContinuousOn (fun t => relBdry (rdrv (cfRec s W ζ ω)) s (γ t)) (Icc 0 v) :=
  (continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg).comp
    (hγ.2.1.mono fun _ ht =>
      (ENNReal.coe_le_coe.mpr ht.2).trans (lt_min_iff.mp hv).2.le)
    (fun _ ht => trace_mem_record_relSafe_before_contact W ζ ω hα hW hW0 hs he hγ hv ht.2)

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
