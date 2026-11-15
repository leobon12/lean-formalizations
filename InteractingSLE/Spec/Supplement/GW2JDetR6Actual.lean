/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Decode

/-!
# The physical record decoder from relative hull identification

The source traces discharge the clock, inverse chart and capacity facts.
The only candidate-specific assertions are its relative hull identity and
availability before its continuation lifetime.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR6

open Exist.StagedLaw Supp8.GB6 GW2TipSystem GW2JDetR3 GW2JDetR4

/-- Relative hull identification and lifetime coverage give the physical
stopped record as the explicit Borel readout. All other geometric premises
come from the two original generating traces. -/
theorem recordRead_eq_of_relative_hulls {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {u | (u : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hT : 0 < T)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hec : ContinuousOn e.1 {u | (u : ℝ≥0∞) < e.2}) (he0 : e.1 0 = 0)
    (hlife : ∀ u : ℝ≥0, (u : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T →
      ((relClock (Ito.rpath (W · ω)) s (Ito.rpath w) u).toNNReal : ℝ≥0∞) < e.2)
    (hgeom : ∀ u : ℝ≥0, (u : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T →
      fwdHull (Ito.rpath e.1) (relClock (Ito.rpath (W · ω)) s (Ito.rpath w) u) =
        relMap (Ito.rpath (W · ω)) s '' fwdHull (Ito.rpath w) u)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T) :
    recordRead s t (cfRec s W ζ ω, e) =
      cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  obtain ⟨V, -, ha0, hm, hc, -, -⟩ :=
    exists_inverse_capacity_chain W ζ ω hα hW hW0 hs hsH hγ hw hw0 hT
  let r := cfRec s W ζ ω
  have he : EqOn (rdrv r) (Ito.rpath (W · ω)) (Icc 0 s) :=
    GaugeE.record_prefix_eq s hW0 hW hs
  have hclock := relClock_eq_of_eqOn s.coe_nonneg he (Ito.rpath w)
  have hmap := relMap_eq_of_eqOn s.coe_nonneg he
  apply recordRead_eq_of_inverse_hulls s r ha0 hm hc hec he0 hγ hw hw0
    (min_le_right _ _) ?_ ?_ ht
  · intro u hu
    rw [hclock]
    exact hlife u hu
  · intro u hu
    rw [hclock, hgeom u hu, ← hmap]
    exact relInv_image_relMap_before_contact W ζ ω hα hW hW0 hs hγ hw hw0 hu

end InteractingSLE.Theorem14.GW2JDetR6
