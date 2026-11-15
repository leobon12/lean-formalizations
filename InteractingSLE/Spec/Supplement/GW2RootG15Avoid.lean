/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootReg
import InteractingSLE.Spec.Supplement.GB6RestartProofR1
import InteractingSLE.Spec.Supplement.GB6Disjoint

/-!
# The actual regularized chart domain before contact

Packet PROVE-T14-GW2ROOT2. Discharge the `hdom` input of F14 for the
regularized chart. The landed generating-trace separation theorem gives
disjoint closed hulls before the first trace contact. Locality identifies
the regularized chart hull with the original hull at its live stop.
Neither hull avoidance nor closed-hull separation is a premise here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG15

open Supp8.GB6

/-- At a live stop, regularization preserves the actual chart hull.
Only continuity before the lifetime is required. -/
theorem regW_fwdHull_eq {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) {s : ℝ≥0}
    (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : W 0 ω = 0) (hs : (s : ℝ≥0∞) < ζ ω) :
    QuantumZipper.fwdHull (fun q : ℝ => regW s W ζ q.toNNReal ω) s =
      QuantumZipper.fwdHull (fun q : ℝ => W q.toNNReal ω) s := by
  obtain ⟨b, hsb, hbζ⟩ := exists_real_btwn_of_lt hs
  apply fwdHull_eq_of_eqOn s.coe_nonneg hsb
  intro q hq
  change (GW2JointKernel.cfE s W ζ ω).1 q.toNNReal = W q.toNNReal ω
  apply cfE_fst_of_lt s hW0 hW
  have hqb : q.toNNReal ≤ b.toNNReal := Real.toNNReal_le_toNNReal hq.2
  exact (ENNReal.coe_le_coe.mpr hqb).trans_lt hbζ

/-- Every physical hull before first trace contact lies in the domain of
the actual regularized chart. This is precisely F14's `hdom`, with the
contact time defined by the two generating traces. -/
theorem inv_notMem_regW_fwdHull_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (fun t => W t ω) (ζ ω) α)
    (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : W 0 ω = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) :
    ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < min
        (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
          ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T →
      ∀ z ∈ QuantumZipper.fwdHull (fun q : ℝ => w q.toNNReal) t,
        -z⁻¹ ∉ QuantumZipper.fwdHull (fun q : ℝ => regW s W ζ q.toNNReal ω) s := by
  intro t ht z hz
  rw [regW_fwdHull_eq W ζ ω hW hW0 hs]
  have hd := disjoint_closure_fwdHull_of_lt_firstContactTime
    hα hW hW0 hγ hw hw0 hs (lt_min_iff.mp ht).2 (lt_min_iff.mp ht).1
  intro hbad
  exact Set.disjoint_left.mp hd (subset_closure hbad)
    (subset_closure (mem_image_of_mem (fun q : ℂ => -q⁻¹) hz))

end InteractingSLE.Theorem14.GW2TipSystem.RootG15
