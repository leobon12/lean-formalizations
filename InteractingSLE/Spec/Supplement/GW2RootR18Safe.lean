/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBCurve

/-!
# A switched physical path cannot enter a retained counterflow pocket

Packet PROVE-T14-GW2ROOT2. GB6's no-entry theorem applies to any continuous
path from zero, so the physical path need not itself be one Loewner trace.
Only disjointness of the two original traces is required; avoidance of the
closed retained hull is a conclusion, including at real boundary visits.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootR18

open Supp8.GB6 Supp8.GB6.CoordB

/-- A continuous switched path from zero is safe for the relative chart
as long as its inversion misses the retained counterflow trace. -/
theorem path_mem_relSafe_of_trace_disjoint {wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞}
    {α γ : ℝ≥0 → ℂ} (hα : IsGeneratingTrace wα Tα α)
    (hwα : Continuous wα) (hwα0 : wα 0 = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < Tα) {v : ℝ≥0}
    (hγ : ContinuousOn γ (Icc 0 v)) (hγ0 : γ 0 = 0)
    (hγH : MapsTo γ (Icc 0 v) Hbar)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (γ '' Icc 0 v \ {0}))) :
    MapsTo γ (Icc 0 v) (relSafe (Ito.rpath wα) s) := by
  obtain ⟨hAk, _, _, hKA⟩ := rangeData_of_isGeneratingTrace hα hwα.continuousOn hwα0 hs
  have hd : Disjoint (closure (QuantumZipper.fwdHull (Ito.rpath wα) s))
      ((fun z : ℂ => -z⁻¹) '' (γ '' Icc 0 v \ {0})) := by
    change Disjoint (closure (QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s)) _
    rw [hKA]
    apply disjoint_closure_fillH_of_unbounded hAk
    · rintro z ⟨b, ⟨⟨t, ht, rfl⟩, hb0⟩, rfl⟩
      exact ⟨im_neg_inv_nonneg (hγH ht), fun hz =>
        Set.disjoint_left.1 hsep hz ⟨γ t, ⟨⟨t, ht, rfl⟩, hb0⟩, rfl⟩⟩
    · rintro z ⟨b, ⟨⟨t, ht, rfl⟩, hb0⟩, rfl⟩
      exact exists_unbounded_inv_image hγ hγ0 ht hb0
  intro t ht
  refine ⟨hγH ht, ?_⟩
  by_cases hzero : γ t = 0
  · rw [hzero]
    exact zero_notMem_closure_invHull (hwα.comp continuous_real_toNNReal) s.coe_nonneg
  · intro hbad
    have hc : ContinuousAt (fun z : ℂ => -z⁻¹) (γ t) := (continuousAt_inv₀ hzero).neg
    have hin := mem_closure_image hc hbad
    rw [Supp8.Q3Rel.image_invHull] at hin
    exact Set.disjoint_left.1 hd hin ⟨γ t, ⟨⟨t, ht, rfl⟩, hzero⟩, rfl⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootR18
