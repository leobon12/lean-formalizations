/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutJordan
import InteractingSLE.Spec.ZhanGT4.DualA2

/-!
# A.2, the final Jordan step: `J ⊂ S ⊂ D(J)` identifies the outer boundary

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.2 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L597–L602, R38): "Countably many capped rational times exhaust the small curve; continuity gives `J ⊂ S`. We have proved
`J ⊂ S ⊂ D(J)`, where `D(J)` is the bounded component of `ℍ ∖ J`. Jordan separation now identifies the outer boundary of
`S` with `J ∩ ℍ`."

In the Lean set-up the crosscut `J = γ((0, 1))` comes with its unbounded side `D` (`IsCrosscutDomain D γ`); "`S ⊂ D(J)`"
(the closed bounded side) is `S ∩ D = ∅`.

* **`IsCrosscutDomain.unbddPart_eq`**: if `γ((0, 1)) ⊆ S` and `S` misses `D`, the part of `ℍ ∖ S` reachable from
  infinity is `D`;
* **`IsCrosscutDomain.outerBoundary_eq`**: hence `outerBoundary S = γ((0, 1))`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H)

namespace IsCrosscutDomain

variable {D : Set ℂ} {γ : ℝ → ℂ}

/-- **The unbounded side of a crosscut is the part reachable from infinity of any set between the crosscut and its
closed bounded side.** -/
theorem unbddPart_eq (hD : IsCrosscutDomain D γ) {S : Set ℂ} (hJS : γ '' Ioo 0 1 ⊆ S) (hSD : Disjoint S D) :
    unbddPart S = D := by
  obtain ⟨R, hR, hfar⟩ := hD.exists_far_mem
  apply Subset.antisymm
  · refine sUnion_subset fun U ⟨hU, hUS, hUb⟩ => ?_
    -- an unbounded subset of `ℍ` has a far point, which lies in `D`
    obtain ⟨z, hzU, hzR⟩ : ∃ z ∈ U, R < ‖z‖ := by
      by_contra hcon
      push Not at hcon
      exact hUb ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hcon z hz)
    have hUH : U ⊆ H := fun w hw => (hUS hw).1
    refine hD.subset_of_isPreconnected hU hUH ?_ ⟨z, hzU, hfar z (hUH hzU) hzR⟩
    exact Set.disjoint_left.2 fun w hwU hwJ => (hUS hwU).2 (hJS hwJ)
  · refine subset_sUnion_of_mem ⟨hD.isPreconnected, fun z hz => ⟨hD.subset_H hz, fun hzS =>
      Set.disjoint_left.1 hSD hzS hz⟩, fun hb => ?_⟩
    -- `D` contains all far points of `ℍ`, so it is unbounded
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    have hz : ((max R C + 1 : ℝ) : ℂ) * I ∈ H := by
      show 0 < (((max R C + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [le_max_left R C]
    have hnorm : ‖((max R C + 1 : ℝ) : ℂ) * I‖ = max R C + 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [le_max_left R C])]
    have h1 := hC _ (hfar _ hz (by rw [hnorm]; linarith [le_max_left R C]))
    rw [hnorm] at h1
    linarith [le_max_right R C]

/-- **A.2's Jordan step**: if the crosscut `γ((0, 1))` lies in `S` and `S` lies in the closed bounded side of the
crosscut (`S` misses the unbounded side `D`), the outer boundary of `S` in `ℍ` is `γ((0, 1))`. -/
theorem outerBoundary_eq (hD : IsCrosscutDomain D γ) {S : Set ℂ} (hJS : γ '' Ioo 0 1 ⊆ S) (hSD : Disjoint S D) :
    outerBoundary S = γ '' Ioo 0 1 := by
  rw [outerBoundary, hD.unbddPart_eq hJS hSD, hD.frontier_inter]

end IsCrosscutDomain

end InteractingSLE.ZhanGT4
