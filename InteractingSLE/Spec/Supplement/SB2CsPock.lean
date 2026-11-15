/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CsMean

/-!
# The pockets of a union of fills

Packet PROVE-SB2-CONDFIN (round 10, D51 item 1). Deterministic geometry for `Cs.ae_localSetMean_eqOn_of_pockets`.
For sets `X`, `Y` with the B-only union `U_B = fill X ∪ fill Y` and the joint union `U_J = fill X ∪ fill (X ∪ Y)`
(`fill` = `fillH ∘ closure`):

* `unionFill_subset`: `U_B ⊆ U_J`;
* **`isOpen_pockets`**: if `ℍ ∖ U_B` is open, the pockets `(ℍ ∖ U_B) ∩ U_J` are open (every pocket point lies in a
  bounded component of `ℍ ∖ cl (X ∪ Y)`, an open set all of whose points are pocket points or in `U_B`).

Deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Cs

theorem unionFill_subset (X Y : Set ℂ) :
    fillH (closure X) ∪ fillH (closure Y) ⊆ fillH (closure X) ∪ fillH (closure (X ∪ Y)) :=
  union_subset_union_right _ (fillH_mono (closure_mono subset_union_right))

/-- **The pockets of the joint fill are open** (given that the complement of the B-only union is open). -/
theorem isOpen_pockets (X Y : Set ℂ)
    (hBo : IsOpen (H \ (fillH (closure X) ∪ fillH (closure Y)))) :
    IsOpen ((H \ (fillH (closure X) ∪ fillH (closure Y))) ∩ (fillH (closure X) ∪ fillH (closure (X ∪ Y)))) := by
  set UB := fillH (closure X) ∪ fillH (closure Y) with hUB
  set S := closure (closure (X ∪ Y)) with hS
  have hO : IsOpen (H \ S) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨⟨hzH, hzB⟩, hzJ⟩
  -- `z` lies outside the closures of `X` and `Y`
  have hzX : z ∉ closure X := fun h' => hzB (Or.inl ⟨hzH, Or.inl (subset_closure h')⟩)
  have hzY : z ∉ closure Y := fun h' => hzB (Or.inr ⟨hzH, Or.inl (subset_closure h')⟩)
  have hzS : z ∉ S := by
    rw [hS, closure_closure, closure_union]
    rintro (h' | h')
    · exact hzX h'
    · exact hzY h'
  have hzF : z ∈ fillH (closure (X ∪ Y)) := by
    rcases hzJ with h' | h'
    · exact absurd (Or.inl h') hzB
    · exact h'
  have hbd : Bornology.IsBounded (connectedComponentIn (H \ S) z) := by
    rcases hzF.2 with h' | h'
    · exact absurd h' hzS
    · exact h'
  refine ⟨connectedComponentIn (H \ S) z ∩ (H \ UB), fun w hw => ⟨hw.2, ?_⟩,
    (hO.connectedComponentIn).inter hBo, ⟨mem_connectedComponentIn ⟨hzH, hzS⟩, hzH, hzB⟩⟩
  have hwS : w ∈ H \ S := connectedComponentIn_subset _ _ hw.1
  refine Or.inr ⟨hwS.1, Or.inr ?_⟩
  rw [connectedComponentIn_eq hw.1] at hbd
  exact hbd

end InteractingSLE.Theorem14.SB.Cs
