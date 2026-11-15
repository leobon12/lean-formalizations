/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GContWindow
import Mathlib.Topology.Bases

/-! # A fixed countable family of compact buffers

Finite unions of a countable plane basis approximate compact sets inside
open sets. This gives countably many candidate buffers independently of the
future path; selecting the member which captures a path is pointwise.
-/

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace

namespace InteractingSLE.Sec5.Aux61GWord

/-- Indices for finite unions in a fixed countable basis of the plane. -/
abbrev BufferIndex := Finset (countableBasis ℂ)

/-- The open buffer represented by a finite list of basis elements. -/
def basisBuffer (s : BufferIndex) : Set ℂ := ⋃ U ∈ s, (U : Set ℂ)

/-- Every member of the fixed buffer family is open. -/
theorem isOpen_basisBuffer (s : BufferIndex) : IsOpen (basisBuffer s) :=
  isOpen_biUnion fun U _ => isOpen_of_mem_countableBasis U.2

/-- A compact set inside an open set has a buffer from the fixed countable
family whose compact closure remains inside that open set. -/
theorem exists_basisBuffer {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ s : BufferIndex, K ⊆ basisBuffer s ∧ closure (basisBuffer s) ⊆ O ∧
      IsCompact (closure (basisBuffer s)) := by
  classical
  obtain ⟨G, hGo, hKG, hGO, hGc⟩ :=
    exists_open_between_and_isCompact_closure hK hO hKO
  let I := {U : countableBasis ℂ // (U : Set ℂ) ⊆ G}
  have hcover : K ⊆ ⋃ U : I, (U.1 : Set ℂ) := by
    intro z hz
    obtain ⟨U, hU, hzU, hUG⟩ :=
      (isBasis_countableBasis ℂ).exists_subset_of_mem_open (hKG hz) hGo
    exact mem_iUnion.2 ⟨⟨⟨U, hU⟩, hUG⟩, hzU⟩
  obtain ⟨t, hKt⟩ := hK.elim_finite_subcover (fun U : I => (U.1 : Set ℂ))
    (fun U => isOpen_of_mem_countableBasis U.1.2) hcover
  let s : BufferIndex := t.image Subtype.val
  have hKG' : K ⊆ basisBuffer s := by
    intro z hz
    obtain ⟨U, hUt, hzU⟩ := mem_iUnion₂.1 (hKt hz)
    exact mem_iUnion₂.2 ⟨U.1, Finset.mem_image.2 ⟨U, hUt, rfl⟩, hzU⟩
  have hsG : basisBuffer s ⊆ G := by
    intro z hz
    obtain ⟨U, hUs, hzU⟩ := mem_iUnion₂.1 hz
    obtain ⟨V, -, rfl⟩ := Finset.mem_image.1 hUs
    exact V.2 hzU
  exact ⟨s, hKG', (closure_mono hsG).trans hGO,
    hGc.of_isClosed_subset isClosed_closure (closure_mono hsG)⟩

/-- A compact set has nested buffers from one fixed countable family,
with both compact closures and the outer closure in the requested open set. -/
theorem exists_nested_basisBuffers {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ s t : BufferIndex, K ⊆ basisBuffer s ∧
      closure (basisBuffer s) ⊆ basisBuffer t ∧
      closure (basisBuffer t) ⊆ O ∧
      IsCompact (closure (basisBuffer s)) ∧ IsCompact (closure (basisBuffer t)) := by
  obtain ⟨t, hKt, htO, htc⟩ := exists_basisBuffer hK hO hKO
  obtain ⟨s, hKs, hst, hsc⟩ := exists_basisBuffer hK (isOpen_basisBuffer t) hKt
  exact ⟨s, t, hKs, hst, htO, hsc, htc⟩

end InteractingSLE.Sec5.Aux61GWord
