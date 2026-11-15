/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstContacts

/-!
# The actual contact set of a nested current pocket

PROVE-POCKET-SIDEIN. The contact set is constructed as the closure of the
inner frontier lying in the current outer domain, in the outer coordinate.
Its closedness, separation from the relative interior and coverage of the
relative frontier are proved. Real contact ordering remains source geometry.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Current contacts are the closure of the inner boundary visible inside
the current outer domain, written in that outer chart. -/
def currentPocketContacts (outer inner : Chart) : Set ℂ :=
  closure (outer.1 '' (frontier (inner.dom : Set ℂ) ∩ (outer.dom : Set ℂ)))

/-- The interior relative frontier is exactly the outer-chart image of the
inner frontier which is still in the current outer domain. -/
theorem frontier_pocketTransitionChart {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) :
    frontier ((pocketTransitionChart outer inner).dom : Set ℂ) ∩ H =
      outer.1 '' (frontier (inner.dom : Set ℂ) ∩ (outer.dom : Set ℂ)) := by
  ext z
  constructor
  · rintro ⟨hzfr, hzH⟩
    have hpO := hO.inv_mem_dom hzH
    have hpc : ContinuousAt outer.2.1 z :=
      hO.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)
    have : NeBot (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] z) :=
      mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hzfr)
    have hpcl : outer.2.1 z ∈ closure (inner.dom : Set ℂ) :=
      mem_closure_of_tendsto (hpc.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun w hw =>
          (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).1 hw |>.2)
    have hpnot : outer.2.1 z ∉ inner.dom := by
      intro hp
      have hz := (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).2 ⟨hzH, hp⟩
      rw [(pocketTransitionChart outer inner).dom.isOpen.frontier_eq] at hzfr
      exact hzfr.2 hz
    refine ⟨outer.2.1 z, ⟨?_, hpO⟩, hO.2.2 z hzH⟩
    rw [inner.dom.isOpen.frontier_eq]
    exact ⟨hpcl, hpnot⟩
  · rintro ⟨p, ⟨hpfr, hpO⟩, rfl⟩
    have hzH := hO.fwd_mem hpO
    rw [inner.dom.isOpen.frontier_eq] at hpfr
    have : NeBot (𝓝[(inner.dom : Set ℂ)] p) :=
      mem_closure_iff_nhdsWithin_neBot.1 hpfr.1
    have hpc : ContinuousAt outer.1 p :=
      hO.differentiableOn_fwd.continuousOn.continuousAt (outer.dom.isOpen.mem_nhds hpO)
    have hzcl : outer.1 p ∈ closure ((pocketTransitionChart outer inner).dom : Set ℂ) :=
      mem_closure_of_tendsto (hpc.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun w hw => by
          rw [dom_pocketTransitionChart hO hI hCurrentInclusion]
          exact mem_image_of_mem _ hw)
    refine ⟨?_, hzH⟩
    rw [(pocketTransitionChart outer inner).dom.isOpen.frontier_eq]
    refine ⟨hzcl, fun hz => ?_⟩
    have hp := (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).1 hz |>.2
    rw [hO.inv_fwd hpO] at hp
    exact hpfr.2 hp

/-- The constructed contact set is the closure of the interior relative
frontier. The shared real side itself is not inserted into this set. -/
theorem currentPocketContacts_eq {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) :
    currentPocketContacts outer inner =
      closure (frontier ((pocketTransitionChart outer inner).dom : Set ℂ) ∩ H) := by
  rw [frontier_pocketTransitionChart hO hI hCurrentInclusion]
  rfl

/-- Closedness of the actual constructed current contacts. -/
theorem isClosed_currentPocketContacts (outer inner : Chart) :
    IsClosed (currentPocketContacts outer inner) := isClosed_closure

/-- Current contacts cannot enter the current relative interior. -/
theorem disjoint_currentPocketContacts {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) :
    Disjoint ((pocketTransitionChart outer inner).dom : Set ℂ)
      (currentPocketContacts outer inner) := by
  rw [currentPocketContacts_eq hO hI hCurrentInclusion]
  apply Disjoint.closure_right _ (pocketTransitionChart outer inner).dom.isOpen
  refine disjoint_left.2 fun z hz hzfr => ?_
  rw [(pocketTransitionChart outer inner).dom.isOpen.frontier_eq] at hzfr
  exact hzfr.1.2 hz

/-- Coverage of the interior relative frontier by the constructed contacts. -/
theorem frontier_subset_currentPocketContacts {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) :
    frontier ((pocketTransitionChart outer inner).dom : Set ℂ) ∩ H ⊆
      currentPocketContacts outer inner := by
  rw [currentPocketContacts_eq hO hI hCurrentInclusion]
  exact subset_closure

/-- Cutting both current domains by the same open ambient complement
leaves only the initial inner pocket frontier visible from the outer domain. -/
theorem currentPocketContacts_eq_initial_frontier {outer inner : Chart}
    {U O : Set ℂ} (hOo : IsOpen O) (hOuterCut : (outer.dom : Set ℂ) ⊆ O)
    (hInnerCut : (inner.dom : Set ℂ) = U ∩ O) :
    currentPocketContacts outer inner =
      closure (outer.1 '' (frontier U ∩ (outer.dom : Set ℂ))) := by
  have heq : frontier (inner.dom : Set ℂ) ∩ (outer.dom : Set ℂ) =
      frontier U ∩ (outer.dom : Set ℂ) := by
    ext p
    constructor
    · rintro ⟨hpfr, hpO⟩
      have hp : p ∈ frontier (U ∩ O) ∩ O := ⟨hInnerCut ▸ hpfr, hOuterCut hpO⟩
      rw [frontier_inter_open_inter hOo] at hp
      exact ⟨hp.1, hpO⟩
    · rintro ⟨hpfr, hpO⟩
      have hp : p ∈ frontier (U ∩ O) ∩ O := by
        rw [frontier_inter_open_inter hOo]
        exact ⟨hpfr, hOuterCut hpO⟩
      exact ⟨hInnerCut ▸ hp.1, hpO⟩
  rw [currentPocketContacts, heq]

end InteractingSLE.Sec7.PocketStopSide
