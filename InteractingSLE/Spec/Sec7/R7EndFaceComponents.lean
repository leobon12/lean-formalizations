/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7SurviveBarriers

/-!
# Allowed surviving components at the infinite end

PROVE-R7-GAPEQ. A bounded surviving component has an exit point on the original
frontier even when the pocket is unbounded. Proper surviving barrier tails exclude
bounded allowed components.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 R7Survive

/-- The boundedness needed in the component-exit argument is only that of the
selected component, not of the whole pocket. -/
theorem exists_frontier_adherent_of_bounded_component {C D : Set ℂ} {z : ℂ}
    (hCo : IsOpen C) (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hDb : ¬ IsBounded D) (hz : z ∈ C ∩ D)
    (hQb : IsBounded (connectedComponentIn (C ∩ D) z)) :
    ∃ p ∈ frontier C ∩ D, p ∈ closure (connectedComponentIn (C ∩ D) z) := by
  let Q := connectedComponentIn (C ∩ D) z
  have hQo : IsOpen Q := (hCo.inter hDo).connectedComponentIn
  have hQsub : Q ⊆ C ∩ D := connectedComponentIn_subset _ _
  obtain ⟨p, hp, hpcl⟩ := exists_frontier_adherent hQo hQb hDo hDc hDb
    ⟨mem_connectedComponentIn hz, hz.2⟩
  have hpQ : p ∈ closure Q := closure_mono
    (fun _ hw => (connectedComponentIn_subset _ _ hw).1) hpcl
  have hpnotQ : p ∉ Q := by
    have hpf := hp.1
    rw [hQo.frontier_eq] at hpf
    exact hpf.2
  refine ⟨p, ⟨?_, hp.2⟩, hpQ⟩
  rw [hCo.frontier_eq]
  refine ⟨closure_mono (fun _ hw => (hQsub hw).1) hpQ, fun hpC => ?_⟩
  exact hpnotQ (QuantumZipper.CA.Uniformizer.mem_cc_of_mem_closure
    (hCo.inter hDo) hpQ ⟨hpC, hp.2⟩)

/-- If every surviving barrier point has an unbounded connected tail in the surviving
closed pocket, every surviving component with an allowed point is unbounded. -/
theorem unbounded_component_of_barrier_tails {C D F K : Set ℂ} {z : ℂ}
    (hCo : IsOpen C) (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hDb : ¬ IsBounded D) (hloc : ∀ p ∈ closure C, IsLocConnWithin C p)
    (hFo : IsOpen F) (hfr : frontier C ⊆ F ∪ K)
    (hFfr : closure C ∩ frontier F ∩ D ⊆ K)
    (htails : ∀ p ∈ K ∩ D, ∃ S : Set ℂ, IsPreconnected S ∧
      S ⊆ closure C ∩ D ∧ ¬ IsBounded S ∧ p ∈ S)
    (hz : z ∈ C ∩ D) (hzF : z ∉ F) :
    ¬ IsBounded (connectedComponentIn (C ∩ D) z) := by
  intro hQb
  let Q := connectedComponentIn (C ∩ D) z
  have hzQ : z ∈ Q := mem_connectedComponentIn hz
  have hQsub : Q ⊆ C ∩ D := connectedComponentIn_subset _ _
  have hex : ∃ p ∈ K ∩ D, p ∈ closure Q := by
    by_cases hmeet : (Q ∩ F).Nonempty
    · have hn : ¬ Disjoint Q (frontier F) := by
        intro hd
        exact hzF (subset_of_isPreconnected_of_disjoint_frontier
          isPreconnected_connectedComponentIn hFo hmeet hd hzQ)
      obtain ⟨p, hpQ, hpfr⟩ := Set.not_disjoint_iff_nonempty_inter.1 hn
      have hp := hQsub hpQ
      exact ⟨p, ⟨hFfr ⟨⟨subset_closure hp.1, hpfr⟩, hp.2⟩, hp.2⟩, subset_closure hpQ⟩
    · have hd : Disjoint Q F := Set.disjoint_iff_inter_eq_empty.2
        (Set.not_nonempty_iff_eq_empty.1 hmeet)
      obtain ⟨p, hp, hpQ⟩ := exists_frontier_adherent_of_bounded_component
        hCo hDo hDc hDb hz hQb
      have hpF : p ∉ F := fun hpF => Set.disjoint_left.1 (hd.closure_left hFo) hpQ hpF
      exact ⟨p, ⟨(hfr hp.1).resolve_left hpF, hp.2⟩, hpQ⟩
  obtain ⟨p, hp, hpQ⟩ := hex
  obtain ⟨S, hS, hSsub, hSb, hpS⟩ := htails p hp
  exact hSb (hQb.closure.subset
    (subset_closure_component hDo hloc hS hSsub ⟨p, hpS, hpQ⟩))

end InteractingSLE.Sec7.R7EndFace
