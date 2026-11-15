/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceComponents
import QuantumZipper.Proofs.Complex.UniformizerTopo

/-!
# Propagating adherence along a surviving boundary continuum

PROVE-R7-GAPEQ. Local connectivity from within makes the closure of a surviving
component relatively open on the surviving closed pocket. A connected barrier prefix
therefore propagates adherence all the way to its target endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

namespace InteractingSLE.Sec7.R7Survive

open Sec6

/-- Near an adherent point in the open ambient domain, every point of the closed
pocket adheres to the same component. -/
theorem exists_ball_closure_component {C D : Set ℂ} {z p : ℂ}
    (hDo : IsOpen D) (hpD : p ∈ D) (hloc : IsLocConnWithin C p)
    (hpQ : p ∈ closure (connectedComponentIn (C ∩ D) z)) :
    ∃ δ > 0, ball p δ ∩ closure C ⊆ closure (connectedComponentIn (C ∩ D) z) := by
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hDo p hpD
  obtain ⟨S, hS, hSc, hSN⟩ := hloc ε hε
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhdsWithin_iff.1 hSN
  obtain ⟨q, hqQ, hqd⟩ := Metric.mem_closure_iff.1 hpQ δ hδ
  have hqS : q ∈ S := hδS ⟨by rwa [mem_ball, dist_comm],
    (connectedComponentIn_subset _ _ hqQ).1⟩
  have hSQ : S ⊆ connectedComponentIn (C ∩ D) z := by
    rw [connectedComponentIn_eq hqQ]
    exact hSc.subset_connectedComponentIn hqS fun _ hw => ⟨(hS hw).1, hεD (hS hw).2⟩
  refine ⟨δ, hδ, isOpen_ball.inter_closure.trans (closure_mono ?_)⟩
  exact fun _ hw => hSQ (hδS hw)

/-- A preconnected subset of the surviving closed pocket cannot leave the closure of
one surviving component after meeting it. -/
theorem subset_closure_component {C D S : Set ℂ} {z : ℂ}
    (hDo : IsOpen D) (hloc : ∀ p ∈ closure C, IsLocConnWithin C p)
    (hS : IsPreconnected S) (hSsub : S ⊆ closure C ∩ D)
    (hne : (S ∩ closure (connectedComponentIn (C ∩ D) z)).Nonempty) :
    S ⊆ closure (connectedComponentIn (C ∩ D) z) := by
  let Q := connectedComponentIn (C ∩ D) z
  let U := interior (closure Q ∪ (closure C ∩ D)ᶜ)
  have hU : ∀ p ∈ S, p ∈ closure Q → p ∈ U := by
    intro p hp hpQ
    obtain ⟨δ, hδ, hball⟩ := exists_ball_closure_component hDo (hSsub hp).2
      (hloc p (hSsub hp).1) hpQ
    apply mem_interior_iff_mem_nhds.2
    apply Filter.mem_of_superset (Metric.ball_mem_nhds p hδ)
    intro q hq
    by_cases hqC : q ∈ closure C ∩ D
    · exact Or.inl (hball ⟨hq, hqC.1⟩)
    · exact Or.inr hqC
  intro p hp
  by_contra hpQ
  obtain ⟨q, hqS, hqQ⟩ := hne
  obtain ⟨w, hwS, hwU, hwQ⟩ := hS U (closure Q)ᶜ isOpen_interior
    isClosed_closure.isOpen_compl
    (fun v hv => by
      by_cases hvQ : v ∈ closure Q
      · exact Or.inl (hU v hv hvQ)
      · exact Or.inr hvQ)
    ⟨q, hqS, hU q hqS hqQ⟩ ⟨p, hp, hpQ⟩
  rcases interior_subset hwU with hw | hw
  · exact hwQ hw
  · exact hw (hSsub hwS)

/-- A bounded pocket component in an unbounded connected open ambient domain has
an adherent exit point on the original pocket frontier, still in that domain. -/
theorem exists_frontier_adherent {C D : Set ℂ} {z : ℂ}
    (hCo : IsOpen C) (hCb : IsBounded C) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDb : ¬ IsBounded D) (hz : z ∈ C ∩ D) :
    ∃ p ∈ frontier C ∩ D, p ∈ closure (connectedComponentIn (C ∩ D) z) := by
  let Q := connectedComponentIn (C ∩ D) z
  have hQo : IsOpen Q := (hCo.inter hDo).connectedComponentIn
  have hQsub : Q ⊆ C := fun _ hw => (connectedComponentIn_subset _ _ hw).1
  have hexit : ¬ closure Q ∩ D ⊆ Q := by
    intro hclosed
    have hDQ : D ⊆ Q := hDc.subset_of_closure_inter_subset hQo
      ⟨z, hz.2, mem_connectedComponentIn hz⟩ hclosed
    exact hDb (hCb.subset (hDQ.trans hQsub))
  obtain ⟨p, hp, hpQ⟩ := Set.not_subset.1 hexit
  have hpC : p ∉ C := fun hpC => hpQ
    (QuantumZipper.CA.Uniformizer.mem_cc_of_mem_closure (hCo.inter hDo) hp.1 ⟨hpC, hp.2⟩)
  refine ⟨p, ⟨?_, hp.2⟩, hp.1⟩
  rw [hCo.frontier_eq]
  exact ⟨closure_mono hQsub hp.1, hpC⟩

end InteractingSLE.Sec7.R7Survive
