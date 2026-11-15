/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceComponents
import InteractingSLE.Spec.Sec7.R6FcCore

/-!
# Local agreement at an unvisited shared wall

PROVE-R6-TWO, Astra §4.3 (R98). Local connectivity of the initial
pocket fixes the incident components near a common unvisited wall.
No uniqueness of a physical boundary fibre is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Ts

open Sec6

/-- Nested initial pockets locally agreeing at an active shared wall
have the same incident surviving components near that wall. Adherence
and local connectivity identify the components, including when the
force attachment elsewhere is a seed corner. -/
theorem components_agree_near_shared_wall {C P D : Set ℂ} {p o i : ℂ}
    (hPC : P ⊆ C) (hD : IsOpen D) (hpD : p ∈ D)
    (hloc : IsLocConnWithin C p)
    (hwall : ∃ r > 0, C ∩ ball p r ⊆ P)
    (hpO : p ∈ closure (connectedComponentIn (C ∩ D) o))
    (hpI : p ∈ closure (connectedComponentIn (P ∩ D) i)) :
    ∃ e > 0, connectedComponentIn (C ∩ D) o ∩ ball p e =
      connectedComponentIn (P ∩ D) i ∩ ball p e := by
  obtain ⟨r, hr, hwallr⟩ := hwall
  obtain ⟨s, hs, hsD⟩ := Metric.isOpen_iff.1 hD p hpD
  obtain ⟨S, hS, hSc, hSN⟩ := hloc (min r s) (lt_min hr hs)
  obtain ⟨e, he, heS⟩ := Metric.mem_nhdsWithin_iff.1 hSN
  have hSC : S ⊆ C ∩ D := fun z hz => ⟨(hS hz).1,
    hsD (ball_subset_ball (min_le_right _ _) (hS hz).2)⟩
  have hSP : S ⊆ P ∩ D := fun z hz => ⟨hwallr ⟨(hS hz).1,
    ball_subset_ball (min_le_left _ _) (hS hz).2⟩, (hSC hz).2⟩
  obtain ⟨zO, hzO, hzOd⟩ := Metric.mem_closure_iff.1 hpO e he
  obtain ⟨zI, hzI, hzId⟩ := Metric.mem_closure_iff.1 hpI e he
  have hzOS : zO ∈ S := heS ⟨by rwa [mem_ball, dist_comm],
    (connectedComponentIn_subset _ _ hzO).1⟩
  have hzIS : zI ∈ S := heS ⟨by rwa [mem_ball, dist_comm],
    hPC (connectedComponentIn_subset _ _ hzI).1⟩
  have hSO : S ⊆ connectedComponentIn (C ∩ D) o := by
    rw [connectedComponentIn_eq hzO]
    exact hSc.subset_connectedComponentIn hzOS hSC
  have hSI : S ⊆ connectedComponentIn (P ∩ D) i := by
    rw [connectedComponentIn_eq hzI]
    exact hSc.subset_connectedComponentIn hzIS hSP
  refine ⟨e, he, Subset.antisymm ?_ ?_⟩
  · rintro z ⟨hz, hzb⟩
    exact ⟨hSI (heS ⟨hzb, (connectedComponentIn_subset _ _ hz).1⟩), hzb⟩
  · rintro z ⟨hz, hzb⟩
    exact ⟨hSO (heS ⟨hzb, hPC (connectedComponentIn_subset _ _ hz).1⟩), hzb⟩

/-- A chart collar in a subdomain supplies adherence of its physical
landing to that subdomain. This asserts an access, with no assertion
about the other prime ends landing at the same physical point. -/
theorem landing_mem_closure_of_image_collar {O : Chart} (hO : O.IsConformal)
    {E : ℂ → ℂ} (hE : EqOn E O.2.1 H) (hEc : ContinuousOn E Hbar)
    {A : Set ℂ} (hAO : A ⊆ O.dom) {x r : ℝ} (hr : 0 < r)
    (hcollar : H ∩ ball (x : ℂ) r ⊆ O.1 '' A) : E (x : ℂ) ∈ closure A := by
  have := R6Fc.neBot_nhdsWithin_H_real x
  refine mem_closure_of_tendsto (R6Fc.tendsto_of_extension hE hEc x) ?_
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr), self_mem_nhdsWithin]
    with z hzb hzH
  obtain ⟨w, hwA, hwz⟩ := hcollar ⟨hzH, hzb⟩
  rw [← hwz, hO.inv_fwd (hAO hwA)]
  exact hwA

/-- The shared physical ball follows from an incident chart collar,
the target-component identities, and the initial shared-wall geometry.
The local inclusion is required at the chosen unvisited point, rather
than at the force landing. -/
theorem shared_ball_of_incident_collar
    {C P D : Set ℂ} {O I : Chart} {o i : ℂ}
    (hO : O.IsConformal) (hIncl : (I.dom : Set ℂ) ⊆ O.dom)
    (hOdom : (O.dom : Set ℂ) = connectedComponentIn (C ∩ D) o)
    (hIdom : (I.dom : Set ℂ) = connectedComponentIn (P ∩ D) i)
    {E : ℂ → ℂ} (hE : EqOn E O.2.1 H) (hEc : ContinuousOn E Hbar)
    {x r : ℝ} (hr : 0 < r)
    (hcollar : H ∩ ball (x : ℂ) r ⊆ O.1 '' (I.dom : Set ℂ))
    (hPC : P ⊆ C) (hD : IsOpen D) (hpD : E (x : ℂ) ∈ D)
    (hloc : IsLocConnWithin C (E (x : ℂ)))
    (hwall : ∃ s > 0, C ∩ ball (E (x : ℂ)) s ⊆ P) :
    ∃ e > 0, (O.dom : Set ℂ) ∩ ball (E (x : ℂ)) e ⊆ I.dom := by
  have hpI := landing_mem_closure_of_image_collar hO hE hEc hIncl hr hcollar
  have hpO := closure_mono hIncl hpI
  rw [hOdom] at hpO
  rw [hIdom] at hpI
  obtain ⟨e, he, heq⟩ := components_agree_near_shared_wall hPC hD hpD hloc hwall hpO hpI
  rw [← hOdom, ← hIdom] at heq
  exact ⟨e, he, fun _ hz => (heq ▸ hz).1⟩

end InteractingSLE.Sec7.R6Ts
