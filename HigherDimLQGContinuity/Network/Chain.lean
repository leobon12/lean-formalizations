import HigherDimLQGContinuity.Network.LeadTube

/-! # Connected chains of the seven edge-network pieces -/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGContinuity

/-- A chain of seven connected pieces gives the edge network's connectivity.
The order is retained tube, lead tube, gate, chamber, gate, lead tube,
retained tube. -/
theorem connected_seven_chain {α : Type*} [TopologicalSpace α]
    (R₀ L₀ G₀ Ch G₁ L₁ R₁ : Set α)
    (hR₀ : IsConnected R₀) (hL₀ : IsConnected L₀)
    (hG₀ : IsConnected G₀) (hCh : IsConnected Ch)
    (hG₁ : IsConnected G₁) (hL₁ : IsConnected L₁)
    (hR₁ : IsConnected R₁)
    (hRL₀ : (R₀ ∩ L₀).Nonempty)
    (hLG₀ : (L₀ ∩ G₀).Nonempty)
    (hGC₀ : (G₀ ∩ Ch).Nonempty)
    (hCG₁ : (Ch ∩ G₁).Nonempty)
    (hGL₁ : (G₁ ∩ L₁).Nonempty)
    (hLR₁ : (L₁ ∩ R₁).Nonempty) :
    IsConnected (R₀ ∪ L₀ ∪ G₀ ∪ Ch ∪ G₁ ∪ L₁ ∪ R₁) := by
  have h01 : IsConnected (R₀ ∪ L₀) := IsConnected.union hRL₀ hR₀ hL₀
  have h02 : IsConnected ((R₀ ∪ L₀) ∪ G₀) :=
    IsConnected.union (by
      obtain ⟨x, hxL, hxG⟩ := hLG₀
      exact ⟨x, Or.inr hxL, hxG⟩) h01 hG₀
  have h03 : IsConnected (((R₀ ∪ L₀) ∪ G₀) ∪ Ch) :=
    IsConnected.union (by
      obtain ⟨x, hxG, hxC⟩ := hGC₀
      exact ⟨x, Or.inr hxG, hxC⟩) h02 hCh
  have h04 : IsConnected ((((R₀ ∪ L₀) ∪ G₀) ∪ Ch) ∪ G₁) :=
    IsConnected.union (by
      obtain ⟨x, hxC, hxG⟩ := hCG₁
      exact ⟨x, Or.inr hxC, hxG⟩) h03 hG₁
  have h05 : IsConnected (((((R₀ ∪ L₀) ∪ G₀) ∪ Ch) ∪ G₁) ∪ L₁) :=
    IsConnected.union (by
      obtain ⟨x, hxG, hxL⟩ := hGL₁
      exact ⟨x, Or.inr hxG, hxL⟩) h04 hL₁
  have h06 : IsConnected ((((((R₀ ∪ L₀) ∪ G₀) ∪ Ch) ∪ G₁) ∪ L₁) ∪ R₁) :=
    IsConnected.union (by
      obtain ⟨x, hxL, hxR⟩ := hLR₁
      exact ⟨x, Or.inr hxL, hxR⟩) h05 hR₁
  simpa only [union_assoc] using h06

/-- A finite family of connected sets all containing one point remains
connected after adjoining that point. -/
theorem connected_union_of_common_point {α ι : Type*} [TopologicalSpace α]
    (p : α) (F : Finset ι) (B : ι → Set α)
    (hB : ∀ i ∈ F, IsConnected (B i))
    (hp : ∀ i ∈ F, p ∈ B i) :
    IsConnected ({p} ∪ ⋃ i ∈ F, B i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simpa using isConnected_singleton (x := p)
  | @insert i T hi ih =>
      have hT : ∀ j ∈ T, IsConnected (B j) := by
        intro j hj
        exact hB j (Finset.mem_insert_of_mem hj)
      have hpT : ∀ j ∈ T, p ∈ B j := by
        intro j hj
        exact hp j (Finset.mem_insert_of_mem hj)
      have hprev := ih hT hpT
      have hmeet : (({p} ∪ ⋃ j ∈ T, B j) ∩ B i).Nonempty :=
        ⟨p, Or.inl rfl, hp i (Finset.mem_insert_self _ _)⟩
      have hnew := IsConnected.union hmeet hprev
        (hB i (Finset.mem_insert_self _ _))
      simpa only [Finset.set_biUnion_insert, union_assoc,
        union_left_comm, union_comm] using hnew

end HigherDimLQGContinuity
