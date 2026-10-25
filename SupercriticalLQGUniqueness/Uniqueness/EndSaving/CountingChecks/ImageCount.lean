


 











import LQGMetric.Topo.Disconnect
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingChecks

open Set Metric

 
def DisconnectsPC {X : Type*} [TopologicalSpace X] (K E F : Set X) : Prop :=
  ¬ ∃ S : Set X, IsPreconnected S ∧ S ⊆ Kᶜ ∧ (S ∩ E).Nonempty ∧ (S ∩ F).Nonempty

theorem DisconnectsPC.pathHit {K E F : Set ℂ} (h : DisconnectsPC K E F) :
    LQGMetric.Disconnects K E F := by
  intro x y γ hx hy
  by_contra hne
  apply h
  refine ⟨range γ, isPreconnected_range γ.continuous, ?_, ⟨x, ⟨0, γ.source⟩, hx⟩,
    ⟨y, ⟨1, γ.target⟩, hy⟩⟩
  intro w hw hwK
  exact hne ⟨w, hw, hwK⟩

 
theorem hit_of_disconnects {K : Set ℂ} {z : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (h : DisconnectsPC K (sphere z r) (sphere z R)) {x y : ℂ} (γ : Path x y)
    (hx : x ∈ closedBall z r) (hy : y ∉ ball z R) : (range γ ∩ K).Nonempty :=
  LQGMetric.Disconnects.closedBall_compl_ball hrR h.pathHit x y γ hx hy

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingChecks

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingChecks

open Finset

 
lemma choose_mono_half {n j s : ℕ} (hjs : j ≤ s) (hs : s ≤ n / 2) :
    n.choose j ≤ n.choose s := by
  induction s, hjs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hjs ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

 
lemma card_superset_le {α : Type*} [DecidableEq α] (S B : Finset α) (k : ℕ) (hB : B ⊆ S)
    (hBk : #B ≤ k) :
    #{A ∈ S.powersetCard k | B ⊆ A} ≤ (#S).choose (k - #B) := by
  calc #{A ∈ S.powersetCard k | B ⊆ A}
      ≤ #((S \ B).powersetCard (k - #B)) := by
        refine card_le_card_of_injOn (fun A => A \ B) ?_ ?_
        · intro A hA
          simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq] at hA
          simp only [mem_coe, mem_powersetCard]
          refine ⟨sdiff_subset_sdiff hA.1.1 le_rfl, ?_⟩
          rw [card_sdiff_of_subset hA.2, hA.1.2]
        · intro A₁ h₁ A₂ h₂ heq
          simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq] at h₁ h₂
          have e₁ : A₁ = (A₁ \ B) ∪ B := (sdiff_union_of_subset h₁.2).symm
          have e₂ : A₂ = (A₂ \ B) ∪ B := (sdiff_union_of_subset h₂.2).symm
          rw [e₁, e₂]
          simp only at heq
          rw [heq]
    _ = (#S - #B).choose (k - #B) := by rw [card_powersetCard, card_sdiff_of_subset hB]
    _ ≤ (#S).choose (k - #B) := Nat.choose_le_choose _ (Nat.sub_le _ _)

 
theorem image_count {α : Type*} [DecidableEq α] (S : Finset α) (k m : ℕ)
    (Φ : Finset α → Finset α) (hk : 2 * k ≤ #S) (hmk : m ≤ k)
    (hΦsub : ∀ A ∈ S.powersetCard k, Φ A ⊆ A)
    (hΦcard : ∀ A ∈ S.powersetCard k, m ≤ #(Φ A)) :
    (#S).choose k ≤ (#S).choose (k - m) * #((S.powersetCard k).image Φ) := by
  rw [← card_powersetCard]
  refine card_le_mul_card_image _ _ ?_
  intro B hB
  obtain ⟨A₀, hA₀, rfl⟩ := mem_image.1 hB
  have hsub0 : Φ A₀ ⊆ A₀ := hΦsub A₀ hA₀
  have hA₀S : A₀ ⊆ S := (mem_powersetCard.1 hA₀).1
  have hA₀k : #A₀ = k := (mem_powersetCard.1 hA₀).2
  have hBk : #(Φ A₀) ≤ k := hA₀k ▸ card_le_card hsub0
  calc #{A ∈ S.powersetCard k | Φ A = Φ A₀}
      ≤ #{A ∈ S.powersetCard k | Φ A₀ ⊆ A} := by
        refine card_le_card ?_
        intro A hA
        simp only [mem_filter] at hA ⊢
        exact ⟨hA.1, hA.2 ▸ hΦsub A hA.1⟩
    _ ≤ (#S).choose (k - #(Φ A₀)) :=
        card_superset_le S (Φ A₀) k (hsub0.trans hA₀S) hBk
    _ ≤ (#S).choose (k - m) :=
        choose_mono_half (by have := hΦcard A₀ hA₀; omega) (by omega)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingChecks

