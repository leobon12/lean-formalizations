/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceEnd
import InteractingSLE.Spec.Sec7.R7EndFaceActual
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# The physical component selected by the infinite end

PROVE-R7-GAPEQ. The actual infinite-end pocket has exactly one unbounded surviving
component. Every allowed surviving point belongs to it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- The actual pocket at infinity is unbounded already from its proper frontier. -/
theorem not_isBounded_cfPocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) :
    ¬ IsBounded (cfPocket R L r) := by
  have hC := h.isCfPocketInf h0
  intro hb
  apply not_isBounded_image_of_tendsto
    (tendsto_norm_atTop_iff_cobounded.1 hC.tendsto₁) (Ici_mem_atTop (0 : ℝ))
  exact hb.closure.subset fun z hz => frontier_subset_closure
    (by rw [hC.frontier_eq]; exact Or.inl hz)

/-- The ambient Loewner domain contains all sufficiently distant pocket points. -/
theorem domain_contains_far_pocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ}
    (h : IsChangeConfigInc R L r) (hW : Continuous W) (s : ℝ) :
    ∃ ρ : ℝ, ∀ z ∈ cfPocket R L r, ρ < ‖z‖ → z ∈ H \ fwdHull W s := by
  obtain ⟨ρ, hρ⟩ := (InteractingSLE.isBounded_fwdHull hW s).exists_norm_le
  exact ⟨ρ, fun z hz hnorm =>
    ⟨PocketJordan.image_negInv_subset_H h.changePocket_subset_H hz,
      fun hzK => (not_le.2 hnorm) (hρ z hzK)⟩⟩

/-- There is an unbounded component and every other unbounded surviving component
equals it. The displayed point is only a representative of that component. -/
theorem exists_unbounded_component {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {D : Set ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hfar : ∃ ρ : ℝ, ∀ z ∈ cfPocket R L r, ρ < ‖z‖ → z ∈ D) :
    ∃ p ∈ cfPocket R L r ∩ D,
      ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ D) p) ∧
      ∀ q : ℂ, ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ D) q) →
        connectedComponentIn (cfPocket R L r ∩ D) q =
          connectedComponentIn (cfPocket R L r ∩ D) p := by
  obtain ⟨ρ, hρ⟩ := hfar
  obtain ⟨S, hS, hSc, T, hT⟩ := exists_preconnected_far_neighborhood h h0 ρ
  have hSb : ¬ IsBounded S := by
    intro hb
    apply not_isBounded_cfPocket h h0
    apply (hb.union (isBounded_closedBall (x := (0 : ℂ)) (r := T))).subset
    intro z hz
    by_cases hzT : T ≤ ‖z‖
    · exact Or.inl (hT z hz hzT)
    · exact Or.inr (mem_closedBall_zero_iff.2 (le_of_not_ge hzT))
  obtain ⟨p, hpS, -⟩ := exists_norm_gt_of_not_isBounded hSb 0
  have hSsub : S ⊆ cfPocket R L r ∩ D := fun _ hz => ⟨(hS hz).1, hρ _ (hS hz).1 (hS hz).2⟩
  have hpQ : ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ D) p) :=
    fun hb => hSb (hb.subset (hSc.subset_connectedComponentIn hpS hSsub))
  exact ⟨p, hSsub hpS, hpQ, fun q hq => component_eq_of_unbounded h h0 ⟨ρ, hρ⟩ hq hpQ⟩

/-- Every allowed point belongs to any chosen unbounded component. This converts
the proved unboundedness assertion into physical face selection. -/
theorem allowed_mem_unbounded_component {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ}
    {F : Set ℂ} {τ s : ℝ} {p : ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hW : Continuous W)
    (hallowed : AllowedUnboundedComponents W (cfPocket R L r) F τ) (hτs : τ ≤ s)
    (hp : ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p)) :
    ∀ z ∈ cfPocket R L r ∩ (H \ fwdHull W s), z ∉ F →
      z ∈ connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p := by
  intro z hz hzF
  rw [← component_eq_of_unbounded h h0 (domain_contains_far_pocket h hW s)
    (hallowed s hτs z hz hzF) hp]
  exact mem_connectedComponentIn hz

/-- The physical infinite-end component exists without any gate choice and contains
every allowed surviving pocket point. -/
theorem exists_allowed_component {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ}
    {F : Set ℂ} {τ s : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hW : Continuous W)
    (hallowed : AllowedUnboundedComponents W (cfPocket R L r) F τ) (hτs : τ ≤ s) :
    ∃ p ∈ cfPocket R L r ∩ (H \ fwdHull W s),
      ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      ∀ z ∈ cfPocket R L r ∩ (H \ fwdHull W s), z ∉ F →
        z ∈ connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p := by
  obtain ⟨p, hp, hpb, -⟩ := exists_unbounded_component h h0 (domain_contains_far_pocket h hW s)
  exact ⟨p, hp, hpb, allowed_mem_unbounded_component h h0 hW hallowed hτs hpb⟩

end InteractingSLE.Sec7.R7EndFace
