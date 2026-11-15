/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerOld

/-!
# Old-access equality from an ordered pair of first-visit arms

PROVE-R7-GAPEQ. Incoming-tree avoidance is a conclusion of attachment constancy. Boundary
avoidance follows from the physical pocket sides. The remaining named planar inputs are
selection of the central side and a proper unvisited third arm when the gates are distinct.
The resulting mapped equality does not assume physical endpoint equality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn

/-- **Remaining central-side selection.** The inside avoids the physical pocket boundary,
contains one pocket point, and all other pocket preimages belong to forbidden bulges. -/
def HasGateFace (W : ℝ → ℝ) (C B Γ : Set ℂ) (r : ℝ) : Prop :=
  (∀ w ∈ innerSide Γ, trMap W 0 r w ∉ frontier C) ∧
    (∃ p ∈ innerSide Γ, trMap W 0 r p ∈ C) ∧
    ∀ w ∈ H, trMap W 0 r w ∈ C → w ∉ innerSide Γ → trMap W 0 r w ∈ B

/-- **Remaining earlier proper arm.** It starts at the fresh target, is disjoint from each
incoming side except there, and is unvisited up to the terminal time. Domain membership and
all properties of its lifted third arm will be proved, rather than required here. -/
def HasProperEarlierArm (η A₁ A₂ : ℝ → ℂ) (σ : ℝ) : Prop :=
  ∃ β : ℝ → ℂ, ContinuousOn β (Ici 0) ∧ InjOn β (Ici 0) ∧ β 0 = A₁ 0 ∧
    (∀ v ∈ Ici (0 : ℝ), β v ∈ H) ∧ Tendsto (fun v => ‖β v‖) atTop atTop ∧
    (∀ t, 0 ≤ t → t < σ → ∀ v ∈ Ici (0 : ℝ), η t ≠ β v) ∧
    (∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Ici (0 : ℝ), A₁ v = β w → A₁ v = A₁ 0) ∧
    ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Ici (0 : ℝ), A₂ v = β w → A₂ v = A₁ 0

/-- A preconnected proper prefix still unvisited at `r` lies in the current domain when its
starting point does. No separate proper-arm Loewner hypothesis is necessary. -/
theorem proper_prefix_domain {W : ℝ → ℝ} {η β : ℝ → ℂ} {r : ℝ}
    (hη : IsLoewnerTrace W η) (hr : 0 ≤ r) (hβ : ContinuousOn β (Ici 0))
    (hβH : ∀ v ∈ Ici (0 : ℝ), β v ∈ H)
    (hunv : ∀ t ∈ Icc (0 : ℝ) r, ∀ v ∈ Ici (0 : ℝ), η t ≠ β v)
    (hβ0 : β 0 ∈ H \ fwdHull W r) :
    ∀ v ∈ Ici (0 : ℝ), β v ∈ H \ fwdHull W r := by
  have hD : β '' Ici 0 ⊆ H \ fwdHull W r := subset_domain_of_isPreconnected hη hr
    (isPreconnected_Ici.image _ hβ) (by rintro _ ⟨v, hv, rfl⟩; exact hβH v hv)
    (Set.disjoint_left.2 (by rintro _ ⟨v, hv, rfl⟩ ⟨t, ht, he⟩; exact hunv t ht v hv he))
    ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩ hβ0
  exact fun v hv => hD ⟨v, hv, rfl⟩

/-- Two lifted prefixes with no physical intersection except the target can meet only at
their first gate or the lifted target. Equal real gates remain distinct accesses until the
gate theorem identifies the gap endpoints. -/
theorem lifted_arms_inter {W : ℝ → ℝ} {r u₁ u₂ : ℝ} {A₁ A₂ a₁ a₂ : ℝ → ℂ} {q₁ q₂ : ℝ}
    (hW : Continuous W) (hr : 0 ≤ r)
    (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂)
    (ha₁H : ∀ v ∈ Ioc (0 : ℝ) 1, a₁ v ∈ H)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) u₁, A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) u₂, A₂ v ∈ H \ fwdHull W r)
    (hi₁ : a₁ '' Ioc 0 1 = fwdMap W r '' (A₁ '' Ico 0 u₁))
    (hi₂ : a₂ '' Ioc 0 1 = fwdMap W r '' (A₂ '' Ico 0 u₂))
    (h12 : ∀ v ∈ Ico (0 : ℝ) u₁, ∀ w ∈ Ico (0 : ℝ) u₂, A₁ v = A₂ w → A₁ v = A₁ 0) :
    a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {(q₁ : ℂ), fwdMap W r (A₁ 0)} := by
  intro w hw
  rcases eq_or_mem_open_arm ha₁0 hw.1 with he | hi
  · exact Or.inl he
  rcases eq_or_mem_open_arm ha₂0 hw.2 with he | hi'
  · have hwH : w ∈ H := by obtain ⟨v, hv, rfl⟩ := hi; exact ha₁H v hv
    rw [he] at hwH
    simp [QuantumZipper.H] at hwH
  · exact Or.inr (lift_inter_eq hW hr hD₁ hD₂ h12 (hi₁ ▸ hi) (hi₂ ▸ hi'))

/-- Boundary points of the gate face in `ℍ` lie on incoming arms, hence map to `∂C`.
This applies when an outer suffix is unvisited: no suffix hull assumption is used. -/
theorem gate_boundary_avoids_pocket {W : ℝ → ℝ} {r u₁ u₂ q₁ q₂ : ℝ}
    {A₁ A₂ a₁ a₂ : ℝ → ℂ} {C : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r) (hC : IsOpen C)
    (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) u₁, A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) u₂, A₂ v ∈ H \ fwdHull W r)
    (hi₁ : a₁ '' Ioc 0 1 = fwdMap W r '' (A₁ '' Ico 0 u₁))
    (hi₂ : a₂ '' Ioc 0 1 = fwdMap W r '' (A₂ '' Ico 0 u₂))
    (hf₁ : A₁ '' Ico 0 u₁ ⊆ frontier C) (hf₂ : A₂ '' Ico 0 u₂ ⊆ frontier C) :
    ∀ w ∈ a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂,
      w ∈ H → trMap W 0 r w ∉ C := by
  have harm : ∀ {a A : ℝ → ℂ} {q u : ℝ}, a 0 = q →
      (∀ v ∈ Ico (0 : ℝ) u, A v ∈ H \ fwdHull W r) →
      a '' Ioc 0 1 = fwdMap W r '' (A '' Ico 0 u) → A '' Ico 0 u ⊆ frontier C →
      ∀ w ∈ a '' Icc 0 1, w ∈ H → trMap W 0 r w ∉ C := by
    intro a A q u ha0 hD hi hf w hw hwH hwC
    rcases eq_or_mem_open_arm ha0 hw with he | he
    · rw [he] at hwH
      simp [QuantumZipper.H] at hwH
    · rw [hi] at he
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := he
      have hfr := hf ⟨v, hv, rfl⟩
      rw [hC.frontier_eq] at hfr
      exact hfr.2 (trMap_zero_fwdMap hW hW0 hr (hD v hv) ▸ hwC)
  rintro w ((hw | hw) | ⟨x, -, rfl⟩) hwH
  · exact harm ha₁0 hD₁ hi₁ hf₁ w hw hwH
  · exact harm ha₂0 hD₂ hi₂ hf₂ w hw hwH
  · simp [QuantumZipper.H] at hwH

end InteractingSLE.Sec7.R7GapEqCorner
