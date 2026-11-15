/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7SurviveActual

/-!
# Physical target adherence in a bounded pocket with two outer arms

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7, Aux. lemma 41 for pockets with two outer arms).

§5.4 (spec p. 474): "The certified `β_R` has only its unvisited incoming crosscut in `D_s`, since its remaining tail
is already in `R_s`. Global exterior avoidance puts every future active counterflow point on the left of that crosscut.
[…] For two outer arms apply this reasoning to both certified frontiers. Outer-tail bulges can remain active in `D_s`,
but they are globally forbidden and cannot contain a future retained point."

In Lean: the two clipped certified frontiers (`R7Survive.exists_closed_midBarrier` for `M₁ = β_R` and `M₂ = β_L`) are
two reverse-visited barriers in the closed pocket from the target `x₀` to the entrance `y₀`; every frontier point of the
pocket is on one of them or in the forbidden set `m(E_R) ∪ m(E_L)` (Lemma R.3, `R7StopIn.cfArc{R,L}_mem_of_outer`), and
the frontier of the forbidden set inside the closed pocket lies on the clipped frontiers. GAPEQ's
`R7Survive.target_adherence_of_barriers` (stated for any two reverse barriers) then gives physical adherence of every
allowed surviving component to the target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7LocalFace R7Survive

/-- **Every allowed surviving component of a bounded pocket with two outer arms adheres to its target.** The
forbidden set is `m(E_R) ∪ m(E_L)`, `E_R = rightSideOf (range M₁)`, `E_L = leftSideOf (range M₂)`; the barriers are the
clipped certified frontiers `M₁`, `M₂`. No reverse visit order of either wall is used. -/
theorem allowedTargetAdherence_outerOuter {R L M₁ M₂ : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (realPath R) (realPath M₁) (realPath L))
    (hO₂ : IsOrderedArcs (realPath R) (realPath M₂) (realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ)
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) :
    AllowedTargetAdherence W (cfPocket R L r)
      (negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) (cfArcR R L r 0) τ σ := by
  have hC := h.isCfPocket h0
  have hb := h.rightLo_pos h0
  obtain ⟨B₁, hB₁c, hB₁H, hB₁cl, hB₁rev, hB₁0, hB₁1, hB₁mem⟩ :=
    exists_closed_midBarrier h h0 hM₁ hO₁ hc₁R hc₁L hη.1 hrev₁
  obtain ⟨B₂, hB₂c, hB₂H, hB₂cl, hB₂rev, hB₂0, hB₂1, hB₂mem⟩ :=
    exists_closed_midBarrier h h0 hM₂ hO₂ hc₂R hc₂L hη.1 hrev₂
  obtain ⟨hF₁o, hF₁fr⟩ := forbidden_right hM₁
  obtain ⟨hF₂o, hF₂fr⟩ := forbidden_left hM₂
  have hfr : frontier (cfPocket R L r) ⊆
      (negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) ∪
        (B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1) := by
    rw [hC.frontier_eq]
    rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · rcases cfArcR_mem_of_outer h hb houterR hB₁1 hB₁mem hs with h' | h'
      exacts [Or.inl (Or.inl h'), Or.inr (Or.inl h')]
    · rcases cfArcL_mem_of_outer h hb houterL hB₂1 hB₂mem hs with h' | h'
      exacts [Or.inl (Or.inr h'), Or.inr (Or.inr h')]
  intro s hτs hsσ
  obtain ⟨hu0, -, hD, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτs hsσ hτ hσ hxf
  have hxD : B₁ 0 ∈ H \ fwdHull W s := by
    rw [hB₁0]
    exact hD 0 ⟨le_rfl, hu0⟩
  rw [← hB₁0]
  apply target_adherence_of_barriers hη hW hW0 (hτ0.trans hτs) hC.isOpen hC.isBounded
    (fun p hp => isLocConnWithin_pocket hC.isOpen hC.isConnected hC.isBounded
      (R7GapEqFin.isJordanCurve_frontier_of_isCfPocket hC) hp)
    (hF₁o.union hF₂o) hB₁c hB₂c hB₁H hB₂H hB₁cl hB₂cl hB₁rev hB₂rev (hB₂0.trans hB₁0.symm) hxD
    ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB₁1.symm⟩ ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB₂1.symm⟩ hfr
  rintro z ⟨⟨hzc, hzf⟩, hzH⟩
  rcases frontier_union_subset _ _ hzf with ⟨hz1, -⟩ | ⟨-, hz2⟩
  · exact Or.inl (hB₁mem z hzc hzH (hF₁fr z hz1 hzH))
  · exact Or.inr (hB₂mem z hzc hzH (hF₂fr z hz2 hzH))

end InteractingSLE.Sec7.Aux41OO
