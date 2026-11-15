/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11FaceLift

/-!
# GB11: construction of the current Jordan face from its lifted walls

The generalized two-wall boundary allows extra real contacts. GB11's proved
Carathéodory correspondence and Janiszewski connectivity identify the current domain
with the component of this boundary. The remaining input consists of the lifted
incoming wall arcs, their gate intersections, and the boundary covering property.
It is explicitly recorded as an unproved input, not as a source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- Compactified incoming wall data at a fixed ambient time. Extra real contacts
are permitted, but the incident base meets each wall only at its own gate.
The last three fields express the source's boundary identification by lifted arcs. -/
structure CurrentGateBoundary (W : ℝ → ℝ) (C : Set ℂ) (t : ℝ) where
  qR : ℝ
  qL : ℝ
  junction : ℂ
  rightWall : ℝ → ℂ
  leftWall : ℝ → ℂ
  gates_le : qR ≤ qL
  right_continuous : ContinuousOn rightWall (Icc 0 1)
  left_continuous : ContinuousOn leftWall (Icc 0 1)
  right_injective : InjOn rightWall (Icc 0 1)
  left_injective : InjOn leftWall (Icc 0 1)
  right_zero : rightWall 0 = mu qR
  left_zero : leftWall 0 = mu qL
  right_one : rightWall 1 = junction
  left_one : leftWall 1 = junction
  wall_inter : rightWall '' Icc 0 1 ∩ leftWall '' Icc 0 1 ⊆ {rightWall 0, junction}
  right_base : rightWall '' Icc 0 1 ∩ gateBase qR qL ⊆ {rightWall 0}
  left_base : leftWall '' Icc 0 1 ∩ gateBase qR qL ⊆ {leftWall 0}
  right_outside : Disjoint (rightWall '' Icc 0 1) (mu '' ownDomain W C t)
  left_outside : Disjoint (leftWall '' Icc 0 1) (mu '' ownDomain W C t)
  frontier_subset : frontier (mu '' ownDomain W C t) ⊆
    rightWall '' Icc 0 1 ∪ leftWall '' Icc 0 1 ∪ gateBase qR qL

/-- The explicit boundary made from the two compactified walls and their real base. -/
def CurrentGateBoundary.boundary {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) : Set ℂ :=
  b.rightWall '' Icc 0 1 ∪ b.leftWall '' Icc 0 1 ∪ gateBase b.qR b.qL

/-- The walls and the incident real base form a Jordan curve even when the walls
have further original-real contacts. -/
theorem CurrentGateBoundary.isJordanCurve {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) : LQGMetric.JordanMap.IsJordanCurve b.boundary :=
  isJordanCurve_walls_gateBase b.gates_le b.right_continuous b.left_continuous
    b.right_injective b.left_injective b.right_zero b.left_zero b.right_one b.left_one
    b.wall_inter b.right_base b.left_base

/-- The constructed boundary is disjoint from the current open domain. -/
theorem CurrentGateBoundary.disjoint_domain {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) : Disjoint b.boundary (mu '' ownDomain W C t) :=
  (b.right_outside.union_left b.left_outside).union_left
    (gateBase_disjoint_ownDomain W C t b.qR b.qL)

/-- The open connected current domain is the selected Jordan component bounded by
its two walls and real base. This constructs the face, rather than assuming it. -/
theorem isCurrentJordanFace_of_gateBoundary {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (hOo : IsOpen (ownDomain W C t)) (hOc : IsConnected (ownDomain W C t))
    (b : CurrentGateBoundary W C t) : IsCurrentJordanFace W C t := by
  obtain ⟨hFo, hFc⟩ := isOpen_isConnected_mu_ownDomain hOo hOc
  obtain ⟨p, hp⟩ := hFc.nonempty
  have hdis : ∀ z ∈ mu '' ownDomain W C t, z ∉ b.boundary := fun z hz hzb =>
    b.disjoint_domain.le_bot ⟨hzb, hz⟩
  exact ⟨b.boundary, b.isJordanCurve, p, hdis p hp,
    eq_connectedComponentIn_of_frontier_subset hFo hFc.isPreconnected hp hdis
      b.frontier_subset⟩

/-- **Unproved lifting input:** existence of the simple incoming wall lifts and their
boundary covering data. The actual Jordan construction and component selection are proved. -/
def GB11CurrentGateBoundaryStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      Nonempty (CurrentGateBoundary (fun r : ℝ => W' r.toNNReal) C t)


/-- GB11's current Jordan face from the primitive wall-lifting input. Connectivity
uses the already proved chart boundary correspondence, with no extra real-contact premise. -/
theorem gb11CurrentJordanFaceStatement_of_gateBoundary
    (hgate : GB11CurrentGateBoundaryStatement) : GB11CurrentJordanFaceStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD t hτt ht
  obtain ⟨b⟩ := hgate W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC
    hE hTr hD t hτt ht
  obtain ⟨e, rR, rL, hbc⟩ := gb11ChartBdryStatement W' γ hW' hW'0 hγ hno αR αL hB hP
    C hC s₁ t₁ s₂ t₂ hs c hc hxC
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hB.1)
    (isClosed_range_of_isCompleteSimpleFlow hB.2.1) hC
  have hW : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => W' r.toNNReal) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hW'0
  exact isCurrentJordanFace_of_gateBoundary
    (isOpen_ownDomain (isLoewnerTrace_of_isGeneratingTrace hγ) hW hW0 t.2 hCo hCH)
    (isConnected_ownDomain_of_pocket hW' hW'0 hγ hB hs hc hCo hCH hxC hbc hτt ht) b

/-- Continuous relative own futures once the source's incoming wall lifts are constructed. -/
theorem gb11RelOwnFutureStatement_of_gateBoundary
    (hgate : GB11CurrentGateBoundaryStatement) : GB11RelOwnFutureStatement :=
  gb11RelOwnFutureStatement_of_currentJordanFace
    (gb11CurrentJordanFaceStatement_of_gateBoundary hgate)

/-- The relative parametrization once the source's incoming wall lifts are constructed. -/
theorem gb11RelParamStatement_of_gateBoundary
    (hgate : GB11CurrentGateBoundaryStatement) : GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_currentJordanFace
    (gb11CurrentJordanFaceStatement_of_gateBoundary hgate)

end InteractingSLE.Theorem14.GB11Chart
