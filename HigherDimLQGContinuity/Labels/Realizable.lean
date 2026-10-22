import HigherDimLQGContinuity.Labels.LabelCutoffs
import HigherDimLQGContinuity.Topology.Junction

/-!
# Deterministic realizability of finite site labels

Realizability records an arc witnessing the geometric predicates of a label.
It depends only on the fixed label and site data, not on a random field.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- The exact geometric witness required for an edge label. -/
def EdgeLabel.IsRealizable {d : ℕ} (S : SiteData d) (e : S.Edge)
    {Kc Kl N : ℕ} {μ ν r c₁ : ℝ}
    (E : EdgeLabel S e Kc Kl N μ ν r c₁) (A α β t₀ : ℝ) : Prop :=
  ∃ γ : ℝ → Rd d,
    Topology.ArcModuli γ A α β ∧
    (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S.seedK e E.1.trial) ∧
    CoveredHit μ (S.edgeCenter e) (labelCellIndices E.1.chamber) (γ '' Icc 0 1) ∧
    CoveredHit μ (S.edgeCenter e) (labelCellIndices E.1.gate0) (γ '' Icc 0 (2 * t₀)) ∧
    CoveredHit μ (S.edgeCenter e) (labelCellIndices E.1.gate1)
      (γ '' Icc (1 - 2 * t₀) 1) ∧
    (∀ x ∈ E.1.lead0.trace ν, ∀ t ∈ Icc t₀ 1, r ≤ dist x (γ t)) ∧
    (∀ x ∈ E.1.lead1.trace ν, ∀ t ∈ Icc 0 (1 - t₀), r ≤ dist x (γ t)) ∧
    dist (E.1.lead0.point ν E.1.lead0.last) (γ 0) ≤ d * ν ∧
    dist (E.1.lead1.point ν E.1.lead1.last) (γ 1) ≤ d * ν

/-- A site label is realizable if each of its edge labels has a deterministic
geometric witness. -/
def IsRealizable {d : ℕ} (S : SiteData d) {Kc Kl N : ℕ}
    {μ ν r c₁ : ℝ} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (A α β t₀ : ℝ) : Prop :=
  ∀ e : S.Edge, EdgeLabel.IsRealizable S e (ℓ e) A α β t₀

/-- The bridge used by source-label construction: assemble the supplied arc
witnesses into realizability of the finite site label. -/
theorem isRealizable_of_edge_witnesses {d : ℕ} (S : SiteData d)
    {Kc Kl N : ℕ} {μ ν r c₁ : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) {A α β t₀ : ℝ}
    (γ : ∀ _ : S.Edge, ℝ → Rd d)
    (hmod : ∀ e, Topology.ArcModuli (γ e) A α β)
    (hseed : ∀ e : S.Edge, ∀ t, t ∈ Icc (0 : ℝ) 1 → γ e t ∈ S.seedK e (ℓ e).1.trial)
    (hchamber : ∀ e, CoveredHit μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) (γ e '' Icc 0 1))
    (hgate0 : ∀ e, CoveredHit μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.gate0) (γ e '' Icc 0 (2 * t₀)))
    (hgate1 : ∀ e, CoveredHit μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.gate1) (γ e '' Icc (1 - 2 * t₀) 1))
    (hclear0 : ∀ e x, x ∈ (ℓ e).1.lead0.trace ν →
      ∀ t ∈ Icc t₀ 1, r ≤ dist x (γ e t))
    (hclear1 : ∀ e x, x ∈ (ℓ e).1.lead1.trace ν →
      ∀ t ∈ Icc 0 (1 - t₀), r ≤ dist x (γ e t))
    (hattach0 : ∀ e, dist ((ℓ e).1.lead0.point ν (ℓ e).1.lead0.last) (γ e 0) ≤ d * ν)
    (hattach1 : ∀ e, dist ((ℓ e).1.lead1.point ν (ℓ e).1.lead1.last) (γ e 1) ≤ d * ν) :
    IsRealizable S ℓ A α β t₀ := by
  intro e
  exact ⟨γ e, hmod e, hseed e, hchamber e, hgate0 e, hgate1 e,
    hclear0 e, hclear1 e, hattach0 e, hattach1 e⟩

/-- Membership in the catalogue is automatic once the geometric code has
been constructed. -/
theorem siteLabel_mem_catalogue {d : ℕ} (S : SiteData d)
    {Kc Kl N : ℕ} {μ ν r c₁ : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) :
    ℓ ∈ labelCatalogue S Kc Kl N μ ν r c₁ := by
  classical
  simp [labelCatalogue]

end HigherDimLQGContinuity
