/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetFrame

/-!
# G8's deterministic frame with the source's nonhitting left sector

Packet PROVE-G8-DET, ruling R63. This successor keeps the original deterministic
frame statement and adds absence of negative-real contacts before the swallow.
The old `G8DetFrameStatement` is unchanged.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC

/-- R63's successor of the deterministic core of G8: the first curve has no
negative-real contact before `σ`, as in the source's nonhitting left sector. -/
def G8DetFrameNHStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q ε : ℝ), 0 < ε →
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    (∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) →
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ u : ℝ≥0, t₀ < u → u < σ →
      α u ∈ H ∧ α u ∉ β '' Icc 0 r ∧ α u ∈ closure (activeDomain α u β r) ∧
        β r ∈ closure (activeDomain α u β r) ∧ IsFrameGap ε α u β r

namespace G8Det

/-- The no-negative-contact premise extends to the landing time since its
endpoint is a positive real `q > 1`. -/
theorem nonneg_real_le_of_before {α : ℝ≥0 → ℂ} {σ : ℝ≥0} {q : ℝ}
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) (hq : 1 < q) (hασ : α σ = q) :
    ∀ t ≤ σ, (α t).im = 0 → 0 ≤ (α t).re := by
  intro t ht him
  rcases ht.lt_or_eq with ht | rfl
  · exact hNH t ht him
  · rw [hασ, ofReal_re]
    exact zero_le_one.trans hq.le

/-- The source's nonhitting premise supplies the opposite-hull exclusion in
the exact R63 form (only contacts strictly before `σ` are constrained). -/
theorem second_tip_outside_of_no_negative_contact {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    {σ r : ℝ≥0} {q : ℝ} (hq : 1 < q) (hασ : α σ = q)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ) :
    β r ∈ H \ fillH (α '' Icc 0 σ) :=
  second_tip_outside_of_nonneg_real hcop hα0
    (nonneg_real_le_of_before hNH hq hασ) hβH hβoff

end G8Det

end InteractingSLE.RLC
