/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4BarrierSelf

/-!
# GW4's walk leaves: the contact order from the counterflow's reverse first visits

Packet PROVE-T14-GW4REG. Theorem GW4's proof (`source/spec/p625-671.md` L235, p. 637): "Every common contact is
ordered the same way on the two walks, because their first visits by `η` have strict reverse order on both." This
file proves that sentence deterministically and wires it:

* `contactOrder_of_reverseVisits`: two injective flows from `0` whose points (after `0`) are first visited by `γ` in
  strict reverse order meet in the same order along both;
* `reverseVisits_of_range_eq`: strict reverse first visits do not depend on the parametrization of a complete simple
  flow;
* **`walkContactOrderRegStatement_of_wallOrder`**: `GW4BarrierSelf.WalkContactOrderRegStatement` from
  `GW4BarrierSelf.CounterflowWallOrderRegStatement` and Theorem 1.3 (which supplies a generating trace).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW4Traverse GW4Ident GW4Reg GW4BarrierSelf

/-- **Strict reverse first visits** of the points of a flow `α` after `α 0` by the counterflow trace `γ`. -/
def ReverseVisits (γ α : ℝ≥0 → ℂ) : Prop :=
  ∀ s s' : ℝ≥0, 0 < s → s < s' → GB11.firstVisit γ (α s') < GB11.firstVisit γ (α s)

/-- One direction of the contact order. -/
theorem lt_of_lt_of_reverseVisits {γ α β : ℝ≥0 → ℂ} (hα : Function.Injective α) (hβ : Function.Injective β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (hVα : ReverseVisits γ α) (hVβ : ReverseVisits γ β) {s s' t t' : ℝ≥0}
    (h₁ : α s = β t) (h₂ : α s' = β t') (hss : s < s') : t < t' := by
  have hs'0 : 0 < s' := lt_of_le_of_lt zero_le hss
  have ht'0 : t' ≠ 0 := by
    rintro rfl
    rw [hβ0, ← hα0] at h₂
    exact (ne_of_gt hs'0) (hα h₂)
  rcases eq_zero_or_pos s with rfl | hs0
  · have ht0 : t = 0 := hβ (by rw [← h₁, hα0, hβ0])
    rw [ht0]
    exact pos_iff_ne_zero.2 ht'0
  · have hv := hVα s s' hs0 hss
    rw [h₁, h₂] at hv
    rcases lt_trichotomy t t' with h | h | h
    · exact h
    · rw [h] at hv
      exact absurd hv (lt_irrefl _)
    · exact absurd (hVβ t' t (pos_iff_ne_zero.2 ht'0) h) (not_lt.2 hv.le)

/-- **The contact order from reverse first visits** (GW4's proof, p. 637): two injective flows from `0` whose points
after `0` are first visited by `γ` in strict reverse order meet in the same order along both. -/
theorem contactOrder_of_reverseVisits {γ αR αL : ℝ≥0 → ℂ} (hR : Function.Injective αR)
    (hL : Function.Injective αL) (hR0 : αR 0 = 0) (hL0 : αL 0 = 0) (hVR : ReverseVisits γ αR)
    (hVL : ReverseVisits γ αL) :
    ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t') := fun _ _ _ _ h₁ h₂ =>
  ⟨lt_of_lt_of_reverseVisits hR hL hR0 hL0 hVR hVL h₁ h₂,
    lt_of_lt_of_reverseVisits hL hR hL0 hR0 hVL hVR h₁.symm h₂.symm⟩

/-- **Reverse first visits do not depend on the parametrization** of a complete simple flow. -/
theorem reverseVisits_of_range_eq {γ α α' : ℝ≥0 → ℂ} (hα : GB11.IsCompleteSimpleFlow α)
    (hα' : GB11.IsCompleteSimpleFlow α') (hr : range α = range α') (hV : ReverseVisits γ α') :
    ReverseVisits γ α := by
  obtain ⟨φ, -, hφm, hφ0, hφ⟩ := exists_strictMono_comp_eq hα' hα hr
  intro s s' hs hss
  have h1 : 0 < φ s := by rw [← hφ0]; exact hφm hs
  have h2 := hV (φ s) (φ s') h1 (hφm hss)
  rwa [hφ, hφ] at h2

/-- **The contact order of the two walks** (`GW4BarrierSelf.WalkContactOrderRegStatement`) from the counterflow's
strict reverse first visits of both walks (`GW4BarrierSelf.CounterflowWallOrderRegStatement`) and Theorem 1.3 (a
generating trace of the counterflow exists almost surely). -/
theorem walkContactOrderRegStatement_of_wallOrder (h13 : Exist.Theorem13Statement.{u})
    (hVO : CounterflowWallOrderRegStatement.{u}) : WalkContactOrderRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hVO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ'] with ω hV htr
  intro αR αL hrR hrL hfR hfL
  obtain ⟨-, -, γ, hγ, -⟩ := htr
  obtain ⟨hVR, hVL⟩ := hV αR αL hrR hrL hfR hfL γ hγ
  exact contactOrder_of_reverseVisits hfR.2.1 hfL.2.1 hfR.2.2.1 hfL.2.2.1 hVR hVL

end GW4Leaf

end Theorem14

end InteractingSLE
