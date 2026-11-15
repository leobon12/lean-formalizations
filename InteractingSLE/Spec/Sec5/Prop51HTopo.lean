/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoBounds

/-!
# The remaining contacted-excursion topology in Proposition 5.1

Prime-end limits, their western signs, compact local finiteness, boundedness in
a putative left-tip configuration, and the no-contact case are proved in the
preceding modules. The contacted case still requires an orientation and face
separation argument. `ContactedWesternExcursionStatement` records precisely that
unproved input. The final adapter is conditional on it and does not prove
`FwdNoWrapQStatement` unconditionally.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- Every finite excursion endpoint and every infinite excursion tail has a
strictly negative terminal coordinate in the counterflow chart. Shrinking the
left endpoint to a positive interior time covers excursions starting at zero. -/
def HasWesternExcursionEnds (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Prop :=
  (∀ a b : ℝ, 0 < a → a < b →
    (∀ t ∈ Ico a b, η t ∈ H \ cfHullQ w s) → η b ∉ H \ cfHullQ w s →
      ∃ x : ℝ, x < 0 ∧
        Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 (x : ℂ))) ∧
  (∀ a : ℝ, 0 ≤ a → (∀ t ∈ Ioi a, η t ∈ H \ cfHullQ w s) →
    ∃ x : ℝ, x < 0 ∧ Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x : ℂ)))

/-- The original rational barriers supply all western endpoints when the tip
misses the proper arc. -/
theorem hasWesternExcursionEnds_of_rational {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (hβs : β s ≠ 0)
    (htip : negInv (β s) ∉ arcRange η)
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η) :
    HasWesternExcursionEnds η w s := by
  constructor
  · intro a b ha hab hD hb
    refine exists_neg_tendsto_revChart_left hη hβ hw hw0 hs ha hab hD hb ?_ hbar
    intro he
    exact htip ⟨b, (ha.trans hab).le, he⟩
  · intro a ha hD
    exact exists_neg_tendsto_revChart_atTop hη hβ hw hw0 hs hβs ha hD hbar

/-- **Unproved remaining planar input**, restricted to paths that contact the
hull. Endpoint lifting and sign exclusion are already supplied by
`HasWesternExcursionEnds`; boundedness is supplied in a putative strict-left-tip
configuration. Compact local finiteness follows from the preceding modules.
What remains is to orient the physical sides of the excursions and connect the
face incident to the tip to the physical right side. This proposition is only
an explicit hypothesis of the conditional adapter below. -/
def ContactedWesternExcursionStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ),
    IsProperArc η → Continuous w → w 0 = 0 → IsLoewnerTrace w β → 0 < s →
    (∀ v : ℝ, 0 < v → β v ≠ 0) →
    (∃ t : ℝ, 0 < t ∧ η t ∈ cfHullQ w s) →
    HasWesternExcursionEnds η w s →
    IsBounded (revChart w s '' (arcRange η ∩ (H \ cfHullQ w s))) →
      negInv (β s) ∉ leftSideOf (arcRange η)

/-- Conditional completion of the exact original no-wrap statement from only
the remaining contacted-excursion separation input. The no-contact case,
endpoint limits, endpoint signs and chart boundedness are discharged here. -/
theorem fwdNoWrapQStatement_of_contactedWestern
    (hsep : ContactedWesternExcursionStatement) : FwdNoWrapQStatement := by
  intro η w β s hη hw hw0 hβ hs hnr hbar hL
  by_cases hcontact : ∃ t : ℝ, 0 < t ∧ η t ∈ cfHullQ w s
  · have hends := hasWesternExcursionEnds_of_rational hη hβ hw hw0 hs.le
      (hnr s hs) hL.1.2 hbar
    have hbound := isBounded_revChart_arcRange_of_mem_leftSideOf hη hβ hw hw0 hs.le hL
    exact hsep η w β s hη hw hw0 hβ hs hnr hcontact hends hbound hL
  · have hpre : ∀ t, 0 < t → η t ∉ cfHullQ w s :=
      fun t ht hmem => hcontact ⟨t, ht, hmem⟩
    exact negInv_notMem_leftSideOf_of_noContact_of_rational hη hβ hw hw0 hs.le
      (hnr s hs) hpre hbar hL

end InteractingSLE.Sec5.Prop51HTopo
