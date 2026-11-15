/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2EraseCompare

/-!
# Finite clock changes for SB3's relative proper completions

S5 uses elapsed physical time on the upper lift, whereas the conditional flow
uses capacity time. A continuous strictly increasing clock on a finite closed
prefix, starting at zero, extends to an order isomorphism of `ℝ≥0` by a linear
tail. Reparametrizing proper completions by this extension leaves their ranges
and Jordan sides unchanged, including at the finite endpoint.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace InteractingSLE.Theorem14.SB.Erase

/-- Retain a clock through `c` and continue with unit speed afterwards. -/
def extendClock (τ : ℝ≥0 → ℝ≥0) (c t : ℝ≥0) : ℝ≥0 :=
  τ (min t c) + (t - c)

theorem extendClock_of_le {τ : ℝ≥0 → ℝ≥0} {c t : ℝ≥0} (ht : t ≤ c) :
    extendClock τ c t = τ t := by
  rw [extendClock, min_eq_left ht, tsub_eq_zero_of_le ht, add_zero]

theorem extendClock_of_ge {τ : ℝ≥0 → ℝ≥0} {c t : ℝ≥0} (ht : c ≤ t) :
    extendClock τ c t = τ c + (t - c) := by
  rw [extendClock, min_eq_right ht]

theorem continuous_extendClock {τ : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
    (hc : ContinuousOn τ (Iic c)) : Continuous (extendClock τ c) := by
  exact (hc.comp_continuous (continuous_id.min continuous_const)
    (fun t => min_le_right t c)).add (continuous_id.sub continuous_const)

theorem strictMono_extendClock {τ : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
    (hm : StrictMonoOn τ (Iic c)) : StrictMono (extendClock τ c) := by
  intro s t hst
  rcases le_or_gt t c with ht | ht
  · rw [extendClock_of_le (hst.le.trans ht), extendClock_of_le ht]
    exact hm (hst.le.trans ht) ht hst
  rcases le_or_gt s c with hs | hs
  · rw [extendClock_of_le hs, extendClock_of_ge ht.le]
    exact (hm.monotoneOn hs (mem_Iic.2 le_rfl) hs).trans_lt
      (lt_add_of_pos_right (τ c) (tsub_pos_of_lt ht))
  · rw [extendClock_of_ge hs.le, extendClock_of_ge ht.le]
    exact add_lt_add_right (tsub_lt_tsub_right_of_le hs.le hst) (τ c)

theorem surjective_extendClock {τ : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
    (hc : ContinuousOn τ (Iic c)) (h0 : τ 0 = 0) :
    Function.Surjective (extendClock τ c) := by
  intro y
  rcases le_or_gt y (τ c) with hy | hy
  · obtain ⟨t, ht, he⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ c from zero_le)
      (hc.mono (fun _ ht => ht.2)) (show y ∈ Icc (τ 0) (τ c) by rw [h0]; exact ⟨zero_le, hy⟩)
    exact ⟨t, (extendClock_of_le ht.2).trans he⟩
  · refine ⟨c + (y - τ c), ?_⟩
    rw [extendClock_of_ge le_self_add, add_tsub_cancel_left, add_tsub_cancel_of_le hy.le]

/-- The order isomorphism extending a strictly increasing continuous finite clock.
Its proof arguments only certify this concrete extension; no clock is selected. -/
def prefixClockIso (τ : ℝ≥0 → ℝ≥0) (c : ℝ≥0)
    (hc : ContinuousOn τ (Iic c)) (hm : StrictMonoOn τ (Iic c)) (h0 : τ 0 = 0) :
    ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (extendClock τ c) (strictMono_extendClock hm)
    (surjective_extendClock hc h0)

theorem prefixClockIso_apply_of_le {τ : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
    (hc : ContinuousOn τ (Iic c)) (hm : StrictMonoOn τ (Iic c)) (h0 : τ 0 = 0)
    {t : ℝ≥0} (ht : t ≤ c) : prefixClockIso τ c hc hm h0 t = τ t :=
  extendClock_of_le ht

/-- A clock order isomorphism preserves the seed-ray closure. -/
theorem seedRayClosure_comp_orderIso (γ : ℝ≥0 → ℂ) (e : ℝ≥0 ≃o ℝ≥0) :
    seedRayClosure (γ ∘ e) = seedRayClosure γ := by
  have e0 : e 0 = 0 := e.map_bot
  unfold seedRayClosure
  rw [range_comp, e.surjective.range_eq, image_univ]
  simp only [Function.comp_apply, e0]

/-- A clock order isomorphism preserves the full closed left Jordan side. -/
theorem closedLeftSide_comp_orderIso (γ : ℝ≥0 → ℂ) (e : ℝ≥0 ≃o ℝ≥0) :
    closedLeftSide (γ ∘ e) = closedLeftSide γ := by
  have e0 : e 0 = 0 := e.map_bot
  unfold closedLeftSide
  rw [seedRayClosure_comp_orderIso]
  simp only [Function.comp_apply, e0]

/-- A clock order isomorphism preserves the full closed right Jordan side. -/
theorem closedRightSide_comp_orderIso (γ : ℝ≥0 → ℂ) (e : ℝ≥0 ≃o ℝ≥0) :
    Supp9B.closedRightSide (γ ∘ e) = Supp9B.closedRightSide γ := by
  have e0 : e 0 = 0 := e.map_bot
  unfold Supp9B.closedRightSide Supp9B.rightSide
  rw [seedRayClosure_comp_orderIso]
  simp only [Function.comp_apply, e0]

/-- Reparametrize a proper completion through a finite physical prefix. The
finite clock need only be continuous and strictly increasing on that prefix. -/
theorem isProperCompletion_comp_prefixClock {γ γ' : ℝ≥0 → ℂ} {τ : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
    (hc : ContinuousOn τ (Iic c)) (hm : StrictMonoOn τ (Iic c)) (h0 : τ 0 = 0)
    (hγ : IsProperCompletion γ (τ c) γ') :
    IsProperCompletion (γ ∘ τ) c (γ' ∘ prefixClockIso τ c hc hm h0) := by
  let e := prefixClockIso τ c hc hm h0
  refine ⟨hγ.1.comp e.continuous, hγ.2.1.comp e.injective,
    fun t => hγ.2.2.1 (e t), hγ.2.2.2.1.comp e.tendsto_atTop, ?_⟩
  intro t ht
  change γ' (prefixClockIso τ c hc hm h0 t) = γ (τ t)
  rw [prefixClockIso_apply_of_le hc hm h0 ht]
  exact hγ.2.2.2.2 (τ t) (hm.monotoneOn ht (mem_Iic.2 le_rfl) ht)

/-- Independent finite clock changes preserve ordered proper completions. The
closed endpoints are retained exactly; no terminal limiting argument is needed. -/
theorem ordered_comp_prefixClocks {α β : ℝ≥0 → ℂ} {τ σ : ℝ≥0 → ℝ≥0} {d a : ℝ≥0}
    (hτc : ContinuousOn τ (Iic d)) (hτm : StrictMonoOn τ (Iic d)) (hτ0 : τ 0 = 0)
    (hσc : ContinuousOn σ (Iic a)) (hσm : StrictMonoOn σ (Iic a)) (hσ0 : σ 0 = 0)
    (hord : HasOrderedProperCompletions α (τ d) β (σ a)) :
    HasOrderedProperCompletions (α ∘ τ) d (β ∘ σ) a := by
  obtain ⟨α', β', hα', hβ', hleft⟩ := hord
  refine ⟨_, _, isProperCompletion_comp_prefixClock hτc hτm hτ0 hα',
    isProperCompletion_comp_prefixClock hσc hσm hσ0 hβ', ?_⟩
  rw [closedLeftSide_comp_orderIso, range_comp,
    (prefixClockIso σ a hσc hσm hσ0).surjective.range_eq, image_univ]
  exact hleft

end InteractingSLE.Theorem14.SB.Erase
