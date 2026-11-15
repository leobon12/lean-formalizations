/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockCap

/-!
# Inverting a relative capacity clock

Packet PROVE-RESTART-CPL5. (W8.1) reconstructs the original stopping rule in relative capacity: the continuation is
read at original time `s₀ + a⁻¹(u)`, where `a` is the relative capacity clock. For measurability in `ω` the inverse
is written as a countable supremum,

  `invClock a U₀ u = sup {q ∈ ℚ, 0 ≤ q ≤ U₀, a q < u}`,

which equals `a⁻¹(u)` whenever `a` is a clock on `[0, U₀]` (`IsClockOn`: `a 0 = 0`, continuous, strictly increasing,
unbounded if `U₀ = ∞`) and `u ≤ capLife a U₀`, the capacity lifetime (`a(U₀)`, or `∞`).

## Main results

* `IsClockOn.exists_eq`: every `u` in the capacity range is attained;
* `IsClockOn.invClock_spec`, `IsClockOn.invClock_apply`: `invClock` inverts `a`;
* `IsClockOn.strictMonoOn_invClock`, `IsClockOn.image_invClock`, `IsClockOn.continuousOn_invClock`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

/-- The inverse of a clock `a` on `[0, U₀]`, as a countable supremum. -/
def invClock (a : ℝ≥0 → ℝ) (U₀ : ℝ≥0∞) (u : ℝ≥0) : ℝ≥0 :=
  ⨆ q : ℚ, if 0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U₀ ∧ a (q : ℝ).toNNReal < u then (q : ℝ).toNNReal
    else 0

/-- The capacity lifetime of a clock on `[0, U₀]`. -/
def capLife (a : ℝ≥0 → ℝ) (U₀ : ℝ≥0∞) : ℝ≥0∞ :=
  if U₀ = ⊤ then ⊤ else ENNReal.ofReal (a U₀.toNNReal)

/-- `a` is a **clock on `[0, U₀]`**: it vanishes at `0`, is continuous and strictly increasing on `[0, U₀]`, and is
unbounded if `U₀ = ∞`. -/
structure IsClockOn (a : ℝ≥0 → ℝ) (U₀ : ℝ≥0∞) : Prop where
  zero : a 0 = 0
  strictMonoOn : StrictMonoOn a {r | (r : ℝ≥0∞) ≤ U₀}
  continuousOn : ContinuousOn a {r | (r : ℝ≥0∞) ≤ U₀}
  unbounded : U₀ = ⊤ → ∀ M : ℝ, ∃ r : ℝ≥0, M ≤ a r

namespace IsClockOn

variable {a : ℝ≥0 → ℝ} {U₀ : ℝ≥0∞} (ha : IsClockOn a U₀)
include ha

theorem nonneg {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ U₀) : 0 ≤ a r := by
  rw [← ha.zero]
  exact ha.strictMonoOn.monotoneOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ U₀ by simp) hr zero_le

omit ha in
theorem le_toNNReal {r : ℝ≥0} (hU : U₀ ≠ ⊤) (hr : (r : ℝ≥0∞) ≤ U₀) : r ≤ U₀.toNNReal := by
  simpa using ENNReal.toNNReal_mono hU hr

theorem le_capLife {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ U₀) : ENNReal.ofReal (a r) ≤ capLife a U₀ := by
  unfold capLife
  split_ifs with hU
  · exact le_top
  · exact ENNReal.ofReal_le_ofReal
      (ha.strictMonoOn.monotoneOn hr (by simp [ENNReal.coe_toNNReal hU]) (le_toNNReal hU hr))

/-- Every value in the capacity range is attained on `[0, U₀]`. -/
theorem exists_eq {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capLife a U₀) :
    ∃ r : ℝ≥0, (r : ℝ≥0∞) ≤ U₀ ∧ a r = u := by
  have hivt : ∀ R : ℝ≥0, (R : ℝ≥0∞) ≤ U₀ → (u : ℝ) ≤ a R → ∃ r : ℝ≥0, (r : ℝ≥0∞) ≤ U₀ ∧ a r = u := by
    intro R hR huR
    have hc : ContinuousOn a (Icc 0 R) :=
      ha.continuousOn.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hR
    obtain ⟨r, hr, hru⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ R) hc
      ⟨by rw [ha.zero]; exact u.2, huR⟩
    exact ⟨r, (ENNReal.coe_le_coe.2 hr.2).trans hR, hru⟩
  by_cases hU : U₀ = ⊤
  · obtain ⟨R, hR⟩ := ha.unbounded hU u
    exact hivt R (by rw [hU]; exact le_top) hR
  · have hS : ((U₀.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U₀ := by rw [ENNReal.coe_toNNReal hU]
    refine hivt _ hS ?_
    have hu' : ENNReal.ofReal u ≤ ENNReal.ofReal (a U₀.toNNReal) := by
      simpa [capLife, hU] using hu
    exact (ENNReal.ofReal_le_ofReal_iff (ha.nonneg hS)).1 hu'

/-- **`invClock` inverts the clock** on the capacity range. -/
theorem invClock_spec {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capLife a U₀) :
    (invClock a U₀ u : ℝ≥0∞) ≤ U₀ ∧ a (invClock a U₀ u) = u := by
  obtain ⟨r, hrU, hru⟩ := ha.exists_eq hu
  suffices h : invClock a U₀ u = r by rw [h]; exact ⟨hrU, hru⟩
  set f : ℚ → ℝ≥0 := fun q => if 0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U₀ ∧
    a (q : ℝ).toNNReal < u then (q : ℝ).toNNReal else 0 with hf
  have hle : ∀ q, f q ≤ r := by
    intro q
    simp only [hf]
    split_ifs with h
    · by_contra hlt
      push Not at hlt
      have := ha.strictMonoOn.monotoneOn hrU h.2.1 hlt.le
      rw [hru] at this
      exact absurd h.2.2 (not_lt.2 this)
    · exact zero_le
  have hbdd : BddAbove (range f) := ⟨r, by rintro _ ⟨q, rfl⟩; exact hle q⟩
  refine le_antisymm (ciSup_le hle) (le_of_forall_lt fun c hc => ?_)
  obtain ⟨q, hcq, hqr⟩ := exists_rat_btwn (show (c : ℝ) < r from hc)
  have hq0 : (0 : ℝ) ≤ q := c.2.trans hcq.le
  have hqr' : (q : ℝ).toNNReal < r := (Real.toNNReal_lt_iff_lt_coe hq0).2 hqr
  have hqU : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U₀ := (ENNReal.coe_le_coe.2 hqr'.le).trans hrU
  have haq : a (q : ℝ).toNNReal < u := hru ▸ ha.strictMonoOn hqU hrU hqr'
  have hfq : f q = (q : ℝ).toNNReal := by
    have hcond : (0 : ℚ) ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U₀ ∧ a (q : ℝ).toNNReal < u :=
      ⟨by exact_mod_cast hq0, hqU, haq⟩
    simp only [hf, hcond, and_self, ↓reduceIte]
  refine lt_of_lt_of_le ?_ ((hfq ▸ le_ciSup hbdd q : (q : ℝ).toNNReal ≤ ⨆ q, f q))
  exact (Real.lt_toNNReal_iff_coe_lt).2 hcq

theorem coe_toNNReal_le_capLife {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ U₀) :
    (((a r).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ capLife a U₀ := by
  exact ha.le_capLife hr

theorem invClock_apply {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ U₀) : invClock a U₀ (a r).toNNReal = r := by
  obtain ⟨hU, heq⟩ := ha.invClock_spec (ha.coe_toNNReal_le_capLife hr)
  rw [Real.coe_toNNReal _ (ha.nonneg hr)] at heq
  exact ha.strictMonoOn.injOn hU hr heq

theorem strictMonoOn_invClock : StrictMonoOn (invClock a U₀) {u | (u : ℝ≥0∞) ≤ capLife a U₀} := by
  intro u hu v hv huv
  by_contra hle
  push Not at hle
  have h := ha.strictMonoOn.monotoneOn (ha.invClock_spec hv).1 (ha.invClock_spec hu).1 hle
  rw [(ha.invClock_spec hu).2, (ha.invClock_spec hv).2] at h
  exact absurd huv (not_lt.2 (NNReal.coe_le_coe.1 h))

theorem image_invClock :
    invClock a U₀ '' {u | (u : ℝ≥0∞) ≤ capLife a U₀} = {r : ℝ≥0 | (r : ℝ≥0∞) ≤ U₀} := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ha.invClock_spec hu).1
  · intro hr
    exact ⟨_, ha.coe_toNNReal_le_capLife hr, ha.invClock_apply hr⟩

theorem continuousOn_invClock : ContinuousOn (invClock a U₀) {u | (u : ℝ≥0∞) ≤ capLife a U₀} := by
  intro u₀ hu₀
  set T₁ := {u : ℝ≥0 | (u : ℝ≥0∞) ≤ capLife a U₀} with hT₁
  set r₀ := invClock a U₀ u₀ with hr₀
  obtain ⟨hr₀U, har₀⟩ := ha.invClock_spec hu₀
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower bound: `u > a r'` for some `b < r' < r₀`
    obtain ⟨r', hbr', hr'r₀⟩ := exists_between hb
    have hr'U : (r' : ℝ≥0∞) ≤ U₀ := (ENNReal.coe_le_coe.2 hr'r₀.le).trans hr₀U
    have hlt : a r' < u₀ := har₀ ▸ ha.strictMonoOn hr'U hr₀U hr'r₀
    have hlt' : (a r').toNNReal < u₀ := (Real.toNNReal_lt_iff_lt_coe (ha.nonneg hr'U)).2 hlt
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt')] with u hu hu'
    refine lt_of_lt_of_le hbr' (le_of_not_gt fun hlt2 => ?_)
    have h := ha.strictMonoOn.monotoneOn (ha.invClock_spec hu).1 hr'U hlt2.le
    rw [(ha.invClock_spec hu).2] at h
    exact absurd ((Real.toNNReal_lt_iff_lt_coe (ha.nonneg hr'U)).1 hu') (not_lt.2 h)
  · obtain ⟨m, hr₀m, hmb⟩ := exists_between hb
    by_cases hmU : (m : ℝ≥0∞) ≤ U₀
    · have hlt : u₀ < a m := har₀ ▸ ha.strictMonoOn hr₀U hmU hr₀m
      have hlt' : u₀ < (a m).toNNReal := (Real.lt_toNNReal_iff_coe_lt).2 hlt
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt')] with u hu hu'
      refine lt_of_le_of_lt (le_of_not_gt fun hlt2 => ?_) hmb
      have h := ha.strictMonoOn.monotoneOn hmU (ha.invClock_spec hu).1 hlt2.le
      rw [(ha.invClock_spec hu).2] at h
      exact absurd ((Real.lt_toNNReal_iff_coe_lt).1 hu') (not_lt.2 h)
    · push Not at hmU
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact lt_of_lt_of_le (ENNReal.coe_lt_coe.1 (lt_of_le_of_lt (ha.invClock_spec hu).1 hmU)) hmb.le

end IsClockOn

end Restart

end InteractingSLE
