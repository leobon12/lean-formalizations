/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermBdry
import InteractingSLE.Spec.Sec5.Aux61FibDataClock

/-!
# The clock and the driver of a simple path in the closed half-plane

Packet PROVE-RC-TERM, second run (ruling R124). `Sec5.Aux61FibData.isClockOn_chartClock_of_injOn` (Proposition 6.12
for simple paths) asks the path to be in `ℍ` at interior times. The relative chart path of an explorer that touches
the real line is only in `ℍ̄`; here the same conclusion is proved from the two driving criteria directly:

* **`isClockOn_chartClock_of_criteria`**: if `γ` is continuous and injective on `[0, U]`, in `ℍ̄`, from `0`, every
  later point `γ r` lies in the closure of the unbounded component of `ℍ ∖ γ([0, t])` (criterion (a)), and `γ` spends
  no open time interval on `ℝ` (criterion (b) for a simple path), then `chartClock γ` is a clock on `[0, U]` and a
  continuous driver from `0` has hull `fill γ([0, t])` at capacity time `chartClock γ t`.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.RealContact

namespace Term

open Restart

/-- **The relative capacity clock of a simple path in `ℍ̄` satisfying the driving criteria is a clock, and the path
generates a Loewner chain** (Proposition 6.12). -/
theorem isClockOn_chartClock_of_criteria {γ : ℝ≥0 → ℂ} {U : ℝ≥0} (hUpos : 0 < U) (hc : ContinuousOn γ (Iic U))
    (hi : InjOn γ (Iic U)) (h0 : γ 0 = 0) (hH : ∀ r ≤ U, 0 ≤ (γ r).im)
    (ha : ∀ t r : ℝ≥0, 0 < t → t < r → r ≤ U → γ r ∈ closure (H \ fillH (γ '' Icc 0 t)))
    (hR : interior {u ∈ Ioo (0 : ℝ) U | (γ u.toNNReal).im = 0} = ∅) :
    IsClockOn (chartClock γ) U ∧ ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ U →
      0 ≤ chartClock γ t ∧ QuantumZipper.fwdHull W (chartClock γ t) = fillH (γ '' Icc 0 t) := by
  set S : ℝ := (U : ℝ) with hSdef
  have hS : 0 < S := NNReal.coe_pos.2 hUpos
  have hmaps : MapsTo Real.toNNReal (Icc 0 S) (Iic U) := fun r hr => by
    simpa [hSdef] using Real.toNNReal_le_toNNReal hr.2
  have hcR : ContinuousOn (realPath γ) (Icc 0 S) := hc.comp continuous_real_toNNReal.continuousOn hmaps
  have hinj : InjOn (realPath γ) (Icc 0 S) := fun a ha' b hb hab => by
    have := hi (hmaps ha') (hmaps hb) hab
    rw [← Real.coe_toNNReal a ha'.1, ← Real.coe_toNNReal b hb.1, this]
  have hHb : MapsTo (realPath γ) (Icc 0 S) Hbar := fun r hr => hH _ (hmaps hr)
  have h0R : realPath γ 0 = 0 := by simp [realPath, h0]
  -- criterion (a)
  have hA : Sec6.DrivingCriterionA (realPath γ) S := by
    rintro t ⟨ht0, htS⟩ _ ⟨r, hr, rfl⟩
    have htn : 0 < t.toNNReal := Real.toNNReal_pos.2 ht0
    have hrn : t.toNNReal < r.toNNReal :=
      (Real.toNNReal_lt_toNNReal_iff (ht0.trans hr.1)).2 hr.1
    have hrU : r.toNNReal ≤ U := by simpa [hSdef] using Real.toNNReal_le_toNNReal hr.2
    have := ha t.toNNReal r.toNNReal htn hrn hrU
    rwa [← realPath_image_Icc γ ht0.le] at this
  have hRb : interior {u ∈ Ioo 0 S | (realPath γ u).im = 0} = ∅ := hR
  have hB : Sec6.DrivingCriterionB (realPath γ) S := Sec6.drivingCriterionB_of_injOn hinj hRb
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσK⟩ := Sec6.exists_driver_of_drivingCriteria hS hcR h0R
    (Sec6.hasSimpleApproxOn_of_injOn hS hcR hinj h0R hHb) hA hB
  -- the clock is `σ` on `[0, U]`
  have hclock : ∀ t : ℝ≥0, t ≤ U → chartClock γ t = σ t := by
    intro t ht
    have ht' : (t : ℝ) ∈ Icc 0 S := ⟨t.2, NNReal.coe_le_coe.2 ht⟩
    obtain ⟨hσt, hK, -⟩ := hσK t ht'
    rw [realPath_image_Icc γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
    have := hcap_fwdHull hW hW0 hσt
    unfold chartClock
    rw [← hK, ConformalImage.hcapSet_eq (isHPHull_fwdHull hW hσt), this]
    ring
  have hle : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (U : ℝ≥0∞) ↔ r ≤ U := fun r => ENNReal.coe_le_coe
  refine ⟨⟨by rw [hclock 0 zero_le]; exact_mod_cast hσ0, fun a ha' b hb hab => ?_, ?_,
    fun h => absurd h ENNReal.coe_ne_top⟩, W, hW, hW0, fun t ht => ?_⟩
  · have ha'' : a ≤ U := (hle a).1 ha'
    have hb' : b ≤ U := (hle b).1 hb
    rw [hclock a ha'', hclock b hb']
    exact hσm ⟨a.2, NNReal.coe_le_coe.2 ha''⟩ ⟨b.2, NNReal.coe_le_coe.2 hb'⟩ (NNReal.coe_lt_coe.2 hab)
  · refine (hσc.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨t.2, NNReal.coe_le_coe.2 ((hle t).1 ht)⟩).congr fun t ht => hclock t ((hle t).1 ht)
  · have ht' : (t : ℝ) ∈ Icc 0 S := ⟨t.2, NNReal.coe_le_coe.2 ht⟩
    obtain ⟨hσt, hK, -⟩ := hσK t ht'
    rw [realPath_image_Icc γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
    rw [hclock t ht]
    exact ⟨hσt, hK⟩

end Term

end InteractingSLE.RealContact
