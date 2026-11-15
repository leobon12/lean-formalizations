/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjSub

/-!
# A passed test's tip is interior in the stage-1 chain of any matching driver (decision D33)

PROVE-GW2-ROOTX round 9, pathwise. **`jointShiftTip_mem_H_of_test`**: at a passed test `(l, a, q)`, for a driver `V`
with a generating trace beyond a level `σ > clock(q)` that agrees with J32's capacity reader on `[0, σ]` (e.g. a version
below its cap), and with J32's capacity reader equal to a clock `cl` up to the buffer, the stage-1 trace of `V`
(`Gm.jointShiftTip V σ (cl v₀)`) is in `ℍ` at `cl q − cl v₀`. This is the test's clause `γ q ∈ ℍ`
(`TestCross.candidateTest`) read through `jointShiftTip_mem_H_of_jointTipRead`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **A passed test's tip is interior in the stage-1 chain.** -/
theorem jointShiftTip_mem_H_of_test {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}
    {a : ℕ} {q : c.Q} {ω : Ω} (htest : ω ∈ (RootJ32.experiment c r).data.tests l a q)
    {V : ℝ≥0 → ℝ} {B : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace V B η) (hVc : Continuous V) (hV0 : V 0 = 0)
    {cl : ℝ≥0 → ℝ}
    (hcap : ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω,
      RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ω) = cl t)
    (hv₀ : (rootEntry r.1).2 ≤ RootJ31.historyTime c r l) (hmono : cl (rootEntry r.1).2 ≤ cl q)
    (hcl0 : 0 ≤ cl (rootEntry r.1).2) {σ : ℝ≥0} (hσB : (σ : ℝ≥0∞) < B) (hqσ : (cl q).toNNReal < σ)
    (hread : ∀ c' : ℝ≥0, c' ≤ σ → RootJ32.capacityDriverRead (rootPt r.1) c.s
      (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) c' (RootJ31.futurePair c r l a ω) = V c') :
    Gm.jointShiftTip V σ (cl (rootEntry r.1).2).toNNReal (cl q - cl (rootEntry r.1).2) ∈ H := by
  obtain ⟨hTq, hqF, -, -⟩ := RootJ32.test_spec c r l a q ω htest
  have htip : RootJ32.sourceTip c r l a ω ((q : ℝ≥0) : ℝ) ∈ H := htest.2.2.1
  unfold RootJ32.sourceTip at htip
  have hk : (0 : ℝ≥0) < (2 : ℝ≥0) ^ r.2 := by positivity
  rw [Real.toNNReal_coe, add_tsub_cancel_of_le hTq.le] at htip
  have hv₀q : (rootEntry r.1).2 ≤ (q : ℝ≥0) := hv₀.trans hTq.le
  have hqB : (q : ℝ≥0) ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω := hqF.le
  have hv₀B : (rootEntry r.1).2 ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω := hv₀.trans le_self_add
  have hU : RootJ31.capacityIncrement ((2 : ℝ≥0) ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
      ((q : ℝ≥0) - (rootEntry r.1).2) (RootJ31.futurePair c r l a ω) / ((2 : ℝ≥0) ^ r.2) ^ 2 =
      (cl q - cl (rootEntry r.1).2).toNNReal := by
    unfold RootJ31.capacityIncrement
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hk.ne'), add_tsub_cancel_of_le hv₀q, hcap _ hqB, hcap _ hv₀B]
  have hA₀ : (RootH29.forwardCapacity (rootPt r.1) c.s (rootEntry r.1).2 (RootJ31.futurePair c r l a ω)).toNNReal =
      (cl (rootEntry r.1).2).toNNReal := by rw [hcap _ hv₀B]
  have hA₀σ : (RootH29.forwardCapacity (rootPt r.1) c.s (rootEntry r.1).2 (RootJ31.futurePair c r l a ω)).toNNReal <
      σ := by
    rw [hA₀]
    exact lt_of_le_of_lt (Real.toNNReal_le_toNNReal hmono) hqσ
  have hu : (RootH29.forwardCapacity (rootPt r.1) c.s (rootEntry r.1).2 (RootJ31.futurePair c r l a ω)).toNNReal +
      RootJ31.capacityIncrement ((2 : ℝ≥0) ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
        ((q : ℝ≥0) - (rootEntry r.1).2) (RootJ31.futurePair c r l a ω) / ((2 : ℝ≥0) ^ r.2) ^ 2 < σ := by
    rw [hA₀, hU, ← Real.toNNReal_add hcl0 (sub_nonneg.2 hmono), add_sub_cancel]
    exact hqσ
  have h := jointShiftTip_mem_H_of_jointTipRead hη hVc.continuousOn hV0 hσB hk hA₀σ hread hu l.length htip
  rwa [hA₀, hU, Real.coe_toNNReal _ (sub_nonneg.2 hmono)] at h

end InteractingSLE.Theorem14.GW2Rj
