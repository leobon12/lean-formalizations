/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfJ32Slow
import InteractingSLE.Spec.Supplement.GW2BfNear

/-!
# J32's near target clause under the per-history dilation (ruling R112)

Packet PROVE-GW2-BUF. J32's sample reads `histStart + W` on its lifetime (the frozen start of `GW2BfJ32Start` and the
driver identification `J32DriverId`), where `W = (−1)^{|l|} 2^{r.2} R(· / 4^{r.2})` is ROOT2's comparison driver of
the candidate's stage. A near comparison dilated by `λ` with `λ (17/8 − S) ≤ 17/8` therefore turns every target
visit before a stop at most `λ²` times the lifetime into J31/J32's reach event (`mem_reachSet_of_scaled_target`).

* `nearLam`: the retained dilation `17/8 / (17/8 − S)` (`S = histStart`, when `S < 17/8`; else `1`);
  `nearLam_pos`, `nearLam_spec`, **`measurable_nearLam`** (a functional of the retained history);
  `histStart_nil`, **`nearLam_nil`**: at the empty history the start is `0` and the dilation is `1`;
* **`ae_read_rootJ32`**: on the gate, J32's sample reads `histStart + W` at every live rational time;
* **`ae_reach_of_scaled_visit_rootJ32`**: on the gate, a visit of `λ W` above `2 + 1/8` before a stop at most the
  lifetime gives the reach event, for every admissible `λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open Exist Staged StagedLaw Restart GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootD25

/-! ### The retained dilation -/

/-- **The near dilation of a history**: `17/8 / (17/8 − S)` when the start `S` is below `17/8`, else `1`. -/
def nearLam (S : ℝ) : ℝ := if S < 2 + 1 / 8 then (2 + 1 / 8) / (2 + 1 / 8 - S) else 1

theorem nearLam_pos (S : ℝ) : 0 < nearLam S := by
  unfold nearLam
  split_ifs with h
  · exact div_pos (by norm_num) (by linarith)
  · exact one_pos

/-- The dilation satisfies ruling R112's inequality. -/
theorem nearLam_spec {S : ℝ} (hS : S < 2 + 1 / 8) : nearLam S * (2 + 1 / 8 - S) ≤ 2 + 1 / 8 := by
  unfold nearLam
  rw [ite_eq_left hS, div_mul_cancel₀ _ (by linarith)]

theorem measurable_nearLam : Measurable nearLam := by
  unfold nearLam
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.div (measurable_const.sub measurable_id)) measurable_const

theorem nearLam_zero : nearLam 0 = 1 := by
  unfold nearLam
  rw [ite_eq_left (show (0 : ℝ) < 2 + 1 / 8 by norm_num), sub_zero, div_self (by norm_num)]

section Hist

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The retained dilation is a functional of the retained history.** -/
theorem measurable_nearLam_histStart (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : Measurable[c.sigma r l] fun ω => nearLam (histStart c r l ω) :=
  measurable_nearLam.comp (measurable_histStart c r l)

/-- At the empty history the stage start is `0`. -/
theorem histStart_nil (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (ω : Ω) : histStart c r [] ω = 0 := by
  have hT : RootJ31.historyTime c r [] = (rootEntry r.1).2 := rfl
  unfold histStart
  rw [hT, sub_self, mul_zero]

/-- **At the empty history the dilation is `1`** (ruling R112). -/
theorem nearLam_nil (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (ω : Ω) :
    nearLam (histStart c r [] ω) = 1 := by
  rw [histStart_nil, nearLam_zero]

end Hist

/-! ### The read and the target clause -/

/-- **J32's read on the gate**: at every live rational time the sample reads the retained start plus ROOT2's
comparison driver of the candidate's stage. -/
theorem ae_read_rootJ32 (h13 : Theorem13Statement.{u}) (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l))
    (hdrv : J32DriverId K Ω c r l a) :
    ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
      (RootJ32.sourceSample c r l a ξ).2 q = histStart c r l ξ +
        (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c ((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2) ξ) := by
  filter_upwards [ae_j32Start_eq_histStart h13 c r l (v0_le_historyTime c r l hord), hdrv]
    with ξ hst hd hξG q hq
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
    lt_of_le_of_lt zero_le (hq.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
  have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < GW2Sdg.rootGain c r l a ξ :=
    GW2Sdg.div_four_pow_lt r.2 (by rw [← j32Sample_fst]; exact hq)
  rw [j32Sample_snd c r l a ξ hq, hst a hlive, hd hξG _ hu]

/-- **The near target clause for J32 under a dilation**: on the gate, if the dilated comparison driver
`λ (−1)^{|l|} 2^{r.2} R(t / 4^{r.2})` is above `2 + 1/8` at a time `t` before a stop that is at most the sample's
lifetime, with `λ (17/8 − S) ≤ 17/8` (`S = histStart < 17/8`), then the sample is in the reach set. -/
theorem ae_reach_of_scaled_visit_rootJ32 (h13 : Theorem13Statement.{u}) (K : PkgFamily.{u}) (Ω : Type u)
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l))
    (hdrv : J32DriverId K Ω c r l a)
    (hcont : ∀ ξ, Continuous fun u => ((K Ω c r).inst l a).drv c u ξ) :
    ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
      histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - histStart c r l ξ) ≤ 2 + 1 / 8 →
      τ ≤ (RootJ32.sourceSample c r l a ξ).1 → (t : ℝ≥0∞) < τ →
      2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length *
        ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c (t / (4 : ℝ≥0) ^ r.2) ξ)) →
      RootJ32.sourceSample c r l a ξ ∈ reachSet := by
  filter_upwards [ae_read_rootJ32 h13 K Ω c r l a hord hdrv] with ξ hread hξG lam τ t hlam hS hscale hτ ht hvis
  have hW : Continuous fun t : ℝ≥0 => (-1 : ℝ) ^ l.length *
      ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c (t / (4 : ℝ≥0) ^ r.2) ξ) :=
    continuous_const.mul (continuous_const.mul ((hcont ξ).comp (continuous_id.div_const _)))
  exact mem_reachSet_of_scaled_target hW (hread hξG) hlam hS hscale hτ ht hvis

end InteractingSLE.Theorem14.GW2Bf
