/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjGood

/-!
# The decoded boundaries are the clocks at the switches (decision D33)

PROVE-GW2-ROOTX round 9, pathwise. On the good set, before the contact and below the cap:

* **`trueBdX_eq_clock`**: GEOM2's decoded boundary `i ∈ [1, N]` is the root-`x` clock at the `i`-th stage time;
* **`trueBdX_mono`**: the decoded boundaries are monotone;
* `pastOf_congr_bd`: the decoded past reads the boundaries only up to its length;
* `candAngle_mem_Icc`: the candidate's angle is in `[−π/2, π/2]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Wm GW2Schedule

section Bd

variable {Ω : Type*} {x₀ : ℝ} {sp : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  {γ α : Ω → ℝ≥0 → ℂ} (hGT : ∀ ω ∈ GT, PhysGoodX x₀ sp Wα ζα W γ α ω) (hs : 0 < sp) (hx : 0 ≤ x₀)
  {V : Ω → ℝ≥0∞} {L : List (ℝ × ℝ≥0)} {N : ℕ} (hLN : L.length = N) {T : ℝ≥0}
  (hTL : schedTime 0 L N = T) (hord : Sec5.Prop513Schedule.TimeOrdered 0 L) {ω : Ω} (hω : ω ∈ GT)
  (hTc : (T : ℝ≥0∞) < contactX x₀ sp γ α ω) (hV : ENNReal.ofReal (clockX x₀ sp Wα ζα W T ω) < V ω)
include hGT hs hx hLN hTL hord hω hTc hV

/-- **The decoded boundaries are the clocks at the stage times.** -/
theorem trueBdX_eq_clock {i : ℕ} (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    trueBdX x₀ sp Wα ζα W GT V L N T ω i = (clockX x₀ sp Wα ζα W (schedTime 0 L i) ω).toNNReal := by
  have hti : schedTime 0 L i ≤ T := hTL ▸ schedTime_mono_of_timeOrdered hord hiN (hLN ▸ le_rfl)
  have htc : (schedTime 0 L i : ℝ≥0∞) < contactX x₀ sp γ α ω := (ENNReal.coe_le_coe.2 hti).trans_lt hTc
  obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hω
  have hVi : ENNReal.ofReal (clockX x₀ sp Wα ζα W (schedTime 0 L i) ω) < V ω :=
    lt_of_le_of_lt (hmono htc hTc hti) hV
  unfold trueBdX
  rw [ite_eq_right (by omega)]
  by_cases hiN' : i < N
  · rw [ite_eq_left hiN', GW2Sdo.stgStartX_eq_clockX hGT hs hx hω htc hVi]
  · rw [ite_eq_right hiN', GW2Sdo.stgStartX_eq_clockX hGT hs hx hω hTc hV]
    have : i = N := le_antisymm hiN (not_lt.1 hiN')
    rw [this, hTL]

/-- **The decoded boundaries are monotone.** -/
theorem trueBdX_mono : Monotone (trueBdX x₀ sp Wα ζα W GT V L N T ω) := by
  refine monotone_nat_of_le_succ fun i => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · unfold trueBdX
    simp only [↓reduceIte]
    exact zero_le
  by_cases hiN : i < N
  · rw [trueBdX_eq_clock hGT hs hx hLN hTL hord hω hTc hV hi hiN.le,
      trueBdX_eq_clock hGT hs hx hLN hTL hord hω hTc hV (by omega) hiN]
    have hti : schedTime 0 L (i + 1) ≤ T := hTL ▸ schedTime_mono_of_timeOrdered hord hiN (hLN ▸ le_rfl)
    have htc : (schedTime 0 L (i + 1) : ℝ≥0∞) < contactX x₀ sp γ α ω := (ENNReal.coe_le_coe.2 hti).trans_lt hTc
    have hti' : schedTime 0 L i ≤ schedTime 0 L (i + 1) :=
      schedTime_mono_of_timeOrdered hord (Nat.le_succ i) (hLN ▸ hiN)
    obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hω
    have h := hmono ((ENNReal.coe_le_coe.2 hti').trans_lt htc) htc hti'
    exact Real.toNNReal_le_toNNReal ((ENNReal.ofReal_le_ofReal_iff (RootJ32.forwardCapacity_nonneg _ _ _ _)).1 h)
  · unfold trueBdX
    rw [ite_eq_right (by omega), ite_eq_right hiN, ite_eq_right (by omega), ite_eq_right (by omega)]

end Bd

theorem pastOf_congr_bd (cf : RecData) (R : ℝ≥0 → ℝ) {b b' : ℕ → ℝ≥0} :
    ∀ n, (∀ i ≤ n, b i = b' i) → pastOf cf R b n = pastOf cf R b' n
  | 0, _ => rfl
  | n + 1, h => by
    change (pastOf cf R b n, _) = (pastOf cf R b' n, _)
    rw [pastOf_congr_bd cf R n fun i hi => h i (hi.trans (Nat.le_succ n)), h n (Nat.le_succ n),
      h (n + 1) le_rfl]

theorem candAngle_eq {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : GW2Rd.candAngle c r l a = (RootJ31.candidateAngle c r a : ℝ) :=
  RootH29.specAngle_last _ _ _ _

theorem candAngle_mem_Icc {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : GW2Rd.candAngle c r l a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  rw [candAngle_eq]
  exact Ioo_subset_Icc_self (c.hΘ (RootJ31.candidateAngle c r a).2)

end InteractingSLE.Theorem14.GW2Rj
