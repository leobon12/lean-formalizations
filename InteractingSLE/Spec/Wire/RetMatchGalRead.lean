/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchRawWire
import InteractingSLE.Spec.Supplement.GB6HullIdRule

/-!
# The complete state read from strict past samples

The GB6 strictly lower dyadics work for the whole driving state. Unlike a
reader at the recorded lifetime, this reader also works at a positive terminal
time, using only the samples strictly before it. The value at zero is the
initial sample. On a positive record it recovers the initial state as well.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchGal

open LawUnique Restart.StoppedExtendWF
open Supp8.GB6.HullId

variable {nL nR : ℕ}

/-- The entire driving state reconstructed from samples strictly before a
positive time; at zero, the initial sample. -/
def readState (γ : HistorySpace nL nR) (t : ℝ≥0) : DrivingValue nL nR :=
  if t = 0 then γ.2 (0, 0) else limUnder atTop fun n => γ.2 (sld t n)

theorem measurable_readState (t : ℝ≥0) :
    Measurable fun γ : HistorySpace nL nR => readState γ t := by
  by_cases ht : t = 0
  · simp only [readState, ht, ↓reduceIte]
    exact (measurable_pi_apply (0, 0)).comp measurable_snd
  · simp only [readState, ht, ↓reduceIte]
    exact (StronglyMeasurable.limUnder fun n =>
      ((measurable_pi_apply (sld t n)).comp measurable_snd).stronglyMeasurable).measurable

theorem measurable_readPath : Measurable (readState (nL := nL) (nR := nR)) :=
  measurable_pi_iff.2 measurable_readState

/-- Positive prefix agreement determines the reconstructed state through the
closed prefix, including its endpoint. No path regularity is needed here. -/
theorem readState_congr {γ δ : HistorySpace nL nR} {r : ℝ≥0∞} (hr : 0 < r)
    (hag : ∀ p, (dyadicTime p : ℝ≥0∞) < r → γ.2 p = δ.2 p)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ r) : readState γ t = readState δ t := by
  by_cases ht0 : t = 0
  · simp only [readState, ht0, ↓reduceIte]
    exact hag (0, 0) (by simpa only [dyadicTime, Nat.cast_zero, zero_div,
      ENNReal.coe_zero] using hr)
  · simp only [readState, ht0, ↓reduceIte]
    congr 1
    funext n
    exact hag _ ((ENNReal.coe_lt_coe.2 (dyadicTime_sld_lt
      (lt_of_le_of_ne zero_le (Ne.symm ht0)) n)).trans_le ht)

/-- On a positive killed record of a state continuous through `t`, the strict
past reader recovers that state at `t`, including a finite terminal time. -/
theorem readState_killedHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {ω : Ω} (hV : 0 < V ω)
    (hc : Continuous (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ V ω) :
    readState (killedHistory W VL VR V ω) t =
      (W t ω, fun i => VL i t ω, fun j => VR j t ω) := by
  by_cases ht0 : t = 0
  · subst t
    simp only [readState, killedHistory, ↓reduceIte, dyadicTime, Nat.cast_zero,
      zero_div, ENNReal.coe_zero, hV]
  · simp only [readState, ht0, ↓reduceIte]
    refine Tendsto.limUnder_eq (((hc.tendsto t).comp (tendsto_dyadicTime_sld t)).congr
      fun n => ?_)
    have hn : (dyadicTime (sld t n) : ℝ≥0∞) < V ω :=
      (ENNReal.coe_lt_coe.2 (dyadicTime_sld_lt
        (lt_of_le_of_ne zero_le (Ne.symm ht0)) n)).trans_le ht
    simp only [killedHistory, hn, ↓reduceIte]
    rfl

end InteractingSLE.Wire.RetMatchGal
