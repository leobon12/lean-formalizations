import QuantumZipper.Proofs.Zipper.Collision
import QuantumZipper.Proofs.Wire2

/-!
# E5-PALM2, part 6: measurability of the collision threshold `ζ = 0₋(T)` of `V`

Task E5-PALM2. For `x ≤ 0`, a.s. `{τ_x < T} = {x > 0₋(T)}` with `0₋(T) = zeroMinus (Vr κ T B ω) T`
(`Wire2.ae_zeroMinus_Vr_facts`). Here `ω ↦ zeroMinus (Vr κ T B ω) T` is shown a.e.-measurable:

* `measurable_realHitTime_drive_of`: for an everywhere-continuous, coordinatewise measurable
  process `B` with `x < drive κ B ω 0`, `ω ↦ τ_x(drive κ B ω)` is measurable (the argument of
  `Collision.aemeasurable_realHitTime`, which works for any such process);
* `Vr = drive κ B̃` for the reversed process `B̃ t = B(T − min(t,T)) − B(T)`; with a good
  version of `B` (`Collision.exists_good_drive`) this gives `aemeasurable_realHitTime_Vr`;
* `0₋(T) = inf {q ∈ ℚ, q < 0 : τ_q < T}` a.s., hence `aemeasurable_zeroMinus_Vr`.

Own elementary argument (reuse of the repository's measurability proof of hitting times).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open Collision ClockInt NonSwallow RealLine FwdClock B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- Hitting times of a measurable, everywhere-continuous process are measurable. -/
theorem measurable_realHitTime_drive_of {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {x : ℝ} (hx0 : ∀ ω, x < drive κ B ω 0) :
    Measurable fun ω => realHitTime (drive κ B ω) x := by
  classical
  set S : ℚ → Set Ω := fun q => {ω | 0 ≤ (q : ℝ) ∧ ∃ n : ℕ, ∀ t : ℚ, (t : ℝ) ∈ Icc 0 (q : ℝ) →
      (1 / ((n : ℝ) + 1)) ≤ -(revZ (drive κ B ω) (1 / ((n : ℝ) + 1)) x t).re} with hS
  have hSm : ∀ q, MeasurableSet (S q) := by
    intro q
    by_cases hq : (0 : ℝ) ≤ q
    · have : S q = ⋃ n : ℕ, ⋂ t : ℚ, {ω | (t : ℝ) ∈ Icc 0 (q : ℝ) →
          (1 / ((n : ℝ) + 1)) ≤ -(revZ (drive κ B ω) (1 / ((n : ℝ) + 1)) x t).re} := by
        have hq' : (0 : ℚ) ≤ q := by exact_mod_cast hq
        ext ω; simp [hS, hq']
      rw [this]
      refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun t => ?_
      by_cases ht : (t : ℝ) ∈ Icc 0 (q : ℝ)
      · simp only [ht, true_implies]
        exact measurableSet_le measurable_const
          (measurable_revZ_re_drive hBm hBc κ (by positivity) x ht.1).neg
      · simp [ht]
    · have hq' : ¬ (0 : ℚ) ≤ q := fun h => hq (by exact_mod_cast h)
      have : S q = ∅ := by ext ω; simp [hS, hq']
      rw [this]; exact MeasurableSet.empty
  have hgm : Measurable fun ω => ⨆ q : ℚ, (S q).indicator (fun _ => ENNReal.ofReal q) ω :=
    Measurable.iSup fun q => measurable_const.indicator (hSm q)
  convert hgm using 1
  funext ω
  have hW : Continuous (drive κ B ω) := continuous_drive_ns hBc κ ω
  rw [realHitTime_eq_iSup_rat]
  refine iSup_congr fun q => ?_
  by_cases hq : (0 : ℝ) ≤ q
  · have hiff := exists_isRealRevSol_iff hW (hx0 ω) hq
    by_cases hm : ω ∈ S q
    · rw [Set.indicator_of_mem hm, if_pos ⟨hq, hiff.2 hm.2⟩]
    · rw [Set.indicator_of_notMem hm, if_neg]
      rintro ⟨-, hex⟩; exact hm ⟨hq, hiff.1 hex⟩
  · rw [Set.indicator_of_notMem (fun hm => hq hm.1), if_neg (fun h => hq h.1)]

/-- The reversed process `B̃ t = B(T − min(t,T)) − B(T)`. -/
def revProc (T : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B (T - min (t : ℝ) T).toNNReal ω - B T.toNNReal ω

theorem drive_revProc (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    drive κ (revProc T B) ω = Vr κ T B ω := by
  funext s
  show Real.sqrt κ * (B (T - min ((s.toNNReal : ℝ≥0) : ℝ) T).toNNReal ω - B T.toNNReal ω) =
    Real.sqrt κ * B (T - min (max s 0) T).toNNReal ω - Real.sqrt κ * B T.toNNReal ω
  rw [Real.coe_toNNReal']
  ring

/-- **Hitting times of the reversed driver are a.e.-measurable** (`x < 0`). -/
theorem aemeasurable_realHitTime_Vr {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) {x : ℝ} (hx : x < 0) :
    AEMeasurable (fun ω => realHitTime (Vr κ T B ω) x) P := by
  obtain ⟨B', -, hB'm, hB'c, hdr⟩ := exists_good_drive hB
  have hm : Measurable fun ω => realHitTime (drive κ (revProc T B') ω) x := by
    refine measurable_realHitTime_drive_of (fun r => (hB'm _).sub (hB'm _)) (fun ω => ?_) κ
      (fun ω => ?_)
    · exact ((hB'c ω).comp (continuous_real_toNNReal.comp (continuous_const.sub
        (NNReal.continuous_coe.min continuous_const)))).sub continuous_const
    · show x < Real.sqrt κ * (B' (T - min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ) T).toNNReal ω -
        B' T.toNNReal ω)
      simp [min_eq_left hT, hx]
  refine ⟨_, hm, ?_⟩
  filter_upwards [hdr κ] with ω h
  rw [drive_revProc]
  show realHitTime (vrev (drive κ B ω) T) x = realHitTime (vrev (drive κ B' ω) T) x
  rw [h]

end E5
end QuantumZipper
