/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC17ContextFrame
import InteractingSLE.Spec.Sec7.ColCovTop

/-! # The complete R100 source data, with their chart exposed

PROVE-SIDE-COLLAR2. This proves the relifted source contract. The landed
`ColCovSourceInput` fixes the principal chart inside its source predicate,
so it cannot consume this relift without a successor of that interface.
No existing declaration or theorem statement is changed here.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC17
open Wire Wire.Current LocalSets WholeField PocketWordIn PhaseSel PocketStopSide

/-- Constant preliminary side data at offset zero. The reference installer
supplies the actual reference sets, records, lifts and phase afterwards. -/
def zeroFramePreSide (Ω : Type) : Late.SideData Ω where
  level := 0
  sets := fun _ _ => ∅
  info := fun _ => ⊥
  lift := fun _ _ _ => 0
  phase := fun _ _ => 0
  offset := 0
  probe := fun _ _ _ => 0
  baseProbe := fun _ _ _ => 0
  weight := fun _ _ _ => 0
  visit := fun _ _ => 0
  event := fun _ => ∅
  currentMean := fun _ _ _ => 0
  referenceMean := fun _ _ _ => 0

/-- R100's complete source input in every physical word context, with
the relift explicitly installed in the source chart. Offset and lattice
index are zero; the normalized source branch is one and `b = 0`.
This is not a proof of the principal-chart `ColCovSourceInput`. -/
theorem colCovSourceInput_zeroFrame :
    ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
      (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
      (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
      (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow),
      let d := wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)
      ∃ (pre : SideTest (Ωw index) → Late.SideData (Ωw index))
        (offsetIndex : SideTest (Ωw index) → ℤ)
        (G₀ : SideTest (Ωw index) → Ωw index → DistOn upperHalfPlaneOpens)
        (n : SideTest (Ωw index) → Ωw index → ℤ),
        (∀ j, (pre j).offset = 0 ∧ offsetIndex j = 0 ∧
          (pre j).offset = (offsetIndex j : ℝ) * phaseStep (16 / (16 / index.kappa))) ∧
        (∀ j, j.Ready d → Measurable[(j.target index d).walls] (n j)) ∧
        InitialPocketConjugateFlowMeanWithChart index d
          (fun j ω => zeroFrameChart ((j.target index d).baseChart ω) (n j ω)) G₀
          (fun j => j.canonicalInitialFlowMean index d) (fun _ _ => 1) (fun _ => 0) ∧
        ∀ j, j.Ready d → ∀ᵐ ω ∂d.measure, ω ∈ (j.target index d).event →
          (pre j).offset = 0 + 2 * π * chiC (16 / index.kappa) * (1 - ((1 : ℤ) : ℝ)) := by
  intro Ωw _ _ baseWord _ hWordb hC index d
  obtain ⟨G₀, n, hn, hSource, _⟩ := hC.exists_zeroFrame_initial_mean index
  refine ⟨fun _ => zeroFramePreSide (Ωw index), fun _ => 0, G₀, n, ?_, hn, hSource, ?_⟩
  · intro j
    exact ⟨rfl, rfl, by simp only [zeroFramePreSide, Int.cast_zero, zero_mul]⟩
  · intro j _
    exact ae_of_all _ fun _ _ => by
      simp only [zeroFramePreSide, Int.cast_one, sub_self, mul_zero, add_zero]

/-- The old principal-chart compatibility at offset zero and `b = 0`
requires branch one. Measurability alone does not imply this equation. -/
theorem sourceFrameOffset_eq_zero_iff (i : BothLow) (n : ℤ) :
    sourceFrameOffset (16 / i.kappa) 0 n = 0 ↔ n = 1 := by
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hκf : 0 < 16 / i.kappa := div_pos (by norm_num) hκ
  have hκf4 : 16 / i.kappa < 4 := (div_lt_iff₀ hκ).2 (by linarith only [i.kappa_gt_four])
  have hc : 2 * π * chiC (16 / i.kappa) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (ne_of_gt (Sec4.chiC_pos hκf hκf4))
  rw [sourceFrameOffset, zero_add]
  constructor
  · intro h
    have he := (mul_eq_zero.mp h).resolve_left hc
    have he' : (n : ℝ) = 1 := (sub_eq_zero.mp he).symm
    exact_mod_cast he'
  · rintro rfl
    simp only [Int.cast_one, sub_self, mul_zero]

/-- Relifting changes the actual chart object unless the branch was
already one. Updating the offset field alone cannot perform this step. -/
theorem zeroFrameChart_eq_self_iff (c : Chart) (n : ℤ) :
    zeroFrameChart c n = c ↔ n = 1 := by
  constructor
  · intro h
    have he := congrArg (fun t : Chart => t.2.2 0) h
    rw [zeroFrameChart_lift] at he
    have hn : (n : ℝ) = 1 := by nlinarith only [he, Real.pi_pos]
    exact_mod_cast hn
  · rintro rfl
    simp only [zeroFrameChart, sub_self, PocketStopField.shiftChart, Int.cast_zero, mul_zero, sub_zero]

end InteractingSLE.Sec7.SideC17
