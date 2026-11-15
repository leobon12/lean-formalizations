/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aForceFixed
import InteractingSLE.Spec.Supplement.GW2aStepBW1
import InteractingSLE.Spec.Supplement.BRLeafGB6Aux
import InteractingSLE.Spec.Sec4.Special3Contact
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Theorem15Inputs

/-!
# `FlowFixedTimeInteriorStatement` from the absorbed-merge input

Packet PROVE-GW2A-FORCE. PROVE-GW2A-STEP's named input `GW2aStep.FlowFixedTimeInteriorStatement` (a deterministic
positive own time before the lifetime is almost surely not a boundary time of a flow line) is proved here from

* Theorem 1.3 (`Exist.Theorem13Statement`: a continuous generating trace before the lifetime; ruling R48 permits it,
  the statement serves Theorem 1.4 only),
* Aux. lemma 24 (`IsIntegratedSLEEvolution.ae_mem_H_of_forall_ne`: nonzero force gaps put the trace in `ℍ`),
* `GW2aForce.ae_absorbedMerge_of_collision` (this packet: at a fixed time every force collision is almost surely an
  absorbed merge — the Bessel comparison), and
* the new named input **`FixedTimeAbsorbedMergeStatement`**: at a deterministic time an absorbed merge almost surely
  does not occur (a fixed time is almost surely not the first swallowing time of a boundary gap between two
  consecutive marks whose inner partial sum is `≤ −2`, i.e. a gap that the trace can never touch).

The genuinely remaining content is this last statement: near such a merge two separate groups of marks approach the
driver together, the drift of every gap is unbounded below relative to a Bessel drift, and the one-dimensional
comparison used for every other collision does not apply (see the handoff).

* `isInteriorStop_of_mem_H`: a stop before the lifetime at an interior trace point is an interior stop;
* **`flowFixedTimeInteriorStatement_of_absorbedMerge`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aForce

/-- **Named input: at a fixed time, an absorbed merge almost surely does not occur.** For an integrated
`SLE_κ(ρ)` evolution with `0 < κ < 4` and an ordered force word, and a deterministic time `t > 0`, almost surely on
`{t < ζ}` no two consecutive marks on one side whose inner partial sum is `≤ −2` and which are unmerged before `t`
are swallowed together at `t`. -/
def FixedTimeAbsorbedMergeStatement : Prop :=
  ∀ {κ : ℝ}, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ}, IsOrderedForceWord xL xR → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → ∀ t : ℝ≥0, 0 < t →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω →
        ¬ AbsorbedMergeR ρR (fun s => W s ω) (fun i s => VR i s ω) t ∧
          ¬ AbsorbedMergeL ρL (fun s => W s ω) (fun i s => VL i s ω) t

/-- **No force collision at a fixed time** (from the absorbed-merge input): almost surely on `{t < ζ}` every force
gap is nonzero at `t`. -/
theorem ae_forall_ne_of_absorbedMerge (hRes : FixedTimeAbsorbedMergeStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω → (∀ i, W t ω ≠ VL i t ω) ∧ ∀ j, W t ω ≠ VR j t ω := by
  filter_upwards [ae_absorbedMerge_of_collision hκ hF hE ht, hRes hκ hκ4 hF hE t ht] with ω hcol hres htζ
  exact ⟨fun i he => (hres htζ).2 ((hcol htζ).2 i he.symm),
    fun j he => (hres htζ).1 ((hcol htζ).1 j he.symm)⟩

/-- **An interior trace point at a stop before the lifetime is an interior stop.** -/
theorem isInteriorStop_of_mem_H {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w ζ α)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hH : α t ∈ H) : GW2Later.IsInteriorStop w t := by
  refine ⟨α t, hH, ?_⟩
  obtain ⟨t₂, htt₂, ht₂⟩ := exists_real_btwn_of_lt ht
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg _) htt₂.le
  have hreg := BRLeaf.pieceRegular_of_lt hα hw hw0 ht
  have hc1 : ContinuousOn (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (t : ℝ≥0∞)).toNNReal) (Icc 0 t₂) :=
    hreg.continuous_stoppedReal.1.continuousOn
  have hc2 : ContinuousOn (fun r : ℝ => w r.toNNReal) (Icc 0 t₂) := by
    refine hw.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    refine lt_of_le_of_lt ?_ ht₂
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal t₂
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)
  have heq : EqOn (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (t : ℝ≥0∞)).toNNReal)
      (fun r : ℝ => w r.toNNReal) (Icc 0 (t : ℝ)) := fun r hr => by
    have hle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)
    simp only [min_eq_left hle, ENNReal.toNNReal_coe]
  have hF : ∀ z, fwdMapInv (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (t : ℝ≥0∞)).toNNReal) (t : ℝ) z =
      fwdMapInv (fun r : ℝ => w r.toNNReal) (t : ℝ) z :=
    LocalExt.fwdMapInv_congr_of_continuousOn hc1 hc2 (NNReal.coe_nonneg _) htt₂ heq
  have htip := hα.tendsto_fwdMapInv_mul_I hw hw0 ht
  show Tendsto (fun y : ℝ => Chart.id.2.1 (fwdMapInv
    (fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (t : ℝ≥0∞)).toNNReal) ((t : ℝ≥0∞).toNNReal : ℝ)
      (y * Complex.I))) (𝓝[>] 0) (𝓝 (α t))
  simp only [ENNReal.toNNReal_coe]
  refine htip.congr fun y => ?_
  exact (hF _).symm

/-- **`FlowFixedTimeInteriorStatement` from the absorbed-merge input** (and Theorem 1.3). -/
theorem flowFixedTimeInteriorStatement_of_absorbedMerge (hRes : FixedTimeAbsorbedMergeStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) : GW2aStep.FlowFixedTimeInteriorStatement.{u} := by
  intro κ hκ hκ4 θ _ b jumps _ Ω _ _ Q _ h _ Wα ζα hfl t ht
  obtain ⟨h', 𝓕, VL, VR, B, -, hcoup⟩ := hfl
  have hE := hcoup.1
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps 0
  filter_upwards [ae_forall_ne_of_absorbedMerge hRes hκ hκ4 hF hE ht, hT13 hκ hF hE,
    hE.ae_mem_H_of_forall_ne hκ hκ4.le, hE.2.2.2.2] with ω hne htr hH hp htζ
  obtain ⟨-, η, hη, -⟩ := htr
  obtain ⟨hneL, hneR⟩ := hne htζ
  have hηH : η t ∈ H := hH (ζα ω) le_rfl η hη t ht htζ.le htζ hneL hneR
  exact isInteriorStop_of_mem_H hη (hp.isForcePath.continuousOn_w) hp.isForcePath.w_zero htζ hηH

end GW2aForce

end Theorem14

end InteractingSLE
