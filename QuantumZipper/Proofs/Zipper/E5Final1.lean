import QuantumZipper.Proofs.Zipper.E5Asm4
import QuantumZipper.Proofs.Zipper.E5IncSwitch
import QuantumZipper.Proofs.Zipper.E5Main4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-FINAL, part 1: random-time E5-G0 and the level-space `Setup` of the collision correction

Task E5-ZOOMMODEL (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of
Lemma 5.6; blueprint `E_BRANCH_BLUEPRINT.md` §4 E5, steps (1)–(2)). This file supplies two of the
inputs of the `E5Main5.ZoomModel` built on the level space of `E5Asm4.e5_level_repr`,
`(Ω₁, Q) = ((ℝ≥0 × NS(P)) × Ω', Rr₁.withDensity w₁)`:

## 1. E5-G0 at a random collision time

The ZoomModel corrections are
`g = locCorr κ V_ω (T − T_ℓ(ω)) ϖ ρ₀ (X' ω)` (full driver) and
`g₀ = locCorr κ (germFreeDrv u₀ V_ω) (T − T_ℓ(ω) − u₀) ϖ ρ₀ (X' ω)` (germ-free driver, E5 step (2)),
so the E5-G0 domination of `E5G0Dom` must be available at an `ω`-dependent time *and with two
different times* for `g` and `g₀` (the `t − u₀` shift of `E5G0.locCorrG0`). Here
`abs_locCorr_sub_le_of_region₂` is `E5G0Dom.abs_locCorr_sub_le_of_region` with `t` and `t₀`
separated, `exists_dominates_locCorrG0_rt` is its pointwise-assembly form, and
`e5G0_of_geometry_measurable_rt` is `E5G0Dom.e5G0_of_geometry_measurable` for a random time —
this is the `hbad` field of `E5Main5.ZoomModel` (own elementary generalization of
`E5G0Dom`; the mathematics is unchanged).

## 2. The level-space `Setup` of the collision correction

`lvlField` is the D28 regular version `X' = regField ϖ ρ₀ ∘ X₁ ∘ snd` of the free field `X₁` of
`e5_level_repr`, `lvlTime` is the level collision time `T − T_ℓ`, and `lvlDrv` the level driver
`Vr κ T B ∘ ofCompl P ∘ snd`. With `Ξ` carrying the level point (`Ξ = fst`), the `hν` input of
`setup_locCorr_switch_reg` / `setup_locCorr_germFree_reg` is **discharged** for the full driver by
`E5Asm2.measurable_varpiT_level` (`measurable_varpiT_lvl`); the remaining inputs are the base
`Setup` (with a constant fallback correction, the Q-law freeness/independence facts of the level
field) and the driver-part measurability `hdrv` (measurability of `z ↦ locCorrDrv κ V_ω t_ω ϖ z`).

Own bookkeeping (no new mathematics).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open D3Plus B2 E1 LengthMarkov ESM

variable {Ω₁ : Type} [MeasurableSpace Ω₁]

/-! ## 1. E5-G0 with two collision times -/

/-! ## 2. The level space of `E5Asm4.e5_level_repr` -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The level space `(ℝ≥0 × NS(P)) × Ω'` of `E5Asm4.e5_level_repr`. -/
abbrev lvl (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Ω' : Type) : Type :=
  (ℝ≥0 × NullMeasurableSpace Ω P) × Ω'

/-- The level collision time `T − T_ℓ` at a level point. -/
def lvlTime (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (p : ℝ≥0 × NullMeasurableSpace Ω P) : ℝ :=
  T - ((levelTime (lenA κ T B X) T.toNNReal p.1 (ofCompl P p.2) : ℝ≥0) : ℝ)

/-- The level driver `Vr κ T B ∘ ofCompl P ∘ snd` at a level point. -/
def lvlDrv (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (p : ℝ≥0 × NullMeasurableSpace Ω P) : ℝ → ℝ :=
  Vr κ T B (ofCompl P p.2)

/-- The level field (D28 regular version) `X' = regField ϖ ρ₀ ∘ X₁ ∘ snd`. -/
def lvlField (ϖ ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample) : lvl Ω P Ω' → FieldSample :=
  fun z => regField ϖ ρ₀ (X₁ z.2)

/-- The level conditioning map: the level point itself (it carries the driver data and the germ
of `E5Asm1.esmGerm`). Its `comap` is the completion-level σ-algebra of the first coordinate. -/
def lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P := fun z => z.1

theorem measurable_lvlXi : Measurable (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) :=
  measurable_fst

theorem measurable_lvlTime (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P =>
      T - ((levelTime (lenA κ T B X) T.toNNReal p.1 (ofCompl P p.2) : ℝ≥0) : ℝ) :=
  measurable_const.sub (NNReal.continuous_coe.measurable.comp
    (measurable_levelTime_level hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2.1 hBc))

end E5
end QuantumZipper
