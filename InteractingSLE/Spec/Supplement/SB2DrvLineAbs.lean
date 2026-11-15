/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLine

/-!
# SB2(1)'s lines at absolute physical times

Packet PROVE-T14-SB2DRV (round 5). FIN's union mean (`FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK`) needs
the flow hull to be a local set *by itself*, which holds at deterministic physical times of the upper flow but not at
the random times `T_L + t`; K2 needs the entrance σ-algebra `𝒢' = D.marks` inside its relative filtration at time `0`.
Both hold for lines indexed by the absolute physical time `T` of the upper flow, stopped at `max(T, T_L)`:

* `maxRule T`: the rule `max(T, first visit)`; `isParamGalmarino_maxRule`, `measurable_maxRule`;
* `D.absSet T = A ∪ ⋃ₙ η_n([0, max(T, T_n)])` (on `{T_L < T}` the union `A ∪ η([0, T])` at the deterministic time
  `T`; before the entrance the erasure union), `D.absMarks T`;
* **`D.isHistoryAvoidanceLocal_abs`**, `D.measurableSet_disjoint_abs`, `D.absMarks_le_aeSigma`, `D.absMarks_le`, and the
  nesting **`D.absMarks_mono`**, **`D.marks_le_absMarks`** (the entrance σ-algebra lies below every absolute line).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart

/-- The rule `max(T, first visit)`. -/
def maxRule (T : ℝ≥0∞) (y : ℂ) (c : ℚ≥0 → ℂ) : ℝ≥0∞ := max T (hitQ y c)

theorem isParamGalmarino_maxRule (T : ℝ≥0∞) : IsParamGalmarino (maxRule T) := by
  intro y c c' hag
  have h1 : hitQ y c' = hitQ y c :=
    isParamGalmarino_hitQ y c c' fun q hq => hag q (hq.trans (le_max_right _ _))
  simp only [maxRule, h1]

theorem measurable_maxRule (T : ℝ≥0∞) : Measurable (Function.uncurry (maxRule T)) :=
  measurable_const.max measurable_hitQ

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

/-- The union at the absolute physical time `T` (stopped at `max(T, T_L)`). -/
def absSet (T : ℝ≥0∞) : Ω → Set ℂ :=
  limSet (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc D.point (maxRule T)

/-- Its marks. -/
@[instance_reducible]
def absMarks (T : ℝ≥0∞) : MeasurableSpace Ω :=
  limMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point (maxRule T)

/-- **The union at the absolute time `T` is a history-marked local set** of the centred field for its marks. -/
theorem isHistoryAvoidanceLocal_abs (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (T : ℝ≥0∞) :
    WholeField.IsHistoryAvoidanceLocal (D.absMarks T) (D.absSet T) (WholeField.centredField h u₀) P :=
  isHistoryAvoidanceLocal_limSet (WholeField.measurable_centredField HP.field.1 u₀)
    (walk_complSigma h12p h13 HP hu₀) D.paths D.point_meas (measurable_maxRule T) (isParamGalmarino_maxRule T)

theorem measurableSet_disjoint_abs (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (T : ℝ≥0∞)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[aeSigma (D.absMarks T) P] {ω | Disjoint (D.absSet T ω) U} :=
  measurableSet_disjoint_limSet D.paths.cont D.paths.start hUH
    ((walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)).1 U hUH)

theorem absMarks_le_aeSigma (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (T : ℝ≥0∞) :
    D.absMarks T ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P :=
  limMarks_le_aeSigma (past_le_aeSigma h12p h13 HP u₀) D.paths D.point_meas (measurable_maxRule T)

theorem absMarks_le (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (T : ℝ≥0∞) : D.absMarks T ≤ mΩ := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  exact limMarks_le ((HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)).2.1 (k + 1))
    D.paths D.point_meas (measurable_maxRule T)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The absolute lines are nested.** -/
theorem absMarks_mono {T T' : ℝ≥0∞} (hTT' : T ≤ T') : D.absMarks T ≤ D.absMarks T' :=
  limMarks_mono_rule D.point_meas (measurable_maxRule T) (isParamGalmarino_maxRule T)
    fun _ _ => max_le_max hTT' le_rfl

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The entrance σ-algebra lies below every absolute line.** -/
theorem marks_le_absMarks (T : ℝ≥0∞) : D.marks ≤ D.absMarks T :=
  limMarks_mono_rule D.point_meas measurable_hitQ isParamGalmarino_hitQ fun _ _ => le_max_right _ _

end EntranceUnion

end InteractingSLE.Theorem14.SB.Lv
