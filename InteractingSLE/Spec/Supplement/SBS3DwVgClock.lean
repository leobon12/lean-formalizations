/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgClock
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SB2VgCap
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2VgClock` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VgClock` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_clockOf_eq_clockMeasLe`;
* `exists_versionClockLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vg

open Lv Exist.Staged Exist.StagedLaw

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The relative clock is the line-mark reading at every time**, almost surely. -/
theorem ae_clockOf_eq_clockMeasLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t : ℝ≥0, Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t =
        clockMeas D I t ω := by
  classical
  filter_upwards [ae_clockOf_eq_capReadLe h13 hS3 HP I D] with ω hcap hF hT t
  have hcap := hcap hF hT
  unfold clockMeas
  by_cases hζt : ζ ω ≤ t
  · simp only [hζt, ↓reduceIte]
    refine le_antisymm ?_ (iSup₂_le fun q hq => ?_)
    · rw [Vd.clockOf_eq_sup_of_le hζt]
      refine iSup₂_le fun s hs => ?_
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn hs
      refine le_trans ?_ (le_iSup₂_of_le q ⟨hq2, hq2.le.trans hζt⟩ le_rfl)
      rw [← hcap q hq2]
      unfold Vc.clockOf
      exact le_iSup₂_of_le s hq1.le (le_iSup_of_le hs le_rfl)
    · rw [← hcap q hq.1]
      exact Vc.monotone_clockOf _ _ _ (ENNReal.coe_le_coe.1 hq.2)
  · simp only [hζt, ↓reduceIte]
    exact hcap t (not_le.1 hζt)

/-- **The version's clock**: continuous, monotone, `0` at `0` at every sample, measurable for the completed line
filtration, and almost surely the relative clock of the flow's lift at a launch on the entrance event. -/
theorem exists_versionClockLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ (a : ℝ≥0 → Ω → ℝ≥0∞), (∀ t, Measurable[D.lineFiltC HP t] (a t)) ∧
      (∀ ω, Continuous fun t => a t ω) ∧ (∀ ω, Monotone fun t => a t ω) ∧ (∀ ω, a 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        ∀ t, a t ω =
          Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t := by
  classical
  -- the good event
  have hgood : ∀ᵐ ω ∂P, (ω ∈ launchSet κ b jumps E (k + 1) →
      (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω)) ∧
      (ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        Continuous (Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω)) ∧
        Sec7.Lemma71C.capClock (fun r : ℝ => (Ve.flowLift κ b jumps E k u η ζ ω) r.toNNReal) 0 = 0 ∧
        ∀ t, Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t =
          clockMeas D I t ω) := by
    filter_upwards [D.ae_mem_event_iff, Vd.ae_continuous_clockOfLe h13 hS3 HP, Vd.ae_clockDataLe h13 hS3 HP,
      ae_clockOf_eq_clockMeasLe h13 hS3 HP I D] with ω hev hc hd hm
    exact ⟨hev, fun hF hT => ⟨hc hF hT, (hd hF hT).1, hm hF hT⟩⟩
  obtain ⟨G, hGm, hGnull, hG⟩ := Vf.exists_measurable_conull hgood
  have hEv : MeasurableSet D.event := (D.absMarks_le HP 0) _ (D.marks_le_absMarks 0 _ (D.measurableSet_event HP))
  -- on `G ∩ D.event`: the launch, the entrance, continuity, zero, and the reading
  have hGE : ∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω := by
    intro ω hω
    have hl := D.event_subset hω.2
    exact ⟨hl, ((hG ω hω.1).1 hl).1 hω.2⟩
  set a : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
    if ω ∈ G ∩ D.event then
      Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t
    else 0 with ha
  refine ⟨a, fun t => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, ?_⟩
  · -- measurable for the completed line filtration
    have hrd : Measurable[D.absMarks (t : ℝ≥0∞)] fun ω => if ω ∈ D.event then clockMeas D I t ω else 0 :=
      Measurable.ite (D.marks_le_absMarks t _ (D.measurableSet_event HP)) (measurable_clockMeas D I t)
        measurable_const
    have heq : a t = fun ω => if ω ∈ G then (if ω ∈ D.event then clockMeas D I t ω else 0) else 0 := by
      funext ω
      by_cases hω : ω ∈ G ∩ D.event
      · obtain ⟨hl, hT⟩ := hGE ω hω
        simp only [ha, hω, ↓reduceIte, hω.1, hω.2]
        exact ((hG ω hω.1).2 hl hT).2.2 t
      · simp only [ha, hω, ↓reduceIte]
        by_cases hωG : ω ∈ G
        · have hωE : ω ∉ D.event := fun h => hω ⟨hωG, h⟩
          simp only [hωG, hωE, ↓reduceIte]
        · simp only [hωG, ↓reduceIte]
    have hrd' : Measurable fun ω => if ω ∈ D.event then clockMeas D I t ω else 0 :=
      hrd.mono (D.absMarks_le HP t) le_rfl
    have hmeas : Measurable (a t) := by
      rw [heq]; exact Measurable.ite hGm hrd' measurable_const
    refine Vf.measurable_lineFiltC D HP t hmeas hrd ?_
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]; exact hGnull
    filter_upwards [hGae] with ω hω
    rw [heq]
    simp only [hω, ↓reduceIte]
  · -- continuity
    by_cases hω : ω ∈ G ∩ D.event
    · obtain ⟨hl, hT⟩ := hGE ω hω
      simp only [ha, hω, ↓reduceIte]
      exact ((hG ω hω.1).2 hl hT).1
    · simp only [ha, hω, ↓reduceIte]
      exact continuous_const
  · -- monotonicity
    by_cases hω : ω ∈ G ∩ D.event
    · simp only [ha, hω, ↓reduceIte]
      exact Vc.monotone_clockOf _ _ _
    · simp only [ha, hω, ↓reduceIte]
      exact monotone_const
  · -- zero at zero
    by_cases hω : ω ∈ G ∩ D.event
    · obtain ⟨hl, hT⟩ := hGE ω hω
      simp only [ha, hω, ↓reduceIte]
      exact Vc.clockOf_eq_zero_of_le zero_le ((hG ω hω.1).2 hl hT).2.1
    · simp only [ha, hω, ↓reduceIte]
  · -- the identification
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]; exact hGnull
    filter_upwards [hGae, D.ae_mem_event_iff] with ω hωG hev hl hT t
    have hωE : ω ∈ D.event := (hev hl).2 hT
    simp only [ha, show ω ∈ G ∩ D.event from ⟨hωG, hωE⟩, ↓reduceIte]

end

end InteractingSLE.Theorem14.SB.Vg
