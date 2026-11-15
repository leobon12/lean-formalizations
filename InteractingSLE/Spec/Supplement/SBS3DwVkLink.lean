/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkLink
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SB2VkFrz
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkLife

/-!
# Successor of `SB2VkLink` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VkLink` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_lift_chartLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section Link

variable {c : Chart} {η : ℝ≥0 → ℂ} {Z : ℝ≥0∞} {L m : ℝ} {γ : ℝ≥0 → ℂ} {ρ : ℝ → ℂ}

end Link

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The lift reads the flow through the launch chart**, almost surely at a launch on the entrance event. -/
theorem ae_lift_chartLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ r : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        Ve.flowLift κ b jumps E k u η ζ ω r + (launchEntry κ b jumps E (k + 1) u ω : ℂ) ∈ H →
        (Lv.launchChart κ b jumps E (k + 1) ω).2.1
            (Ve.flowLift κ b jumps E k u η ζ ω r + (launchEntry κ b jumps E (k + 1) u ω : ℂ)) =
          η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) := by
  filter_upwards [Vc.ae_lineGeom_liftOfLe h13 hS3 HP] with ω hrec hl hT r hr hH
  have hTL : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hcoe : ((t₀ : ℝ≥0) : ℝ≥0∞) = Ve.entT κ b jumps E k u η ζ ω := ENNReal.coe_toNNReal hTL
  have e2 : (Ve.entT κ b jumps E k u η ζ ω).toReal = (t₀ : ℝ) := rfl
  -- a horizon beyond `r`
  obtain ⟨T, S₁, hTζ, hvis, hS₁, hS₁T, hrS⟩ : ∃ (T : ℝ≥0) (S₁ : ℝ), (T : ℝ≥0∞) ≤ ζ ω ∧
      Ve.entT κ b jumps E k u η ζ ω < T ∧ 0 < S₁ ∧ (Ve.entT κ b jumps E k u η ζ ω).toReal + S₁ < T ∧
      (r : ℝ) < S₁ := by
    by_cases hζ : ζ ω = ⊤
    · refine ⟨t₀ + r + 2, r + 1, by rw [hζ]; exact le_top, ?_, by positivity, ?_, by linarith⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; linarith [r.2]
      · rw [e2]; push_cast; linarith
    · set Zt : ℝ≥0 := (ζ ω).toNNReal with hZt
      have hZc : ((Zt : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
      have hr' : (t₀ : ℝ) + r < Zt := by
        rw [← hZc, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add] at hr; exact hr
      refine ⟨Zt, ((r : ℝ) + (Zt - t₀)) / 2, hZc.le, ?_, ?_, ?_, ?_⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; linarith [r.2]
      · linarith [r.2]
      · rw [e2]; linarith
      · linarith
  obtain ⟨p, g, β', γ, tL, Wr, ηr, -, ⟨-, -, hgi, -, -⟩, ⟨-, -, -, -, htL, -, -, hlift⟩, hag, -, hlo⟩ :=
    hrec hl T hTζ hvis S₁ hS₁ hS₁T
  have htL' : t₀ = tL := by
    have := congrArg ENNReal.toNNReal htL
    rw [ENNReal.toNNReal_coe] at this
    exact this.symm
  have hγr : Ve.flowLift κ b jumps E k u η ζ ω r = γ r := by
    rw [hlo r hrS, ← htL']
    rfl
  have hγH : γ r ∈ H := by
    have h' : 0 < (Ve.flowLift κ b jumps E k u η ζ ω r + (launchEntry κ b jumps E (k + 1) u ω : ℂ)).im := hH
    rw [Complex.add_im, Complex.ofReal_im, add_zero, hγr] at h'
    exact h'
  have h1 := hgi hγH
  rw [hlift r, Lw.shiftChart_inv, hag (tL + r) (by push_cast; linarith)] at h1
  rw [hγr, htL']
  exact (sub_left_inj.1 h1).symm

end

end InteractingSLE.Theorem14.SB.Vk
