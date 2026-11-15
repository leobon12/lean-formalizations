/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VjEnt
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SB2VgClock
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2VjEnt` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VjEnt` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_entMeas_eqLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vj

open Lv Exist.Staged Exist.StagedLaw

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The entrance read from the clock is the entrance**, almost surely at a launch on the entrance event. -/
theorem ae_entMeas_eqLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] {a : ℝ≥0 → Ω → ℝ≥0∞}
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      entMeas a ω = Ve.entT κ b jumps E k u η ζ ω := by
  filter_upwards [hae, Vd.ae_clockDataLe h13 hS3 HP, Vd.ae_chain_liftOfLe h13 hS3 HP] with ω ha hcd hch hF hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  have h0 : Sec7.Lemma71C.capClock (fun r : ℝ => (Ve.flowLift κ b jumps E k u η ζ ω) r.toNNReal) 0 = 0 := (hcd hF hT).1
  have hpos : ∀ s : ℝ≥0, 0 < s → ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
      0 < Sec7.Lemma71C.capClock (fun r : ℝ => (Ve.flowLift κ b jumps E k u η ζ ω) r.toNNReal) s := by
    intro s hs hsζ
    obtain ⟨Wr, ηr, β', hc⟩ := hch hF hT (TL.toNNReal + s) le_self_add hsζ
    exact capClock_pos_of_chain hc (by rw [NNReal.coe_add]; exact add_sub_cancel_left _ _) (NNReal.coe_pos.2 hs)
  rw [entMeas_eq (ha hF hT) h0 hpos (by rw [hTLc]; exact hT), hTLc]

end

end InteractingSLE.Theorem14.SB.Vj
