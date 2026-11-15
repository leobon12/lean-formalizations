/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrStopAe
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwViRed
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkAsm
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SBS3DwVkLife
import InteractingSLE.Spec.Supplement.SBS3DwVkLink
import InteractingSLE.Spec.Supplement.SBS3DwVmAd
import InteractingSLE.Spec.Supplement.SBS3DwVmSafe
import InteractingSLE.Spec.Supplement.SBS3DwVnEnd
import InteractingSLE.Spec.Supplement.SBS3DwVnTr

/-!
# Successor of `SB2VrStopAe` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VrStopAe` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_physStopLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vr

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **D10 steps 2 and 3 for SB2(1), almost surely.** At a launch on the entrance event, the physical stops of the
flow's lift are positive, strictly below the relative lifetime, nondecreasing, and increase to it. -/
theorem ae_physStopLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      (∀ m, 0 < physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) m) ∧
      (∀ m, physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) m < Vk.relLife κ b jumps E k u η ζ ω) ∧
      Monotone (physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω)) ∧
      ⨆ m, physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) m = Vk.relLife κ b jumps E k u η ζ ω := by
  have hflow := HP.flow
  obtain ⟨-, -, W, -, -, -, -, -, hgen⟩ := hflow
  filter_upwards [Vd.ae_clockDataLe h13 hS3 HP, Vd.ae_isDrivenCurve_liftLe h13 hS3 HP, hgen,
    ae_tip_bad_of_isFlowLine HP.flow,
    ae_notMem_closure_badSet HP.kappa_pos HP.kappa_lt_four HP.boundary HP.field HP.flow]
    with ω hcd hdr hg hend hnv hl hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTZ : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_toNNReal hTLtop]; exact hT
  have hζ0 : 0 < ζ ω := lt_of_le_of_lt (zero_le) hT
  have h0 := (hcd hl hT).1
  have hstr : StrictBefore (Ve.flowLift κ b jumps E k u η ζ ω) TL.toNNReal (ζ ω) := by
    by_cases hζ : ζ ω = ⊤
    · rw [hζ]; exact strictBefore_of_top ((hdr hl hT).1 hζ)
    · refine strictBefore_of_fin hζ hTZ ?_
      have := (hdr hl hT).2 hζ
      exact this
  have hcont : ContinuousOn (fun t => η ω t - u) {t | TL.toNNReal ≤ t ∧ (t : ℝ≥0∞) ≤ ζ ω} :=
    hg.2.1.mono fun t ht => ht.2
  have hend' : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω → (fun t => η ω t - u) T ∈ sb2BadClosure κ b jumps u ψ := by
    intro T hTe
    have hb := hend hζ0 (by rw [← hTe]; exact ENNReal.coe_ne_top)
    rw [← hTe, ENNReal.toNNReal_coe] at hb
    exact subset_closure hb
  have hnv' : ∀ t : ℝ≥0, TL.toNNReal ≤ t → (t : ℝ≥0∞) < ζ ω →
      (fun t => η ω t - u) t ∉ sb2BadClosure κ b jumps u ψ := fun t _ ht => hnv hζ0 t ht
  have hd : 0 < infEDist ((fun t => η ω t - u) TL.toNNReal) (sb2BadClosure κ b jumps u ψ) := by
    rw [infEDist_pos_iff_notMem_closure, sb2BadClosure, closure_closure]
    exact hnv' _ le_rfl hTZ
  refine ⟨fun m => physStop_pos h0 hstr hTZ hcont hd m, fun m => physStop_lt h0 hstr hTZ hcont hend' m, physStop_mono,
    iSup_physStop h0 hstr hTZ hcont hend' isClosed_closure hnv'⟩

end

end InteractingSLE.Theorem14.SB.Vr
