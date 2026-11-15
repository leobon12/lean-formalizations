/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkLife
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SB2VkFam
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

/-!
# Successor of `SB2VkLife` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VkLife` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_capLife_eqLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The family's lifetime is the relative lifetime of the flow's lift**, almost surely at a launch on the
entrance event. -/
theorem ae_capLife_eqLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      Sec7.Lemma71C.capLife (ρ ω) =
        ⨆ (s : ℝ≥0) (_ : (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
        ENNReal.ofReal (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) := by
  filter_upwards [hρ, Vd.ae_clockDataLe h13 hS3 HP] with ω hρω hcd hl hT
  obtain ⟨h1, h2⟩ := hρω hl hT
  obtain ⟨-, hloc⟩ := hcd hl hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- monotonicity of the capacity clock of the lift on `[0, y]` for `T_L + y < ζ`
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ((TL.toNNReal + y.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
      capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) x ≤
        capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) y := by
    intro x y hx hxy hyζ
    have hy : 0 ≤ y := hx.trans hxy
    have hm := (hloc (TL.toNNReal + y.toNNReal) le_self_add hyζ).2
    have key : ∀ z, z ∈ Icc (0 : ℝ) y →
        z ∈ Icc (0 : ℝ) (((TL.toNNReal + y.toNNReal : ℝ≥0) : ℝ) - (TL.toNNReal : ℝ)) := fun z hz =>
      ⟨hz.1, by rw [NNReal.coe_add, Real.coe_toNNReal _ hy]; linarith [hz.2]⟩
    exact hm (key x ⟨hx, hxy⟩) (key y ⟨hy, le_rfl⟩) hxy
  by_cases hζ : ζ ω = ⊤
  · rw [capLife_eq_iSup_of_eqOn (h1 hζ) fun x hx y hy hxy =>
      hmono x y hx hxy (by rw [hζ]; exact ENNReal.coe_lt_top)]
    refine iSup_congr fun s => ?_
    rw [iSup_pos (show (((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞)) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)]
  · set ℓ : ℝ := (ζ ω).toReal - TL.toReal with hℓ
    have hℓpos : 0 < ℓ := by
      rw [hℓ, sub_pos]; exact (ENNReal.toReal_lt_toReal hTLtop hζ).2 hT
    have hiff : ∀ s : ℝ≥0, (s : ℝ) < ℓ ↔ ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω := fun s => by
      rw [← ENNReal.coe_toNNReal hζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add, hℓ, hTLr]
      constructor <;> intro h' <;> [skip; skip] <;>
        · have h3 : (ζ ω).toReal = ((ζ ω).toNNReal : ℝ) := rfl
          linarith
    rw [capLife_relCurve_of_eqOn hℓpos (h2 hζ) fun x hx y hy hxy => hmono x y hx.1 hxy (by
      rw [← ENNReal.coe_toNNReal hζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
        Real.coe_toNNReal _ (hx.1.trans hxy)]
      have := hy.2
      rw [hℓ, hTLr] at this
      have h3 : (ζ ω).toReal = ((ζ ω).toNNReal : ℝ) := rfl
      linarith)]
    exact iSup_congr fun s => iSup_congr_Prop (hiff s) fun _ => rfl

end

end InteractingSLE.Theorem14.SB.Vk
