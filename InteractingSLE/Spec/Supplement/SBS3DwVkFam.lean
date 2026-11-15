/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkFam
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SB2VjRel
import InteractingSLE.Spec.Restart.ChartMeasFlow
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

/-!
# Successor of `SB2VkFam` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VkFam` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `exists_drivenFamilyLe`;
* `ae_isDrivenCurve_familyLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The measurable driven family** (the relative lift, reparametrized when the remaining life is finite). -/
theorem exists_drivenFamilyLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {a : ℝ≥0 → Ω → ℝ≥0∞} (ha : ∀ t, Measurable (a t))
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) :
    ∃ ρ : Ω → ℝ → ℂ, (∀ r, 0 ≤ r → Measurable fun ω => ρ ω r) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0)) := by
  classical
  obtain ⟨G, F, hGm, hGn, hFm, hF⟩ := Vj.exists_joint_absLiftLe h13 hS3 HP I D
  have he : Measurable (Vj.entMeas a) := Vj.measurable_entMeas ha
  have hζm : Measurable ζ := Restart.measurable_lifetime_of_isFlowLine HP.flow
  set tm : Ω → ℝ → ℝ≥0 := fun ω r =>
    if ζ ω = ⊤ then r.toNNReal else (clockOf ((ζ ω).toReal - (Vj.entMeas a ω).toReal) r).toNNReal with htm
  refine ⟨fun ω r => F (ω, (Vj.entMeas a ω).toNNReal + tm ω r), fun r _ => ?_, ?_⟩
  · have hL : Measurable fun ω => (ζ ω).toReal - (Vj.entMeas a ω).toReal := hζm.ennreal_toReal.sub he.ennreal_toReal
    have hcl : Continuous fun L : ℝ => (clockOf L r).toNNReal :=
      continuous_real_toNNReal.comp (continuous_id.mul continuous_const)
    have htmm : Measurable fun ω => tm ω r :=
      Measurable.ite (hζm (measurableSet_singleton ⊤)) measurable_const (hcl.measurable.comp hL)
    exact hFm.comp (measurable_id.prodMk (he.ennreal_toNNReal.add htmm))
  · have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGn
    filter_upwards [Vj.ae_entMeas_eqLe h13 hS3 HP hae, D.ae_mem_event_iff, hGae] with ω hent hev hωG hl hT
    have hωE : ω ∈ D.event := (hev hl).2 hT
    have he' := hent hl hT
    set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
    have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
    have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
    refine ⟨fun hζ r hr => ?_, fun hζ r hr => ?_⟩
    · have hr' : (0 : ℝ) ≤ r := hr
      show F (ω, (Vj.entMeas a ω).toNNReal + tm ω r) = _
      simp only [htm, hζ, ↓reduceIte]
      rw [he']
      rw [hF ω ⟨hωG, hωE⟩ _ (by rw [hζ]; exact ENNReal.coe_lt_top)]
      unfold Vi.absLift
      rw [add_tsub_cancel_left]
      rfl
    · have hr' : (0 : ℝ) ≤ r := hr
      set ℓ : ℝ := (ζ ω).toReal - TL.toReal with hℓ
      have hℓpos : 0 < ℓ := by
        rw [hℓ, sub_pos]
        exact (ENNReal.toReal_lt_toReal hTLtop hζ).2 hT
      have hcm := clockOf_mem_Ico hℓpos hr'
      show F (ω, (Vj.entMeas a ω).toNNReal + tm ω r) = _
      simp only [htm, hζ, ↓reduceIte]
      rw [he']
      have hlt : ((TL.toNNReal + (clockOf ℓ r).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        rw [← ENNReal.coe_toNNReal hζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
          Real.coe_toNNReal _ hcm.1]
        have h1 := hcm.2
        rw [hℓ] at h1
        have h2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
        have h3 : (ζ ω).toReal = ((ζ ω).toNNReal : ℝ) := rfl
        linarith
      rw [hF ω ⟨hωG, hωE⟩ _ hlt]
      unfold Vi.absLift
      rw [add_tsub_cancel_left]
      rfl

/-- **The family is a driven curve**, almost surely at a launch on the entrance event. -/
theorem ae_isDrivenCurve_familyLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω → IsDrivenCurve (ρ ω) := by
  filter_upwards [hρ, Vd.ae_isDrivenCurve_liftLe h13 hS3 HP] with ω hρω hdr hl hT
  obtain ⟨h1, h2⟩ := hρω hl hT
  obtain ⟨d1, d2⟩ := hdr hl hT
  by_cases hζ : ζ ω = ⊤
  · have d : IsDrivenCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) := d1 hζ
    exact IsDrivenCurve.congr d fun x hx => ((h1 hζ) hx).symm
  · have d : IsDrivenCurve (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
        ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) := d2 hζ
    exact IsDrivenCurve.congr d fun x hx => ((h2 hζ) hx).symm

end

end InteractingSLE.Theorem14.SB.Vk
