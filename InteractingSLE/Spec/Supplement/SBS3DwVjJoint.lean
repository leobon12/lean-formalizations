/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VjJoint
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SB2ViAbs
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

/-!
# Successor of `SB2VjJoint` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VjJoint` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `exists_joint_absLiftLe`.
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
  {u₀ : ℂ → ℝ}

/-- **The absolute lift is jointly measurable** on a measurable conull event inside the entrance event, below the
lifetime. -/
theorem exists_joint_absLiftLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ (G : Set Ω) (F : Ω × ℝ≥0 → ℂ), MeasurableSet G ∧ P Gᶜ = 0 ∧ Measurable F ∧
      ∀ ω ∈ G ∩ D.event, ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω → F (ω, T) = Vi.absLift κ b jumps E k u η ζ ω T := by
  classical
  obtain ⟨G₁, hG₁m, hG₁n, hmeas⟩ := Vi.exists_measurable_absLiftLe h13 hS3 HP I D
  have hfacts : ∀ᵐ ω ∂P, (ω ∈ launchSet κ b jumps E (k + 1) →
      (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω)) ∧
      (ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω → ContinuousAt (Vi.absLift κ b jumps E k u η ζ ω) T) := by
    filter_upwards [D.ae_mem_event_iff, Vi.ae_absLift_goodLe h13 hS3 HP I D] with ω hev hgd
    exact ⟨hev, fun hl hT T hTζ => (hgd hl hT T hTζ).1⟩
  obtain ⟨G₂, hG₂m, hG₂n, hG₂⟩ := Vf.exists_measurable_conull hfacts
  set f : Ω → ℝ≥0 → ℂ := fun ω T =>
    if ω ∈ G₁ ∩ D.event ∩ {ω | (T : ℝ≥0∞) < ζ ω} then Vi.absLift κ b jumps E k u η ζ ω T else 0 with hf
  have hfm : ∀ T, Measurable fun ω => f ω T := fun T => by
    have := (hmeas T).mono ((D.lineFiltC HP).le T) le_rfl
    convert this using 2
  obtain ⟨F, hFm, hF⟩ := exists_jointly_measurable hfm
  refine ⟨G₁ ∩ G₂, F, hG₁m.inter hG₂m, ?_, hFm, fun ω hω T hTζ => ?_⟩
  · rw [compl_inter]
    exact measure_union_null hG₁n hG₂n
  · obtain ⟨⟨hω1, hω2⟩, hωE⟩ := hω
    have hl := D.event_subset hωE
    have hT := ((hG₂ ω hω2).1 hl).1 hωE
    have hcont := (hG₂ ω hω2).2 hl hT T hTζ
    have hev : f ω =ᶠ[𝓝 T] Vi.absLift κ b jumps E k u η ζ ω := by
      have hopen : IsOpen {T' : ℝ≥0 | (T' : ℝ≥0∞) < ζ ω} :=
        isOpen_lt ENNReal.continuous_coe continuous_const
      filter_upwards [hopen.mem_nhds hTζ] with T' hT'
      simp only [hf, show ω ∈ G₁ ∩ D.event ∩ {ω | (T' : ℝ≥0∞) < ζ ω} from ⟨⟨hω1, hωE⟩, hT'⟩, ↓reduceIte]
    rw [hF ω T (hcont.congr hev.symm)]
    simp only [hf, show ω ∈ G₁ ∩ D.event ∩ {ω | (T : ℝ≥0∞) < ζ ω} from ⟨⟨hω1, hωE⟩, hTζ⟩, ↓reduceIte]

end

end InteractingSLE.Theorem14.SB.Vj
