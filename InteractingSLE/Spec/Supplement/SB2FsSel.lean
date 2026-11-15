/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FsGlue
import InteractingSLE.Spec.Supplement.SB2CvOff
import InteractingSLE.Spec.Supplement.SB2MzMain
import InteractingSLE.Spec.Supplement.SB2FlZero

/-!
# Selector events for the gluing at `ℓ + 2`

Worker PROVE-SB2-F3LAW (round 6, D80). `Fs.stageLawOn_glue` at stage `ℓ + 2` needs its selector event in the line
σ-algebra of the stage-`ℓ + 2` family and in the completed retained past `aeSigma (stageMarks (ℓ + 2))`.
**`selector_of_prev`**: every event of the stage-`ℓ` line σ-algebra qualifies (`𝓖 0 ≤ stageMarks (ℓ + 1) ≤
stageMarks (ℓ + 2)`, CANON's `Cz.capPast_le_stageMarks_succ`; `𝓖 0 ≤ 𝓖' 0`). In particular F2b′'s live events at `ℓ`
(SB2LIFT's 6E `F`, NOJUMP's 9E `FB`, `Fr`), which are measurable for that σ-algebra, are selectors at `ℓ + 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Fs

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms

/-- **Events of the stage-`ℓ` line σ-algebra are selectors at `ℓ + 2`.** -/
theorem selector_of_prev {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    {C : Set Ω} (hC : MeasurableSet[lineFiltC P 𝓖 0] C) :
    MeasurableSet[lineFiltC P 𝓖' 0] C ∧ MeasurableSet[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] C := by
  have hℓlt : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  have hℓ₂le : ℓ + 2 ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ₂).1.le
  have h𝓖𝓖' : 𝓖 0 ≤ 𝓖' 0 := by
    rw [h𝓖, h𝓖']
    exact sup_le_sup le_rfl (Fl.capPast_le_capPast _ hwℓ hℓ₂le)
  have h𝓖S : 𝓖 0 ≤ stageMarks κ b jumps E u l k (ℓ + 2) := by
    rw [h𝓖]
    exact (Cz.capPast_le_stageMarks_succ E u l k ℓ hℓlt hwℓ).trans (Mz.stageMarks_mono (by omega))
  exact ⟨inf_le_inf_left _ (WalkLaw.aeSigma_mono (P := P) h𝓖𝓖') _ hC,
    WalkLaw.aeSigma_mono (P := P) h𝓖S _ hC.2⟩

end InteractingSLE.Theorem14.SB.Fs
