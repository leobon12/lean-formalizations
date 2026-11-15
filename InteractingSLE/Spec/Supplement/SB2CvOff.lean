/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CzLaw

/-!
# The tail event and the offset of a stage, read in the retained past

Packet PROVE-SB2-CANON, round 2 (items (P2), (P3) of `Cz.SB2LowerStagePkgStatement`). F2b′ (NOJUMP's statement) gives
its live event `F` and its offset `x₀` measurable for the completed line σ-algebra `mΩ ⊓ aeSigma 𝓖₀ P` of the stage,
`𝓖₀ = (upper past) ⊔ (B's past capped at own time 0 through ℓ + 1)`. The package needs them in the retained past.

* **`capPast_le_stageMarks_succ`**: `𝓖₀ ≤ Ms.stageMarks (ℓ + 1)` (the capped record is a function of the full one).
* **`exists_eq_of_measurableSet_inf_aeSigma`**: an event of `mΩ ⊓ aeSigma 𝓖 P` is a.s. an event of any `𝒮 ⊇ 𝓖`; with
  the above, F2b′'s live event is a.s. an event of `Ms.stageMarks (ℓ + 1)` (the package's tail event `T`).
* **`exists_offset_stageMarks`**: the offset is, on B's launches at `ℓ` with positive lifetime and driver starting at
  `0`, a.s. equal to a function `x₁` measurable for `Ms.stageMarks ℓ`. The extra information of `𝓖₀` over the retained
  past is the capped record of piece `ℓ`, `readRec (retOf 0 e) = (e(0)·, 0, decide (ζ = 0))`, which is the constant
  `(0, 0, false)` on that event (Doob–Dynkin with the record frozen at its live value).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets Ms

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
/-- **The capped past of a stage is part of the retained past after the stage.** -/
theorem capPast_le_stageMarks_succ (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
    (k ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))) :
    pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤
      stageMarks κ b jumps E u l k (ℓ + 1) := by
  have hcap := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps)
    (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at hcap
  exact sup_le_sup le_rfl hcap

/-- **An event of the completed `𝓖` is almost surely an event of any larger `𝒮`.** -/
theorem exists_eq_of_measurableSet_inf_aeSigma {𝓖 𝒮 : MeasurableSpace Ω} (h : 𝓖 ≤ 𝒮) {F : Set Ω}
    (hF : MeasurableSet[mΩ ⊓ aeSigma 𝓖 P] F) : ∃ T : Set Ω, MeasurableSet[𝒮] T ∧ F =ᵐ[P] T := by
  obtain ⟨T, hT, hFT⟩ := (MeasurableSpace.measurableSet_inf.1 hF).2
  exact ⟨T, h _ hT, hFT⟩

/-- **The offset of a stage in the retained past**: on B's launches at `ℓ` with positive lifetime and driver starting
at `0`, a function measurable for the completed line σ-algebra of the stage is a.s. a function of the retained past. -/
theorem exists_offset_stageMarks [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hle : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ)
    {x₀ : Ω → ℝ} (hx₀ : Measurable[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) P] x₀) :
    ∃ x₁ : Ω → ℝ, Measurable[stageMarks κ b jumps E u l k ℓ] x₁ ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
            none →
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ 0 →
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).1 0 = 0 → x₀ ω = x₁ ω := by
  classical
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  set Ew := StagedReg.regFam E w with hEwdef
  set Eu := StagedReg.regFam E (Lu.upperSpec u l) with hEudef
  set pu := pastMap κ b jumps (Lu.upperSpec u l) Eu k with hpudef
  set pc := pastMap κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Ew (ℓ + 1) with hpcdef
  set pw := pastMap κ b jumps w Ew ℓ with hpwdef
  have h𝓖 : pastSigma κ b jumps (Lu.upperSpec u l) Eu k ⊔
      pastSigma κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Ew (ℓ + 1) =
      MeasurableSpace.comap (fun ω => (pu ω, pc ω)) inferInstance :=
    (MeasurableSpace.comap_prodMk _ _).symm
  -- a version measurable for the capped past, then Doob–Dynkin
  have hk := ae_ae_eq_of_measurable_aeSigma (P := P) hle hx₀
  obtain ⟨x', hx'm, hx'e⟩ := Qx.exists_measurable_ae_eq_of_kernel_const (P := P) hle (hx₀.mono inf_le_left le_rfl)
    (G := univ) (by filter_upwards [hk] with ω₀ h _ using h)
  rw [h𝓖] at hx'm
  obtain ⟨g, hg, hgx⟩ := hx'm.exists_eq_measurable_comp
  set r₀ : RecData := (fun _ => 0, 0, false) with hr₀
  set q : Ω → PastData (ℓ + 1) := fun ω i => if h : (i : ℕ) < ℓ then pw ω ⟨i, h⟩ else r₀ with hqdef
  refine ⟨fun ω => g (pu ω, q ω), ?_, ?_⟩
  · have hpu : Measurable[stageMarks κ b jumps E u l k ℓ] pu := Measurable.of_comap_le le_sup_left
    have hpw : Measurable[stageMarks κ b jumps E u l k ℓ] pw := Measurable.of_comap_le le_sup_right
    have hq : Measurable[stageMarks κ b jumps E u l k ℓ] q := by
      refine @measurable_pi_iff Ω _ _ (stageMarks κ b jumps E u l k ℓ) _ _ |>.2 fun i => ?_
      by_cases h : (i : ℕ) < ℓ
      · have e : (fun ω => q ω i) = fun ω => pw ω ⟨i, h⟩ := by funext ω; simp only [hqdef, h, dite_true]
        rw [e]
        exact (measurable_pi_apply _).comp hpw
      · have e : (fun ω => q ω i) = fun _ => r₀ := by funext ω; simp only [hqdef, h, dite_false]
        rw [e]
        exact @measurable_const _ _ _ (stageMarks κ b jumps E u l k ℓ) _
    exact hg.comp (hpu.prodMk hq)
  · filter_upwards [hx'e] with ω hω hl hz h0
    rw [hω (mem_univ ω), hgx]
    show g (pu ω, pc ω) = g (pu ω, q ω)
    congr 2
    funext i
    by_cases h : (i : ℕ) < ℓ
    · simp only [hqdef, h, dite_true]
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞))
          (fun j => Ew j ω) (ℓ + 1)).2.2.1 i) = readRec ((ExplState.run κ b jumps w (fun j => Ew j ω) ℓ).2.2.1 i)
      rw [retained_run_of_lt _ _ (show (i : ℕ) < ℓ + 1 by omega), retained_run_of_lt _ _ h,
        run_capSpec_of_le hℓ.le _ (show (i : ℕ) + 1 ≤ ℓ by omega)]
    · have hiℓ : (i : ℕ) = ℓ := le_antisymm (Nat.lt_succ_iff.1 i.2) (not_lt.1 h)
      simp only [hqdef, h, dite_false]
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞))
          (fun j => Ew j ω) (ℓ + 1)).2.2.1 i) = r₀
      rw [hiℓ, WalkSide.retained_run_capSpec_succ (fun j => Ew j ω) hℓ.le hwℓ hl]
      have hz' : ¬ (Ew ℓ ω).2 ≤ 0 := by
        rw [nonpos_iff_eq_zero]; exact hz
      simp only [readRec, retOf, hr₀, ENNReal.coe_zero, zero_le, min_eq_right, min_eq_left, hz',
        decide_false, ENNReal.toNNReal_zero, h0]

end

end InteractingSLE.Theorem14.SB.Cz
