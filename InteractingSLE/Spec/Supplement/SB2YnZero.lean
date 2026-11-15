/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YmZero
import InteractingSLE.Spec.Supplement.SB2YnHead
import InteractingSLE.Spec.Supplement.SB2YnLaw

/-!
# The zero piece widened to pieces at `relOff` that die no later than their entrance at `R`

Packet PROVE-T14-SB2LIFT (round 38, decision D89, CANON's handoff R9.2 option (A)). CANON's R9.2 finds one root
sample type in no piece of the induction step: `relOff = ℓ`, off a zero root, `0 < ζ_ℓ` and `ζ_ℓ = entrR` (B's piece
first reaches `R` exactly at its death). Its piece runs only up to `R`, so the retained hull does not change. This
file widens SB2LIFT's `Sz.zero_piece_root` from `ζ_ℓ = 0` to
`ζ_ℓ = 0 ∨ (upper launch ∧ relOff = ℓ ∧ ¬ ZeroRoot ∧ ζ_ℓ ≤ entrR)`. The upper launch holds at every sample of the step's
coverage.

* `ae_stage_subset_hull`: in both cases the stage set two stages on lies in the hull `A₁ 0` of stage `ℓ`, and the
  hull `A₁' 0` of stage `ℓ + 2` is `A₁ 0` (`Sz.ae_stage_succ_succ_subset`, `Sx.fillVer_eq_of_subset`).
* `ae_leftAdm_root_fill`: `Sz.ae_leftAdm_zero_root` with the hull identity as a premise in place of `ζ_ℓ = 0`.
* **`zero_piece_rootE`**: `Sz.zero_piece_root` on `C ∩ {launch at ℓ, ζ_ℓ = 0 ∨ (…), ¬ (relOff = ℓ ∧ ZeroRoot)}`,
  with the same word and profiles and the same inputs (including `hLR`). The law is `Fl.mvLaw_succ_succ_fill`
  (`SB2YnLaw`). The left heights use `Fo.ae_leftAdm_zero` off `relOff = ℓ` (where `ζ_ℓ = 0`) and
  `ae_leftAdm_root_fill` at `relOff = ℓ`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Fs

/-- **The retained hull does not grow over the stages `ℓ`, `ℓ + 1`**, almost surely, at a zero lifetime or at a
piece at `relOff = ℓ` (an upper launch, off a zero root) dying no later than its entrance at `R`: the regularized stage
set after `ℓ + 2` instructions lies in the hull `A₁` of stage `ℓ`, and the hull `A₁'` of stage `ℓ + 2` is `A₁`. -/
theorem ae_stage_subset_hull (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {A₁ A₁' : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∨
        (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
          relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
          ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≤ Nd.entrR κ b jumps E u l k ℓ ω)) →
      IsHPHull (A₁ ω) →
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω ⊆ A₁ ω ∧
        A₁' ω = A₁ ω := by
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨-, -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hℓ₂le : ℓ + 2 ≤ w.2.2.length := (List.getElem?_eq_some_iff.1 hwℓ₂).1.le
  filter_upwards [ae_stage_succ_succ_subset h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft, hA, hA',
    hrun su hsu] with ω hsub hAω hA'ω hru hlℓ hcase hHP
  set U := WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω with hU
  set Sℓ := WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω with hSℓ
  set S₂ := WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) (ℓ + 2) ω with hS₂
  have hℓlt : ℓ ≤ w.2.2.length := (SB.Nc.flow_of_launch hlℓ).1.le
  have hF : A₁ ω = Mf.fillVer (fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) ω := by
    rw [hAω]
    exact Qr.fillVer_congr (by rw [WalkInf.stageSet_capSpec_of_le hℓlt ω le_rfl])
  have hF' : A₁' ω = Mf.fillVer (fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) (ℓ + 2) ω) ω := by
    rw [hA'ω]
    exact Qr.fillVer_congr (by rw [WalkInf.stageSet_capSpec_of_le hℓ₂le ω le_rfl])
  have hB₁H : U ∪ Sℓ ⊆ H := union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)
    (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)
  have hHP' : IsHPHull (Mf.fillVer (fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) ω) := hF ▸ hHP
  have hb₁ : Bornology.IsBounded (U ∪ Sℓ) := by
    by_contra hnb
    rw [Mf.fillVer_of_not_bounded (B := fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) hnb] at hHP'
    exact hnb hHP'.2.1
  have hfillU : fillH (closure U) = fillH (upperPrefix κ b jumps E u l k ω) := by
    rw [hU, Qt.stageSet_eq_prefixPhysSet_inter_H, Mo.fillH_closure_inter_H]
    show _ = fillH (SB.prefixPhysSet κ b jumps su (fun j => E su j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0)
    rw [Lw.fillH_union_real]
    unfold SB.prefixPhysSet
    rw [hru k]
  have hsubA : S₂ ⊆ A₁ ω := by
    intro z hz
    rcases hsub hlℓ hcase hz with hz1 | hz2
    · rw [hF]
      exact Mf.subset_fillVer (B := fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
        WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) (fun ω => union_subset
          (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)) ω (Or.inr hz1)
    · have h1 : fillH (upperPrefix κ b jumps E u l k ω) ⊆ A₁ ω := by
        rw [← hfillU, hF, Mf.fillVer_of_bounded (B := fun ω => WalkLaw.stageSet κ b jumps su
          (StagedReg.regFam E su) k ω ∪ WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) hb₁]
        exact fillH_mono (closure_mono subset_union_left)
      exact h1 hz2
  refine ⟨hsubA, ?_⟩
  have hmono : Sℓ ⊆ S₂ := by
    rw [hSℓ, hS₂, show ℓ + 2 = ℓ + 1 + 1 from rfl, WalkLaw.stageSet_succ, WalkLaw.stageSet_succ]
    exact subset_union_left.trans subset_union_left
  have hUA : U ⊆ A₁ ω := by
    rw [hF]
    exact subset_union_left.trans (Mf.subset_fillVer (B := fun ω => WalkLaw.stageSet κ b jumps su
      (StagedReg.regFam E su) k ω ∪ WalkLaw.stageSet κ b jumps w (StagedReg.regFam E w) ℓ ω) (fun ω => union_subset
        (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)) ω)
  rw [hF', hF]
  exact Sx.fillVer_eq_of_subset hB₁H (union_subset_union_right _ hmono) hHP'
    (by rw [← hF]; exact union_subset hUA hsubA)

/-- **D34's left heights at `relOff = ℓ` when the hull does not change**, almost surely: off a zero root, at a launch
at `ℓ + 2` with the hull of stage `ℓ + 2` equal to the one of stage `ℓ`, the word admissible left of `R`'s entry
stays admissible left of the new entry (as `ae_leftAdm_zero_root`, with the hull identity as a premise). -/
theorem ae_leftAdm_root_fill (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁ A₁' : Ω → Set ℂ}
    (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    {β : Ω → BoundaryWord} :
    ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ →
      ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      A₁' ω = A₁ ω →
      IsHPHull (A₁ ω) → Fm.FreeRight (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)) →
      Fm.LeftAdm κ (β ω) (Fm.entry (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω))) →
      (∀ x r : ℝ, 0 < r → Disjoint (ball (x : ℂ) r) (A₁ ω) → x ∉ jumps →
        Fm.bdryVal (A₁ ω) x ∉ (β ω).jumps → (β ω).fn (Fm.bdryVal (A₁ ω) x) = b x) →
      Fm.LeftAdm κ (β ω) (Fm.entry (A₁' ω) (stPt (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)))) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  by_cases hℓ2 : ℓ + 2 < w.2.2.length
  swap
  · exact Eventually.of_forall fun ω _ hl2 => absurd (SB.Nc.flow_of_launch hl2).1 hℓ2
  filter_upwards [SB.Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft,
    SB.Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hℓ2,
    Fo.ae_free_between_seeds h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA',
    Sx.ae_root_seed h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft]
    with ω hg hgeo2 hfree hseed hev hl2 hoff hZ hAA hHP hFR hLR hread
  have hgω := hg hev.1
  rw [hAA]
  -- the seeds: B's point at `ℓ` is left of `R`, the next seed right of it
  obtain ⟨hpt, hRin⟩ := hseed hev hoff hZ
  have hRp' : realMax (upperPrefix κ b jumps E u l k ω) ≤
      stPt (ExplState.run κ b jumps w (fun i => E w i ω) (ℓ + 2)) := by
    have hmem : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈ SB.Nc.retX κ b jumps E u l k (ℓ + 2) ω :=
      Or.inr (WalkIntRunChron.prefixPhysSet_mono w _ (by omega : ℓ + 1 ≤ ℓ + 2) hRin)
    obtain ⟨hXc2, -, -, -, -⟩ := hgeo2 hl2
    have hmax2 := SB.Nc.realMax_retX_eq hgω hl2 (lt_of_eq_of_lt hoff (by omega)) (SB.Nc.even_of_launch hl2)
    rw [← hmax2]
    exact SB.Lx.le_realMax_of_mem hXc2 hmem
  refine Fo.leftAdm_entry_mono (b := b) (jumps := jumps) hHP hFR hRp' hLR (fun x hx hxJ hyJ => ?_)
    (fun x hx hxp' hxJ => ?_)
  · obtain ⟨r, hr, hd⟩ := hFR x hx
    exact hread x r hr hd hxJ hyJ
  · obtain ⟨r, hr, hd⟩ := hFR x hx
    exact hfree hev hl2 x (lt_of_le_of_lt hpt hx) hxp' ⟨r, hr, by rw [hAA]; exact hd⟩ hxJ

/-- **The zero step of the induction, widened to pieces at `relOff = ℓ` dying no later than their entrance at
`R`** (Theorems 1.2–1.3). See the module docstring. -/
theorem zero_piece_rootE (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {A₁ A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ᵐ ω ∂P, A₁ 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    -- the line family's local-set facts for `A₁ 0`
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] (A₁ 0))
    (hAc : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (centredField h u₀) P)
    -- the stage data at `ℓ`
    {C : Set Ω} {β : Ω → BoundaryWord} {S : Set Lv.WordProfile}
    (hst : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S)
    -- the base's root facts at `R` for the stage word (CANON's `Cz.StageInv`)
    (hLR : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
        Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) :
    StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁'
      (C ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∨
          (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
            relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
            ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≤ Nd.entrR κ b jumps E u l k ℓ ω)) ∧
        ¬ (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
          ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))}) β S := by
  obtain ⟨⟨K, G, Y, M, hlaw, hcov⟩, hβm, hS, hprof, hL⟩ := hst
  obtain ⟨G₂, hlaw₂, hcov₂⟩ := Fl.mvLaw_succ_succ_fill h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ k ℓ
    hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw
  have h𝓜 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : IsLocalSet (A₁ 0) (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hloc.isAvoidanceLocal
  have hread := Fo.ae_read_of_meanIdentity hh hu₀ hAm hl hlaw.2.2.2.2.2.2.2.2.1
    (Fq.hmean_of_law hh hu₀ h𝓜 hAm hAc hloc hlaw (S := G) (Eventually.of_forall fun _ h => h))
  have hzero := Fo.ae_leftAdm_zero h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA hA' (β := β)
  have hzr := ae_leftAdm_root_fill h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft (A₁ := A₁ 0) hA'
    (β := β)
  have hhull := ae_stage_subset_hull h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hwℓ₂ hA hA'
  refine ⟨⟨K, G₂, Y, M, hlaw₂, ?_⟩, hβm.mono (WalkLaw.aeSigma_mono (P := P) (Mz.stageMarks_mono (by omega)))
    le_rfl, hS, ?_, ?_⟩
  · filter_upwards [hcov, hcov₂, hhull, hlaw.2.2.2.2.1] with ω e1 e2 e3 ef hω hl2
    have hG := e1 hω.1 hω.2.1
    have hHP : IsHPHull (A₁ 0 ω) := ef hG ▸ Mo.isHPHull_fillH hlaw.2.1 hlaw.2.2.1 ω
    exact e2 hG hl2 (e3 hω.2.1 hω.2.2.1 hHP).1
  · filter_upwards [hprof] with ω e1 hω _ using e1 hω.1 hω.2.1
  · filter_upwards [hL, hzero, hread, hcov, hlaw.2.2.2.2.1, hLR, hzr, hhull] with ω eL ez er ec ef eR ezr eh hω hev2
      hoff2
    obtain ⟨hC, hlℓ, hcase, hne⟩ := hω
    have hev : ω ∈ stageEvent κ b jumps E u l k ℓ := ⟨hev2.1, hlℓ⟩
    have hG : ω ∈ G := ec hC hlℓ
    have hHP : IsHPHull (A₁ 0 ω) := ef hG ▸ Mo.isHPHull_fillH hlaw.2.1 hlaw.2.2.1 ω
    by_cases hro : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ
    · -- `relOff = ℓ` off a zero root: the hull does not change, seeded at `R`
      have hZ : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) := fun hZ => hne ⟨hro, hZ⟩
      obtain ⟨hFR, hLadm⟩ := eR hev hro.ge
      exact ezr hev hev2.2 hro hZ (eh hlℓ hcase hHP).2 hHP hFR hLadm
        (fun x r hr hd hxJ hyJ => er hG hHP x r hr hd hxJ hyJ)
    · have hz : (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 :=
        hcase.resolve_right fun h => hro h.2.1
      have he1 := Nc.even_of_launch hlℓ
      have he2 := relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      have hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ := by omega
      exact (ez hev hev2.2 hoff hz (eL hC hev hoff) (fun x r hr hd hxJ hyJ => er hG hHP x r hr hd hxJ hyJ)).2.2

end InteractingSLE.Theorem14.SB.Sz
