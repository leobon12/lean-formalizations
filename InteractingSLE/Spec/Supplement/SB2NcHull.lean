/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcBase

/-!
# F2b′'s retained hull: a version of `A₁ 0` observed through the line filtration

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). **`exists_retVersion`**: the retained union at the start of
B's stage `ℓ` (the upper explored set through `k` with B's explored set before `ℓ`, the set `A₁ 0` of F2b′'s line
family) has a version `K₀`, measurable for the hitting σ-algebra and the line filtration at time `0`
(`𝓖 0 = upper past ⊔ capped lower past`), relatively closed in `ℍ`, and almost surely equal to the filled union
(`Lcd.exists_lineVersion` for each staged history, the union and the fill).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The line filtration's σ-algebra at time `0`: the upper past through `k` and B's past capped at its time `0` in
stage `ℓ` (regularized families). -/
abbrev lineSigma0 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : MeasurableSpace Ω :=
  pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
    pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
      ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)

/-- **The retained union has a version observed through the line filtration at time `0`.** -/
theorem exists_retVersion (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (Bu Bl : Ω → Set ℂ),
      Measurable[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k, hittingSigma]
        Bu ∧
      Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ, hittingSigma] Bl ∧
      (∀ ω, Bu ω ⊆ H ∧ IsOpen (H \ Bu ω)) ∧ (∀ ω, Bl ω ⊆ H ∧ IsOpen (H \ Bl ω)) ∧
      (∀ᵐ ω ∂P, Bu ω = WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω) ∧
      (∀ᵐ ω ∂P, Bl ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ∧
      Measurable[lineSigma0 κ b jumps E u l k ℓ, hittingSigma] (fillVer fun ω => Bu ω ∪ Bl ω) ∧
      (∀ ω, fillVer (fun ω => Bu ω ∪ Bl ω) ω ⊆ H ∧ IsOpen (H \ fillVer (fun ω => Bu ω ∪ Bl ω) ω)) ∧
      ∀ᵐ ω ∂P, fillVer (fun ω => Bu ω ∪ Bl ω) ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  set Eu := StagedReg.regFam E su with hEudef
  set Ew := StagedReg.regFam E w with hEwdef
  have hmu : pastSigma κ b jumps su Eu k ≤ mΩ := (hE' su hsu).2.1 k
  have hmw : pastSigma κ b jumps w Ew ℓ ≤ mΩ := (hE' w hw).2.1 ℓ
  -- the line versions of the two explored sets
  obtain ⟨hAu, hou, hlocu⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh (hE' su hsu) (hreg' su)
    hu₀ k
  obtain ⟨Bu, hBum, hBuc, hBuae, -⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hmu⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) hou hAu hlocu
  obtain ⟨hAw, how, hlocw⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh (hE' w hw) (hreg' w)
    hu₀ ℓ
  obtain ⟨Bl, hBlm, hBlc, hBlae, -⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hmw⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) how hAw hlocw
  -- both pasts lie in the line σ-algebra at time `0`
  have hle_u : pastSigma κ b jumps su Eu k ≤ lineSigma0 κ b jumps E u l k ℓ := le_sup_left
  have hle_w : pastSigma κ b jumps w Ew ℓ ≤ lineSigma0 κ b jumps E u l k ℓ := by
    refine le_trans ?_ le_sup_right
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := -(Real.pi / 2)) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le Ew le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ ℓ)
  have hUm : Measurable[lineSigma0 κ b jumps E u l k ℓ, hittingSigma] fun ω => Bu ω ∪ Bl ω :=
    @LocalSets.measurable_union_hitting Ω (lineSigma0 κ b jumps E u l k ℓ) Bu Bl (hBum.mono hle_u le_rfl)
      (hBlm.mono hle_w le_rfl)
  have hUH : ∀ ω, Bu ω ∪ Bl ω ⊆ H := fun ω => union_subset (hBuc ω).1 (hBlc ω).1
  have hUo : ∀ ω, IsOpen (H \ (Bu ω ∪ Bl ω)) := fun ω => by
    rw [← sdiff_inter_sdiff]
    exact (hBuc ω).2.inter (hBlc ω).2
  refine ⟨Bu, Bl, hBum, hBlm, hBuc, hBlc, hBuae, hBlae, measurable_fillVer hUH hUm,
    fun ω => ⟨fillVer_subset_H hUH ω, isOpen_H_diff_fillVer hUo ω⟩, ?_⟩
  filter_upwards [hBuae, hBlae] with ω hu hl
  have e : Bu ω ∪ Bl ω = WalkLaw.stageSet κ b jumps su Eu k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Ew ℓ ω := by
    rw [hu, hl, WalkInf.stageSet_capSpec_of_le hℓ.le ω le_rfl]
  by_cases hbd : Bornology.IsBounded (Bu ω ∪ Bl ω)
  · rw [fillVer_of_bounded (B := fun ω => Bu ω ∪ Bl ω) hbd, fillVer_of_bounded (e ▸ hbd), e]
  · rw [fillVer_of_not_bounded (B := fun ω => Bu ω ∪ Bl ω) hbd, fillVer_of_not_bounded (e ▸ hbd), e]

end

end InteractingSLE.Theorem14.SB.Nc
