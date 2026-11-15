/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfSets

/-!
# The joint line sets of SB2(2)'s stages (D51 item 1)

Packet PROVE-SB2-CONDFIN (round 10, D51). D51 adopts NOJUMP's joint second line set at the tails and the root:
`A₂ t = fill (A ∪ B_{≤ℓ}` capped at `t)`, so the union line set `A₁ ∪ A₂` contains the pockets that `A` and B's piece
enclose. LCMEAN's landed family (`Mf.exists_sb2LowerStageSets`, `Ml.exists_sb2LineFamily_cf`) has B's own second
set. The joint set is LCMEAN's construction of `A₁` taken one instruction later (the union of the upper prefix and
B's capped prefix through instruction `ℓ + 1`): LCMEAN's union locality (`Lcd.stageUnion_markedLocal` at
`(k, ℓ + 1)`), a line version (`Lcd.exists_lineVersion`) and the filled version (`Mf.fillVer_package`).

* **`exists_jointStageSets`**: relatively closed measurable sets `A₁`, `A₂`, almost surely
  `fillVer (A ∪ B_{<ℓ})` and `fillVer (A ∪ B_{≤ℓ,τ})`, with `A₁` field-determined, `A₁`, `A₂` local, and the union
  `A₁ ∪ A₂` relatively closed, local, and history-marked local for the joint pasts
  `pastSigma_up(k) ⊔ pastSigma_cap(ℓ + 1)` (the line filtration's `𝓖 τ`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cs

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s retained set and joint explored set at a lower line**: `A₁` almost surely `fillVer (A ∪ B_{<ℓ})`,
`A₂` almost surely `fillVer (A ∪ B_{≤ℓ,τ})`; both local, `A₁` field-determined, and the union relatively closed,
local and history-marked local for the joint pasts through instruction `ℓ + 1`. -/
theorem exists_jointStageSets (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))) (τ : ℝ≥0∞)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A₁ A₂ : Ω → Set ℂ,
      Measurable[mΩ, hittingSigma] A₁ ∧ Measurable[mΩ, hittingSigma] A₂ ∧
      MeasurableSpace.comap A₁ hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
      IsLocalSet A₁ (centredField h u₀) P ∧ IsLocalSet A₂ (centredField h u₀) P ∧
      (∀ ω, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      Measurable[mΩ, hittingSigma] (fun ω => A₁ ω ∪ A₂ ω) ∧
      (∀ ω, A₁ ω ∪ A₂ ω ⊆ H ∧ IsOpen (H \ (A₁ ω ∪ A₂ ω))) ∧
      IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal
        (pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
        (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      ∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
        A₂ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) ω := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := τ) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  set s₁ := Lu.upperSpec u l with hs₁
  set s₂ := capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ with hs₂
  set E₁ := StagedReg.regFam E s₁ with hE₁
  set E₂ := StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) with hE₂
  -- the two marked-local unions
  obtain ⟨hA1, ho1, hd1, hloc1⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k ℓ
  obtain ⟨hA2, ho2, -, hloc2⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k (ℓ + 1)
  have h𝓜₁ : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤ mΩ := sup_le (hup.2.1 k) (hcap.2.1 ℓ)
  have h𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 (ℓ + 1))
  have h𝓜₁𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) :=
    sup_le_sup_left (pastSigma_mono s₂ E₂ (Nat.le_succ ℓ)) _
  -- line versions and their filled versions
  obtain ⟨B₁, hB₁m, hB₁c, hB₁ae, hB₁loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₁⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨B₂, hB₂m, hB₂c, hB₂ae, hB₂loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho2 hA2 hloc2
  obtain ⟨hA₁m, hA₁c, -, hA₁l⟩ := fillVer_package hh0 h𝓜₁ hB₁c hB₁m hB₁loc
  obtain ⟨hA₂m, hA₂c, -, hA₂l⟩ := fillVer_package hh0 h𝓜 hB₂c hB₂m hB₂loc
  -- the union
  have hUm : Measurable[pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1), hittingSigma]
      fun ω => fillVer B₁ ω ∪ fillVer B₂ ω := by
    let _ : MeasurableSpace Ω := pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1)
    exact measurable_union_hitting (hA₁m.mono h𝓜₁𝓜 le_rfl) hA₂m
  have hUloc : IsHistoryAvoidanceLocal (pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1))
      (fun ω => fillVer B₁ ω ∪ fillVer B₂ ω) (centredField h u₀) P := by
    refine Lv.isHistoryAvoidanceLocal_of_ae_enlargement hloc2 ?_ fun U hUH => hUm (measurableSet_avoid U.isOpen hUH)
    filter_upwards [hB₂ae] with ω h2
    rintro z ⟨hz, -⟩
    have hz' : z ∈ B₂ ω := by rw [h2]; exact hz
    exact Or.inr (subset_fillVer (fun ω => (hB₂c ω).1) ω hz')
  have hUc : ∀ ω, fillVer B₁ ω ∪ fillVer B₂ ω ⊆ H ∧ IsOpen (H \ (fillVer B₁ ω ∪ fillVer B₂ ω)) := by
    intro ω
    refine ⟨union_subset (hA₁c ω).1 (hA₂c ω).1, ?_⟩
    have e : H \ (fillVer B₁ ω ∪ fillVer B₂ ω) = (H \ fillVer B₁ ω) ∩ (H \ fillVer B₂ ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, mem_union]
      tauto
    rw [e]
    exact (hA₁c ω).2.inter (hA₂c ω).2
  have hUl : IsLocalSet (fun ω => fillVer B₁ ω ∪ fillVer B₂ ω) (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 (hUm.mono h𝓜 le_rfl) (Eventually.of_forall hUc)).out 4 1).2 hUloc.isAvoidanceLocal
  refine ⟨fillVer B₁, fillVer B₂, hA₁m.mono h𝓜₁ le_rfl, hA₂m.mono h𝓜 le_rfl,
    hA₁m.comap_le.trans hd1, hA₁l, hA₂l, hA₁c, hA₂c, hUm.mono h𝓜 le_rfl, hUc, hUl, hUloc, ?_⟩
  filter_upwards [hB₁ae, hB₂ae] with ω h1 h2
  refine ⟨?_, ?_⟩
  · unfold fillVer; rw [h1]
  · unfold fillVer; rw [h2]

end InteractingSLE.Theorem14.SB.Cs
