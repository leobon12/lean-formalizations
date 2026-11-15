/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfUnb
import InteractingSLE.Spec.Supplement.SB2LnMean
import InteractingSLE.Spec.Supplement.SB2LcdUnion
import InteractingSLE.Spec.Supplement.WalkStageLocalAE

/-!
# SB2(2)'s retained and explored sets at a lower line: the probabilistic inputs of the union mean

Packet PROVE-SB2-LCMEAN, round 3. `Ln.ae_chartTransport_eq_couplingMean_of_stagePullback` (round 2) takes, besides the
stage-chart geometry and the individual means, the set-level hypotheses of the union-mean engine: measurability,
field-determination of the retained set, locality of both sets and of their union. For SB2(2)'s actual objects — the
upper prefix `A` (program `Lu.upperSpec u l` after `k` instructions), the lower walk `B` before piece `ℓ` and through
piece `ℓ` stopped at own time `τ` (program `capSpec lowerWalk ℓ θ τ` after `ℓ` and `ℓ + 1` instructions), all for the
regularized families — they are proved here from the landed marked locality (Theorems 1.2–1.3 as hypotheses):

* **`exists_sb2LowerStageSets`**: there are relatively closed, measurable sets `A₁`, `A₂`, almost surely the filled
  versions `fillVer (A ∪ B_{<ℓ})` and `fillVer B_{≤ℓ,τ}`, such that `A₁` is field-determined and `A₁`, `A₂` and
  `A₁ ∪ A₂` are local sets of the centred field;
* **`sb2Lower_chartTransport_eq_couplingMean`**: SB2(2)'s union mean in K2's `hmean` form for these sets, from the
  stage-chart geometry (`Ln.IsStagePullback`, the mirrored configuration, the composite relative chart), the
  individual-mean formulas (for every local-set mean of `A₁`, `A₂`) and the unbounded lower-union components of
  the two stage sets (transferred to the filled sets by `not_isBounded_lowerUnion_fillVer`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Mf

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField
open _root_.InteractingSLE.Theorem14.SB.Union (relComp)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s retained and explored sets at a lower line**: relatively closed measurable sets `A₁`, `A₂`, almost
surely the filled versions of `A ∪ B_{<ℓ}` and of `B_{≤ℓ,τ}`, with `A₁` field-determined and `A₁`, `A₂`, `A₁ ∪ A₂`
local sets of the centred field. -/
theorem exists_sb2LowerStageSets (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
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
      IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      (∀ ω, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      ∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
        A₂ ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ω := by
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
  -- the three marked-local sets
  obtain ⟨hA1, ho1, hd1, hloc1⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k ℓ
  obtain ⟨hA2, ho2, hloc2⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hcap (hreg' _) hu₀
    (ℓ + 1)
  obtain ⟨-, -, -, hloc⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k (ℓ + 1)
  have h𝓜₁ : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤ mΩ := sup_le (hup.2.1 k) (hcap.2.1 ℓ)
  have h𝓜₂ : pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤ mΩ := hcap.2.1 (ℓ + 1)
  have h𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 (ℓ + 1))
  have h𝓜₁𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) :=
    sup_le_sup_left (pastSigma_mono s₂ E₂ (Nat.le_succ ℓ)) _
  have h𝓜₂𝓜 : pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) := le_sup_right
  -- line versions and their filled versions
  obtain ⟨B₁, hB₁m, hB₁c, hB₁ae, hB₁loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₁⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨B₂, hB₂m, hB₂c, hB₂ae, hB₂loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₂⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho2 hA2 hloc2
  obtain ⟨hA₁m, hA₁c, -, hA₁l⟩ := fillVer_package hh0 h𝓜₁ hB₁c hB₁m hB₁loc
  obtain ⟨hA₂m, hA₂c, -, hA₂l⟩ := fillVer_package hh0 h𝓜₂ hB₂c hB₂m hB₂loc
  -- the union
  have hUm : Measurable[pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1), hittingSigma]
      fun ω => fillVer B₁ ω ∪ fillVer B₂ ω := by
    let _ : MeasurableSpace Ω := pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1)
    exact measurable_union_hitting (hA₁m.mono h𝓜₁𝓜 le_rfl) (hA₂m.mono h𝓜₂𝓜 le_rfl)
  have hUloc : IsHistoryAvoidanceLocal (pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1))
      (fun ω => fillVer B₁ ω ∪ fillVer B₂ ω) (centredField h u₀) P := by
    refine Lv.isHistoryAvoidanceLocal_of_ae_enlargement hloc ?_ fun U hUH => hUm (measurableSet_avoid U.isOpen hUH)
    filter_upwards [hB₁ae, hB₂ae] with ω h1 h2
    rintro z ⟨hz | hz, -⟩
    · have hz' : z ∈ B₁ ω := by rw [h1]; exact Or.inl hz
      exact Or.inl (subset_fillVer (fun ω => (hB₁c ω).1) ω hz')
    · have hz' : z ∈ B₂ ω := by rw [h2]; exact hz
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
  refine ⟨fillVer B₁, fillVer B₂, hA₁m.mono h𝓜₁ le_rfl, hA₂m.mono h𝓜₂ le_rfl,
    hA₁m.comap_le.trans hd1, hA₁l, hA₂l, hUl, hA₁c, hA₂c, ?_⟩
  filter_upwards [hB₁ae, hB₂ae] with ω h1 h2
  refine ⟨?_, ?_⟩
  · unfold fillVer; rw [h1]
  · unfold fillVer; rw [h2]

/-- **SB2(2)'s union mean at a lower line, in K2's `hmean` form, for the actual retained and explored sets**: with
`A₁`, `A₂` the sets of `exists_sb2LowerStageSets` (almost surely the filled `A ∪ B_{<ℓ}` and `B_{≤ℓ,τ}`), for every
local-set mean `g` of `A₁ ∪ A₂`: given the unbounded lower-union components of the two stage sets, the stage-chart
geometry (`Ln.IsStagePullback`), the
mirrored configuration, the individual-mean formulas (for every local-set mean of `A₁`, `A₂`) and the composite
relative chart, the chart transport of `g + u₀` is the relative coupling mean. -/
theorem sb2Lower_chartTransport_eq_couplingMean (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))) (τ : ℝ≥0∞)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A₁ A₂ : Ω → Set ℂ,
      (∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
        A₂ ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ω) ∧
      ∀ {g : Ω → DistOn upperHalfPlaneOpens},
        IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P g →
        (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion
            (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
              WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
                (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω),
          ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion
            (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
              WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
                (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)) z)) →
        (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion
            (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω),
          ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion
            (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω)) z)) →
        ∀ {c : Ω → Chart} {gb : Ω → ℂ → ℂ} {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ}
          {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ} {tt ur : Ω → ℝ} {lam : ℝ} {β₀ βE βu : Ω → ℝ → ℝ}
          {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ} {D : Set Ω},
        (∀ᵐ ω ∂P, ω ∈ D → Ln.IsStagePullback (c ω) (gb ω) (A₁ ω) (A₂ ω) (A ω) (fwdHull (w ω) (tt ω))) →
        (∀ᵐ ω ∂P, ω ∈ D → Lm.IsRelConfigJKL (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω)
          (tt ω) (ur ω) (chiC κ) lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω)) →
        (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₁ (centredField h u₀) P g₁ →
          ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => G₀ ω (Ψ ω ((c ω).1 z)) - chiC κ * ((LΨ ω ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₁ ω)) →
        (∀ g₂ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g₂ →
          ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
            EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (tt ω) ((c ω).1 z)) -
              chiC κ * ((logDerivFwd (w ω) (tt ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ ω)) →
        ∀ {crel : Ω → Chart} (hcr : ∀ ω, (crel ω).IsConformal), (∀ ω, ContinuousOn (crel ω).2.2 (crel ω).dom) →
        (∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (crel ω).2.1 y = (c ω).2.1 (Ψi ω y)) → ∀ {ℓ₀ : ℝ},
        (∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (crel ω).2.2 ((crel ω).2.1 y) =
          (LΨ ω (Ψi ω y)).im + (c ω).2.2 ((crel ω).2.1 y) + ℓ₀) →
        ∀ a : ℝ, ∀ᵐ ω ∂P, ω ∈ D → ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wr ω) (ur ω)) →
          Chart.chartTransport (hcr ω) 1 a (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
            ∫ y, couplingMean κ (Wr ω) (ur ω) (fun z => G ω z + (a + chiC κ * ℓ₀)) y * ψ y := by
  obtain ⟨A₁, A₂, hA₁m, hA₂m, hd₁, hl₁, hl₂, hlU, -, -, hae⟩ :=
    exists_sb2LowerStageSets h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ τ hu₀
  refine ⟨A₁, A₂, hae, ?_⟩
  intro g hg hunbS₁ hunbS₂ c gb A Ψ Ψi LΨ Sb w Wr η ηr tt ur lam β₀ βE βu S₀ SE Su G₀ GE G v D hpb hcfg hind₁ hind₂
    crel hcr hcrℓ hcrinv ℓ₀ hcrlift a
  have hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z) := by
    filter_upwards [hae, hunbS₁] with ω he hs
    rw [he.1]
    exact not_isBounded_lowerUnion_fillVer
      (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
      ω hs
  have hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z) := by
    filter_upwards [hae, hunbS₂] with ω he hs
    rw [he.2]
    exact not_isBounded_lowerUnion_fillVer (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ω hs
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₁m hl₁
  obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₂m hl₂
  exact Ln.ae_chartTransport_eq_couplingMean_of_stagePullback hh0 hu₀.1 hu₀.2.1 hA₁m hA₂m hd₁ hl₁ hl₂ hlU
    hunb₁ hunb₂ hg hg₁ hg₂ hpb hcfg (hind₁ g₁ hg₁) (hind₂ g₂ hg₂) hcr hcrℓ hcrinv hcrlift a

end InteractingSLE.Theorem14.SB.Mf
