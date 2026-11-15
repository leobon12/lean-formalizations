/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdStageLoc
import InteractingSLE.Spec.Supplement.WalkUnionMeanAE
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.SB2JLower

/-!
# SB2(2)'s union locality on the physical lines of the lower walk

Packet PROVE-T14-SB2LCOND (round 2), the locality half of the union kernel of SB2(2)'s relative stages (supplement
p. 631: "At every rational ordinary time of the other history, its marked union with `A` has the Gaussian local-set
kernel"; p. 632: "For a walk this approximation is performed within each of its finitely many ordinary stages").

* **`stageUnion_markedLocal`** (generic): the union of the explored sets of two staged programs of one field (after
  `n₁` and `n₂` instructions) is a history-marked local set of the centred field for the joined retained pasts, its
  avoidance events are events of the joined pasts up to null sets, its complement in `ℍ` is a.s. open, and the joined
  pasts are a.s. events of the field (the pattern of the landed `WalkLaw.walkUnion_markedAE`, with the generic stage
  locality `stageSet_markedLocal_of_thm12_thm13`).
* **`sb2LowerLines_markedLocal`** (SB2(2)): for the regularized family `regFam E`, the upper prefix after `k`
  instructions of the scheduled program `upperSpec u l` (the retained history `A`, without its real bridge, which is
  not in `ℍ`) united with the lower walk through instruction `ℓ`, its piece `ℓ` stopped at the deterministic own time
  `τ` (the capped program `capSpec`, whose last piece is the walk's piece `ℓ` stopped at `τ`), is a history-marked
  local set for `pastSigma_upper(k) ⊔ pastSigma_capped(ℓ + 1)`. These are K2's physical lines (`BW1Lines`'s `hloc`)
  for the lifted stage that is the walk's piece `ℓ`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lcd

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The union of the explored sets of two staged programs is a marked local set** for the joined retained pasts
(R58 form), and the joined pasts are almost surely events of the field. -/
theorem stageUnion_markedLocal (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {s₁ s₂ : ExplSpec} {E₁ E₂ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₁ : IsStagedHistory κ b jumps P h s₁ E₁) (hE₂ : IsStagedHistory κ b jumps P h s₂ E₂)
    (hreg₁ : ∀ j ω, IsRegularDriver (E₁ j ω)) (hreg₂ : ∀ j ω, IsRegularDriver (E₂ j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (n₁ n₂ : ℕ) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (pastSigma κ b jumps s₁ E₁ n₁ ⊔ pastSigma κ b jumps s₂ E₂ n₂) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps s₁ E₁ n₁ ω ∪ WalkLaw.stageSet κ b jumps s₂ E₂ n₂ ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ (WalkLaw.stageSet κ b jumps s₁ E₁ n₁ ω ∪ WalkLaw.stageSet κ b jumps s₂ E₂ n₂ ω))) ∧
    pastSigma κ b jumps s₁ E₁ n₁ ⊔ pastSigma κ b jumps s₂ E₂ n₂ ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps s₁ E₁ n₁ ⊔ pastSigma κ b jumps s₂ E₂ n₂)
      (fun ω => WalkLaw.stageSet κ b jumps s₁ E₁ n₁ ω ∪ WalkLaw.stageSet κ b jumps s₂ E₂ n₂ ω)
      (WholeField.centredField h u₀) P := by
  obtain ⟨hA₁, ho₁, hloc₁⟩ := stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE₁ hreg₁ hu₀ n₁
  obtain ⟨hA₂, ho₂, hloc₂⟩ := stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE₂ hreg₂ hu₀ n₂
  have hR₁ := stagedPiecesRegular_of_regular h13 hκ hb hE₁ hreg₁
  have hR₂ := stagedPiecesRegular_of_regular h13 hκ hb hE₂ hreg₂
  obtain ⟨f₁, hf₁, hp₁⟩ := StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE₁ hR₁ n₁
  obtain ⟨f₂, hf₂, hp₂⟩ := StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE₂ hR₂ n₂
  have hd₁ := WalkLaw.pastSigma_le_aeSigma_centred hf₁ hp₁ u₀
  have hd₂ := WalkLaw.pastSigma_le_aeSigma_centred hf₂ hp₂ u₀
  obtain ⟨A₁, -, hA₁ae, hA₁m⟩ := WalkLaw.exists_version_of_aeSigma
    (fun ω => WalkLaw.stageSet_subset_H κ b jumps s₁ E₁ n₁ ω) ho₁ hA₁
  obtain ⟨A₂, -, hA₂ae, hA₂m⟩ := WalkLaw.exists_version_of_aeSigma
    (fun ω => WalkLaw.stageSet_subset_H κ b jumps s₂ E₂ n₂ ω) ho₂ hA₂
  have hloc₁' := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hA₁ae.mono fun ω h => h.symm) hloc₁
  have hloc₂' := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hA₂ae.mono fun ω h => h.symm) hloc₂
  have hU := WalkLaw.isHistoryAvoidanceLocal_union_of_det (WholeField.measurable_centredField hh.1 u₀) hA₁m hA₂m
    hd₁ hd₂ hloc₁' hloc₂'
  refine ⟨fun U hUH => ?_, ?_, sup_le hd₁ hd₂, WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ hU⟩
  · have e : {ω | Disjoint (WalkLaw.stageSet κ b jumps s₁ E₁ n₁ ω ∪ WalkLaw.stageSet κ b jumps s₂ E₂ n₂ ω)
          (U : Set ℂ)} =
        {ω | Disjoint (WalkLaw.stageSet κ b jumps s₁ E₁ n₁ ω) (U : Set ℂ)} ∩
          {ω | Disjoint (WalkLaw.stageSet κ b jumps s₂ E₂ n₂ ω) (U : Set ℂ)} := by
      ext ω
      simp only [mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
    rw [e]
    exact (WalkLaw.aeSigma_mono (le_sup_left : pastSigma κ b jumps s₁ E₁ n₁ ≤ _) _ (hA₁ U hUH)).inter
      (WalkLaw.aeSigma_mono (le_sup_right : pastSigma κ b jumps s₂ E₂ n₂ ≤ _) _ (hA₂ U hUH))
  · filter_upwards [ho₁, ho₂] with ω h1 h2
    have e : ∀ s t v : Set ℂ, s \ (t ∪ v) = (s \ t) ∩ (s \ v) := fun s t v => Set.ext fun z => by
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
      tauto
    rw [e]
    exact h1.inter h2
  · filter_upwards [hA₁ae, hA₂ae] with ω h1 h2
    simp only [h1, h2]

/-- **SB2(2)'s union locality on the lower walk's physical lines.** For the regularized family, the upper prefix after
`k` instructions united with the lower walk through instruction `ℓ` with its piece `ℓ` stopped at own time `τ` is a
history-marked local set of the centred field for the joined retained pasts (R58 form). -/
theorem sb2LowerLines_markedLocal (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))) (τ : ℝ≥0∞)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    WholeField.IsHistoryAvoidanceLocal
      (pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
      (fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω)
      (WholeField.centredField h u₀) P := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := τ) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  exact (stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _) hu₀ k (ℓ + 1)).2.2.2

end InteractingSLE.Theorem14.SB.Lcd
