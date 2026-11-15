/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RLift
import InteractingSLE.Spec.Supplement.SB2LwLift
import InteractingSLE.Spec.Supplement.SBFinPositive
import InteractingSLE.Spec.Supplement.WalkContinuum

/-!
# SB4's distinct-seed leaf, lower-walk half, with R95's premise

Packet PROVE-T14-SB4LEAF. The first conjunct of `Ly.SB4DistinctSeedLaunchTailRStatement` (the switch data of an upper
schedule from `u ≤ 0` against the right side of the completed lower walk, ruling R95's form) from

* SB2(2) in R99's form (`Lz.SB2LowerLaunchEntryAdmStatement`, PROVE-T14-SB2FIN5's target),
* the pointwise lift of SB2(2)'s lower tail (`Lf.SB2LowerTailLiftStatement`, named input),
* the lower walk's properness (`WalkCont.RightWalkProperRegStatement`, from Theorems 1.2–1.3) and Theorem 1.3.

At every switch: the launch parametrization and its rational incidence (`Side.exists_rightSide_launch_param`), the
lifetime alternative (`Retain.ae_launch_word_cases`), the launch readout (`Retain.ae_launch_chosenTrace_readout`),
and the frame (`Lf.ae_relTailGeometry_of_lift`). On the zero-lifetime branch the sewing certificate needs no SB3
(`HasRelTailGeometry.hasActualTailSewing_zero`); on the positive branch SB2(2)'s output supplies R95's premise
(`Lz.lowerLeftAdmissible_of_activeHighWord`), the staged lower walk and the word.

* `upperPrefix_inter_rightSideOf`: the bridge adds no point of the right side;
* **`scheduleLaunchTailR_lower_lift`** (ruling R104a): from SB2(2)'s combined target `Lh.SB2LowerLaunchLiftStatement`
  (an output whose completed lower tail lifts; PROVE-T14-SB2LOW);
* `sb2LowerLaunchLiftStatement_of_pair` and `scheduleLaunchTailR_lower`: the round-1 form, from R99's SB2(2) and the
  every-output lift `Lf.SB2LowerTailLiftStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule

/-- The real bridge adds no point of a right side (`rightSideOf` lies in `ℍ`). -/
theorem upperPrefix_inter_rightSideOf {X B : Set ℂ} {u : ℝ} (h : X ∩ rightSideOf B = ∅) :
    (X ∪ ((↑) : ℝ → ℂ) '' Icc u 0) ∩ rightSideOf B = ∅ := by
  rw [union_inter_distrib_right, h, empty_union]
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨⟨y, -, hy⟩, hz⟩ := hz
  have := hz.1.1
  rw [← hy] at this
  exact absurd (show (0 : ℝ) < ((y : ℂ)).im from this) (by simp)

/-- The retained prefix of the actual history is the one at the retained realization, conditionally almost surely,
so the avoidance of a right side passes to every conditional sample. -/
theorem ae_ae_prefix_avoid {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ} {S : Ω → Set ℂ}
    (havoid : ∀ᵐ ω ∂P, prefixPhysSet κ b jumps spec (fun j => E j ω) k ∩ S ω = ∅) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      prefixPhysSet κ b jumps spec (fun j => E j ω₀) k ∩ S ω = ∅ := by
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae (hE.2.1 k) havoid,
    Retain.ae_ae_run_eq spec hR (hE.2.1 k) le_rfl] with ω₀ h1 h2
  filter_upwards [h1, h2] with ω hω hrun
  have he : prefixPhysSet κ b jumps spec (fun j => E j ω₀) k = prefixPhysSet κ b jumps spec (fun j => E j ω) k := by
    unfold prefixPhysSet; rw [hrun]
  rw [he]; exact hω

/-- **SB4's distinct-seed leaf, lower-walk half, with R95's premise**: for an upper schedule from `u ≤ 0` with angles in
`(−π/2, π/2]`, the bridge's lower left groups admissible and the hybrid bridge condition, every switch has the
launch-form data `Ly.HasScheduleLaunchTailR` against the right side of the completed lower walk. -/
theorem scheduleLaunchTailR_lower_lift (hC : Lh.SB2LowerLaunchLiftStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2)) {u : ℝ} (hu : u ≤ 0)
    (hθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) :
    ScheduleLaunchTailR κ b jumps P h E u l (b '' {x | x ∈ Ioo u 0 ∧ x ∉ jumps})
      (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω)) := by
  intro k hk hprev
  have hprog : IsBoundaryContinuedProgram (upperSpec u l).2.2 :=
    GW2Sched.isBoundaryContinuedProgram_scheduleProgram (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  have hEu := hE _ hprog
  have hRu := hreg _ hprog
  have hprogL := Fin.isBoundaryContinuedProgram_lowerWalk b jumps
  obtain ⟨a, ham, hareg⟩ := Side.exists_rightSide_launch_param hb hEu.1 hRu (hE _ hprogL).1 (hreg _ hprogL) hk
  refine ⟨a, ham, hareg, ?_⟩
  -- SB2(2)'s premise at the launch samples
  have hleftP : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅ :=
    hprev.mono fun ω hω _ => upperPrefix_inter_rightSideOf hω
  have hout := hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg u l k hu hl hθ hL hleftP
  have hβQ := KernelTower.ae_ae_condExpKernel_of_ae (hEu.2.1 k)
    (hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg)
  have havQ := ae_ae_prefix_avoid hEu hRu hprev
  filter_upwards [hout, hβQ, havQ, Retain.ae_launch_word_cases hκ hb hEu hRu k,
    Retain.ae_launch_chosenTrace_readout h13 hκ hEu hRu hk, hRu.ae_pieceRegular]
    with ω₀ hout₀ hβ₀ hav₀ hwc hread hreg₀
  intro c θ hlaunch
  obtain ⟨hcc, bc, jc, hl₀, hbc, hct, hG, hfl₀, hcases⟩ := hwc c θ hlaunch
  obtain ⟨f, -, hf, hfc, -, hreadW⟩ := hread c θ hlaunch
  -- the geometry for any witness with any SB2(2) output
  have hgeo : ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (hl' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
      (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      IsFlowLineDriver κ b' J' θ
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) hl'
        (fun t ω => (E (upperSpec u l) k ω).1 t) (fun ω => (E (upperSpec u l) k ω).2) →
      IsLowerLaunchOutput κ b jumps P E u l k ω₀ c b' J' hl' m EL →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (∃ y : ℝ, y < 0 ∧ y < realMin (upperPrefix κ b jumps E u l k ω₀) ∧
            (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
          ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
            IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
              (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        HasRelTailGeometry (schedulePiece κ b jumps u l (fun j => E (upperSpec u l) j ω) k)
          (rightSideOf (lowerWalkSet κ b jumps E ω))
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω) m
          (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E (upperSpec u l) k ω).1 t)
            (fun ω => (E (upperSpec u l) k ω).2) ω t)) (E (upperSpec u l) k ω).2 :=
    fun b' J' hl' m EL hfl' hout' hlift' =>
      ae_relTailGeometry_of_lift h13 hκ hu hreg₀ hlaunch hcc hf hfc hfl'
        ((hreadW b' J' hl' hfl').mono fun _ hω => hω.2.1) hout'.1 hout'.2.2.1 hβ₀ hlift' hav₀
  rcases hcases with hzero | hpos
  · -- zero lifetime: the sewing certificate without SB3
    refine Or.inl ?_
    obtain ⟨m, EL, hout', hlift'⟩ := hout₀ c θ hlaunch bc jc hl₀ hbc hct hG
    filter_upwards [hgeo bc jc hl₀ m EL hfl₀ hout' hlift', hzero]
      with ω hg hz _
    rw [hz.1] at hg
    exact hg.hasActualTailSewing_zero
  · -- positive lifetime: the relative data with R95's premise
    refine Or.inr fun b' J' hl' hb' hct' hfl' => ?_
    have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl'
    obtain ⟨m, EL, hout', hlift'⟩ := hout₀ c θ hlaunch b' J' hl' hb' hct' hG'
    have hg := hgeo b' J' hl' m EL hfl' hout' hlift'
    obtain ⟨hm, hlm, -, hword, hst, hregL, -, -⟩ := hout'
    exact ⟨m, EL, hm, Lz.lowerLeftAdmissible_of_activeHighWord hκ hκ4 (fun p hp => (hθ p hp).1) hL hlm hword,
      fun _ => ⟨hst, hregL⟩, hword, hpos, hg.mono fun _ hω _ => hω⟩

/-- **R99's SB2(2) with the every-output lift give the combined target** (R104a's form is weaker than the pair). -/
theorem sb2LowerLaunchLiftStatement_of_pair (hSB2 : Lz.SB2LowerLaunchEntryAdmStatement.{u})
    (hLift : SB2LowerTailLiftStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [sb2LowerSetting_output_of_adm hSB2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hl
    hlθ hL hleft, hLift κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft] with ω₀ h₀ h₁
  intro c θ hcθ b' J' h' hb' hT' hG'
  obtain ⟨m, EL, hout⟩ := h₀ c θ hcθ b' J' h' hb' hT' hG'
  exact ⟨m, EL, hout, h₁ c θ hcθ b' J' h' hb' hT' hG' m EL hout⟩

/-- **The lower-walk half in the round-1 form** (R99's SB2(2) and the every-output lift). -/
theorem scheduleLaunchTailR_lower (hSB2 : Lz.SB2LowerLaunchEntryAdmStatement.{u})
    (hLift : SB2LowerTailLiftStatement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2)) {u : ℝ} (hu : u ≤ 0)
    (hθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) :
    ScheduleLaunchTailR κ b jumps P h E u l (b '' {x | x ∈ Ioo u 0 ∧ x ∉ jumps})
      (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω)) :=
  scheduleLaunchTailR_lower_lift (sb2LowerLaunchLiftStatement_of_pair hSB2 hLift) hPR h13 hκ hκ4 hb hh hcf hζ' hE
    hreg hl hu hθ hL

end InteractingSLE.Theorem14.SB.Lf
