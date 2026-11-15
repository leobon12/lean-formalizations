/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3LtCut
import InteractingSLE.Spec.Supplement.SBS3LtOld
import InteractingSLE.Spec.Supplement.SBS3TerminalAfterMean
import InteractingSLE.Spec.Supplement.SBS3TerminalUnion
import InteractingSLE.Spec.Supplement.SB2LgChain
import InteractingSLE.Spec.Supplement.SBS3RetainedSchedule
import InteractingSLE.Spec.Supplement.SB2JqStage
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Lemma S3's tail form for SB2(2)'s lower walk (`ℍ`-form), from Theorems 1.2–1.3

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles exchanged, supplement p. 631; ruling R120, decision D6
addendum: "after the walk's visit to `R`, no lower piece runs along the upper history for a time interval"). R48:
Theorems 1.2 and 1.3 at universes `u` and `0` are the only inputs.

The comparison (Fable reviewer, DECISIONS-FABLE-3): both histories enter with their actual stage means and side labels
— the upper schedule prefix at `k` (old, right entry chart at `R`, `old_sample_facts_right`) and the lower walk capped
at a rational own time `q` of the piece carrying the cut (`second_sample_facts_walk`, `exists_walk_cut`); the protected
union means of the two explored sets (`ae_markedUnionMeans_stages`); the lower core
`exists_protectedWordComparison_lower`;
the heights `±λ − ψχ` and `±λ + (π/2)χ` never agree (`ProtectedWordComparison.false_two_old`).

* `ae_capStageFacts`: the capped stage's mean, labels and union means, almost surely (countably many `(j, q)`);
* **`ae_lowerTail_noArc_H`**: the P-level statement;
* **`SB2LowerWalkTailNoCommonArcHStatement`**, **`sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13`**: the kernel
  form (`Lf.SB2LowerSetting`), with the conclusion `¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw Restart WalkSide LocalSets

/-- **The capped stage's actual mean, labels and union means, almost surely** (Theorems 1.2–1.3). For a staged
program `w` with an everywhere-regular staged history `Ew` and an unstopped angle-`θ` flow at `j`, capped at the own
time `q`, and any staged history `(sA, EA)` with an actual mean `g₁` of a version `A₁` of its explored set at `kA`:
almost surely there are the capped explored set's version `A₂`, its actual mean `g₂` and a sorted word `β₂` with the
physical side labels and the mean formula on the capped run chart (at a launch), and the protected union means of
`A₁`, `A₂` at every common point and radii. -/
theorem ae_capStageFacts (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {sA : ExplSpec} {EA : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEA : IsStagedHistory κ b jumps P h sA EA)
    (hRA : StagedPiecesRegular κ b jumps P sA EA) {kA : ℕ}
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A₁ : Ω → Set ℂ} {g₁ : Ω → DistOn upperHalfPlaneOpens} (hA₁m : Measurable[mΩ, hittingSigma] A₁)
    (hA₁eq : ∀ᵐ ω ∂P, A₁ ω = WalkLaw.stageSet κ b jumps sA EA kA ω)
    (hg₁ : IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁)
    {w : ExplSpec} {Ew : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEw : IsStagedHistory κ b jumps P h w Ew)
    (hRw : StagedPiecesRegular κ b jumps P w Ew) (hregw : ∀ j ω, IsRegularDriver (Ew j ω))
    {j : ℕ} (hjl : j < w.2.2.length) {θ : ℝ} (hwj : w.2.2[j]? = some (Sum.inl (θ, ⊤))) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (A₂ : Set ℂ) (g₂ : DistOn upperHalfPlaneOpens) (β₂ : BoundaryWord),
      A₂ ⊆ H ∧ IsOpen (H \ A₂) ∧ A₂ = WalkLaw.stageSet κ b jumps (capSpec w j θ q) Ew (j + 1) ω ∧
      IsHarmonicDistOn g₂ (H \ A₂) ∧
      ((ExplState.run κ b jumps (capSpec w j θ q) (fun i => Ew i ω) (j + 1)).2.2.2.1 j ≠ none →
        min (instrTime (capSpec w j θ q) j) (Ew j ω).2 ≠ ⊤ →
        β₂.IsSorted ∧ HasInteriorStageSides κ b jumps (capSpec w j θ q) (fun i => Ew i ω) (j + 1) β₂ ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ → g₂ φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ *
              (ExplState.run κ b jumps (capSpec w j θ q) (fun i => Ew i ω) (j + 1)).2.2.2.2.1.2.2 z)
            (fun z => β₂.mean ((ExplState.run κ b jumps (capSpec w j θ q) (fun i => Ew i ω) (j + 1)).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps (capSpec w j θ q) (fun i => Ew i ω) (j + 1)).2.2.2.2.1.dom) ∧
      ∀ vA vB : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vA (H \ A₁ ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, vA z * φ z) →
        InnerProductSpace.HarmonicOnNhd vB (H \ A₂) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ → g₂ φ = ∫ z, vB z * φ z) →
        ∀ p : ℂ, p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} → p ∈ A₂ ∪ {z : ℂ | z.im = 0} →
        ∀ rA > 0, ∀ rB > 0,
          MarkedUnionMeans (A₁ ω) A₂ (FinRel.freeNear A₂ (A₁ ω) p rA ∩ FinRel.freeNear (A₁ ω) A₂ p rB) p vA vB := by
  have hEc : IsStagedHistory κ b jumps P h (capSpec w j θ q) Ew :=
    isStagedHistory_capSpec hb hEw hregw hjl hwj
  have hRc := stagedPiecesRegular_capSpec hRw hjl.le hwj q
  obtain ⟨A₂, g₂, β₂, Y₂, hA₂m, hA₂c, hA₂eq, hg₂, -, -, hm₂⟩ :=
    exists_postMean_interiorStageSides h12p h13 hκ hκ4 hb hh hEc hRc hregw hu₀ j
  have hU := ae_markedUnionMeans_stages h12p h13 hκ hκ4 hb hh hEA hEc hRA hRc hu₀ kA (j + 1) hA₁m hA₂m
    hA₁eq hA₂eq hg₁ hg₂
  filter_upwards [hA₂eq, hg₂.2.1, hm₂, hU] with ω h1 h2 h3 h4
  refine ⟨A₂ ω, g₂ ω, β₂ ω, (hA₂c ω).1, (hA₂c ω).2, h1, h2, fun hl hf => ?_, h4⟩
  obtain ⟨hs, hsd, -, hmean⟩ := h3 hl hf
  exact ⟨hs, hsd, hmean⟩

end InteractingSLE.Theorem14.SB.S3.Asm

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw Restart WalkSide LocalSets GW1Bookkeep
open Supp9B (IsProperCurve)

/-- **Lemma S3's tail form for SB2(2)'s lower walk, in `ℍ`, almost surely** (Theorems 1.2–1.3; R48). In SB2(2)'s
setting (upper schedule from `u ≤ 0` with angles in `(−π/2, π/2]`, the lower walk of angle `−π/2` from `0`, the
counterflow, the upper prefix not on the right of the walk), almost surely at a launch `k` of the upper schedule: for
every proper parametrization `β₀` of the lower walk and its visit `t_R` to `R = max (A ∩ ℝ)`, no open time interval
after `t_R` maps into `A ∩ ℍ`, `A` the upper prefix with the bridge `[u, 0]`. -/
theorem ae_lowerTail_noArc_H (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0)
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ tR : ℝ≥0, β₀ tR = (realMax (upperPrefix κ b jumps E u l k ω) : ℂ) →
        ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ upperPrefix κ b jumps E u l k ω ∩ H := by
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  -- GW1's walk statements (as in `Lk.sb2LowerChainStatement_of_thm12_thm13`)
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀) (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  have hS := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  have hC := GW1WalkFinish.walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 h13₀) hD4
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hEu := hE _ hsu
  have hRu := hER _ hsu
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hwbc
  have hregw := hreg' w
  have hRw : StagedPiecesRegular κ b jumps P w Ew := stagedPiecesRegular_of_regular h13 hκ hb hEw hregw
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨A₁, g₁, β₁, Y₁, hA₁m, hA₁c, hA₁eq, hg₁, hW₁, hm₁⟩ :=
    exists_scheduleRetainedMean_reg h12p h13 hκ hκ4 hb hh hEu hRu hu₀ k
  have hcap : ∀ᵐ ω ∂P, ∀ (j : ℕ) (q : ℚ), j < w.2.2.length →
      w.2.2[j]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      ∃ (A₂ : Set ℂ) (g₂ : DistOn upperHalfPlaneOpens) (β₂ : BoundaryWord),
      A₂ ⊆ H ∧ IsOpen (H \ A₂) ∧
      A₂ = WalkLaw.stageSet κ b jumps (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) Ew (j + 1) ω ∧
      IsHarmonicDistOn g₂ (H \ A₂) ∧
      ((ExplState.run κ b jumps (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) (fun i => Ew i ω) (j + 1)).2.2.2.1
          j ≠ none →
        min (instrTime (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) j) (Ew j ω).2 ≠ ⊤ →
        β₂.IsSorted ∧ HasInteriorStageSides κ b jumps (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal)
          (fun i => Ew i ω) (j + 1) β₂ ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ → g₂ φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ * (ExplState.run κ b jumps
              (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) (fun i => Ew i ω) (j + 1)).2.2.2.2.1.2.2 z)
            (fun z => β₂.mean ((ExplState.run κ b jumps
              (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) (fun i => Ew i ω) (j + 1)).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps
              (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) (fun i => Ew i ω) (j + 1)).2.2.2.2.1.dom) ∧
      ∀ vA vB : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vA (H \ A₁ ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, vA z * φ z) →
        InnerProductSpace.HarmonicOnNhd vB (H \ A₂) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ → g₂ φ = ∫ z, vB z * φ z) →
        ∀ p : ℂ, p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} → p ∈ A₂ ∪ {z : ℂ | z.im = 0} →
        ∀ rA > 0, ∀ rB > 0,
          MarkedUnionMeans (A₁ ω) A₂ (FinRel.freeNear A₂ (A₁ ω) p rA ∩ FinRel.freeNear (A₁ ω) A₂ p rB) p vA vB := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun q => ?_
    by_cases hj : j < w.2.2.length ∧ w.2.2[j]? = some (Sum.inl (-(Real.pi / 2), ⊤))
    · filter_upwards [ae_capStageFacts h12p h13 hκ hκ4 hb hh hEu hRu hu₀ hA₁m hA₁eq hg₁ hEw hRw hregw hj.1 hj.2
        (q : ℝ).toNNReal] with ω hω _ _
      exact hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hj
  have hWC := Lk.ae_walkChainFacts_of_reg hS h13 hT hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    (StagedReg.regFam E) hE' hreg'
  have hTip := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg' true
  have hComp := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    (StagedReg.regFam E) hE' hreg' true
  have hInj := ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hEw hregw hRw j
  filter_upwards [hW₁.sorted, hW₁.sides, hm₁, hg₁.2.1, hcap, hWC, hTip, hComp, hInj,
    GW1W.regLaunches_of_stagedPiecesRegular hRw, hrun w hwbc, hRu, Lk.ae_injLaunches h13 hκ hκ4 hb hEu hRu,
    Lu.ae_isRightEntryValue_upperEntry hRu k, hleft, hA₁eq] with ω hβ₁s hside₁ hm₁ω hharm₁ hcapω hWCω htipω
    hcompω hinjω hRLω hrunω hRuω hinjuω hentω hleftω hA₁ω
  intro hF β₀ hβ hβ0 hβr tR htR s₁ s₂ htRs hs harc
  set Du : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => E (Lu.upperSpec u l) j ω with hDu
  set Dw : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => Ew j ω with hDw
  -- the walk at `ω`
  have htip' : GW1WalkChain.WalkTipCoordinates κ b jumps w Dw := htipω
  have hdN : stStatus (ExplState.run κ b jumps w Dw w.2.2.length) = GW1Conn.stDone := hcompω
  have hβr' : range β₀ = statePhysicalSet 0 (ExplState.run κ b jumps w Dw w.2.2.length) := by
    rw [hβr, hDw, hrunω w.2.2.length]
    rfl
  -- the old side
  obtain ⟨⟨c₀, θ₀⟩, hl₀⟩ := Option.ne_none_iff_exists'.1 hF
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (Lf.sspec u l) Du (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (Du j).1 (min (instrTime (Lf.sspec u l) j) (Du j).2) :=
    fun j c' θ' hl' => hRuω j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ := Lf.exists_path_upperPrefix hu l Du hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω := hpA
  have hent := hentω hF
  rw [Lu.upperLaunchChart_eq hl₀] at hent
  have hc₀s : c₀ = stChart (ExplState.run κ b jumps (Lf.sspec u l) Du k) := (eq_launch_of_launches _ _ hl₀).2.2
  rw [hc₀s, ← hpA'] at hent
  obtain ⟨v₁, hv₁, hrep₁⟩ := hharm₁
  obtain ⟨c, g, e₁, word, hc, hgc, hgi, hgf, hgb, hmo₁, hws, hmean₁, hlabel⟩ :=
    old_sample_facts_right hu l Du hreg₀ hinjuω hl₀ hp hpA hent hβ₁s (hm₁ω v₁ hv₁ hrep₁) hside₁
  -- S1: the upper prefix is on the closed left of the walk
  have hav := hleftω hF
  have hav' : prefixPhysSet κ b jumps (Lu.upperSpec u l) Du k ∩ rightSideOf (range β₀) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω ⊆ closedLeftSide β₀ := Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  rw [← hpA'] at hAL harc htR
  -- the cut on a launched piece
  have harcH : β₀ '' Ioo s₁ s₂ ⊆ H := fun z hz => (harc hz).2
  obtain ⟨j, c', θ', q, s₁', Cg, gc, τ, hl, hq0, hqζ, hαq, hτ, hτe, hD, hPc, hPh, hmo, hgc', hgi', hC', hgf',
    h0P, hα, hinjα, hPc', hsplit⟩ := exists_walk_cut hWCω hRLω hinjω htip' hdN hβ hβr' hs harcH
  obtain ⟨hi, -, -⟩ := eq_launch_of_launches w Dw hl
  have hjl : j < w.2.2.length := by
    by_contra hc'
    rw [List.getElem?_eq_none (not_lt.1 hc')] at hi
    cases hi
  have hθ' : θ' = -(Real.pi / 2) := angle_eq_of_mem_boundaryWalkSpec (List.mem_of_getElem? hi)
  have htop : instrTime w j = ⊤ := Lx.instrTime_boundaryWalk_of_launch hl
  have hwj : w.2.2[j]? = some (Sum.inl (-(Real.pi / 2), ⊤)) := by rw [hi, hθ', htop]
  obtain ⟨A₂, g₂, β₂, -, hA₂o, hA₂eq, hharm₂, hm₂, hU⟩ := hcapω j q hjl hwj
  have hlc : (ExplState.run κ b jumps (capSpec w j (-(Real.pi / 2)) (q : ℝ).toNNReal) Dw (j + 1)).2.2.2.1 j ≠
      none := by
    rw [launches_run_capSpec_succ hjl.le hwj, hl]; exact Option.some_ne_none _
  have hfinc : min (instrTime (capSpec w j (-(Real.pi / 2)) ((q : ℝ).toNNReal : ℝ≥0∞)) j) (Dw j).2 ≠ ⊤ := by
    rw [instrTime_capSpec hjl.le]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  obtain ⟨hβ₂s, hside₂, hmean₂⟩ := hm₂ hlc hfinc
  obtain ⟨v₂, hv₂, hrep₂⟩ := hharm₂
  obtain ⟨hpre₂, f, Φ, e₂, hch, hfd, hfin, hDo, hmo₂, hmean₂', hlab₂⟩ :=
    second_sample_facts_walk hRLω hl hD hPc hPh hmo hgc' hgi' hC' hgf' h0P hα hinjα hqζ hq0 hαq hPc' hβ hβ0
      hsplit hτe (hmean₂ v₂ hv₂ hrep₂) hside₂
  -- the compared arc
  obtain ⟨σ₁, hσ₁a, hσ₁b⟩ := exists_between hτ.1
  have hsub : Icc σ₁ τ ⊆ Ioo s₁ s₂ := fun t ht => ⟨lt_of_lt_of_le hσ₁a ht.1, lt_of_le_of_lt ht.2 hτ.2⟩
  have harc' : β₀ '' Icc σ₁ τ ⊆ pA '' Icc 0 1 ∩ H := (image_mono hsub).trans harc
  -- the explored sets
  have hA'f : A₁ ω ⊆ fillH (pA '' Icc 0 1) := by
    intro z hz
    rw [hA₁ω] at hz
    have hzA : z ∈ pA '' Icc 0 1 := by rw [hpA]; exact Or.inl (Or.inl (Or.inr hz.1))
    exact ⟨hz.2, Or.inl (subset_closure hzA)⟩
  have hA'a : pA '' Icc 0 1 ∩ H ⊆ A₁ ω := by
    rintro z ⟨hzA, hzH⟩
    rw [hA₁ω]
    rw [hpA] at hzA
    rcases hzA with hzP | ⟨y, -, rfl⟩
    · exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet _ (E (Lu.upperSpec u l)) k ω hzP hzH
    · exact absurd hzH (WalkPiece.ofReal_notMem_H y)
  have hB'f : A₂ ⊆ fillH (β₀ '' Icc 0 τ) := by
    intro z hz
    rw [hA₂eq] at hz
    have hzP : z ∈ β₀ '' Icc 0 τ := by rw [hpre₂]; exact Or.inl (Or.inr hz.1)
    exact ⟨hz.2, Or.inl (subset_closure hzP)⟩
  have hB'a : β₀ '' Icc 0 τ ∩ H ⊆ A₂ := by
    rintro z ⟨hzP, hzH⟩
    rw [hA₂eq]
    rw [hpre₂] at hzP
    exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet _ Ew (j + 1) ω hzP hzH
  -- the protected comparison and its contradiction
  obtain ⟨val, d, hlab, hval⟩ := exists_protectedWordComparison_lower hp hp0 hpH hβ hβ0 hAL hc hgc hgi hgf hgb
    hmo₁ hws hmean₁ hlabel (η := β₀) (q₁ := σ₁) (q₂ := τ) (fun s _ => rfl) hch hfd hfin hDo hmo₂ hβ₂s hmean₂'
    (Jx := ∅) (fun y _ hy _ hyH => hlab₂ y hy hyH) (hA₁c ω).2 hA₂o hA'f hB'f hA'a hB'a
    (fun x₀ h1 h2 rA hrA rB hrB => hU v₁ v₂ hv₁ hrep₁ hv₂ hrep₂ x₀ h1 h2 rA hrA rB hrB) htR
    (htRs.trans hσ₁a.le) hσ₁b harc'
  exact ProtectedWordComparison.false_two_old hκ hκ4 hlθ d hlab hval

end InteractingSLE.Theorem14.SB.S3.Asm

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw Restart
open Supp9B (IsProperCurve)

/-- **Lemma S3's tail form for SB2(2)'s lower walk, in `ℍ`** (in the kernel form of `Lf.SB2LowerSetting`): almost
surely at an upper launch `k`, under the retained upper kernel, for every proper parametrization `β₀` of the lower walk
and its visit `t_R` to `R = max (A ∩ ℝ)`, no open time interval after `t_R` maps into `A ∩ ℍ` — no lower piece runs
along the upper history (ruling R120, decision D6 addendum). -/
def SB2LowerWalkTailNoCommonArcHStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ tR : ℝ≥0, β₀ tR = (realMax (upperPrefix κ b jumps E u l k ω₀) : ℂ) →
        ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ upperPrefix κ b jumps E u l k ω₀ ∩ H

/-- **`SB2LowerWalkTailNoCommonArcHStatement` from Theorems 1.2–1.3** (R48): the P-level form
`ae_lowerTail_noArc_H` transferred to the retained kernels (`KernelTower.ae_ae_condExpKernel_of_ae`; the upper run
before `k` is kernel-a.s. that of `ω₀`, `Retain.ae_ae_run_eq`). -/
theorem sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) :
    SB2LowerWalkTailNoCommonArcHStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hPQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (ae_lowerTail_noArc_H h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft)
  have hrunQ := Retain.ae_ae_run_eq (Lu.upperSpec u l) hRu hm𝒢 le_rfl
  filter_upwards [hPQ, hrunQ] with ω₀ hP₀ hrun₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hP₀, hrun₀] with ω hω hrω
  intro β₀ hβ hβ0 hβr tR htR s₁ s₂ h1 h2
  have hlaunchω : ω ∈ Lu.upperLaunchSet κ b jumps E u l k := by
    show (ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [launches_run_succ_of_run_eq (Lu.upperSpec u l) hrω, hlaunch]
    exact Option.some_ne_none _
  have hAω : upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ := by
    show prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) k ∪
        ((↑) : ℝ → ℂ) '' Icc u 0 =
      prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω₀) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0
    unfold prefixPhysSet; rw [hrω]
  rw [← hAω] at htR ⊢
  exact hω hlaunchω β₀ hβ hβ0 hβr tR htR s₁ s₂ h1 h2

end InteractingSLE.Theorem14.SB.S3.Asm
