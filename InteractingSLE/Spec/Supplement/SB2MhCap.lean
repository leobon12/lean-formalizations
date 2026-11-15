/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MhPast
import InteractingSLE.Spec.Supplement.WalkSideAssembly
import InteractingSLE.Spec.Supplement.WalkInfChart
import InteractingSLE.Spec.Supplement.WalkSideDom
import InteractingSLE.Spec.Supplement.SB2LcdKer
import InteractingSLE.Spec.Supplement.SB2LcdStageLoc
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# The explored prefix's own mean after a capped piece (SB2(2)'s explored mean, per test)

Packet PROVE-SB2-LCMEAN, round 5 (the `hind₂` input of `Ln.ae_eqOn_unionMean_of_stagePullback`). For a boundary walk
run with the regularized family `StagedReg.regFam E` (SB2(2)'s lower walk: `θ = −π/2`, `right = true`), the walk prefix
through instruction `ℓ`, the piece `ℓ` stopped at own time `τ`, has a measurable, relatively closed local version `A₂`,
and on the capped launch event `capEvent` (`ℓ` launched, `τ` before the piece's lifetime) every local-set mean of `A₂`
is, for tests supported in the domain of the chart `c'` of the capped run, the chart mean of the stop word read through
`c'`:

* **`exists_capMean`**: from the landed stage law after a capped piece (`WalkSide.ae_capMean`), the chart version
  (`WalkInf.prefixChartVersionStatement_of_mem`), the domain fact (`WalkSide.prefixChartDomStatement`), the capped
  marked locality (`Lcd.stageSet_markedLocal_of_thm12_thm13`) and piece regularity of the regularized family
  (`Exist.StagedLaw.stagedPiecesRegular_of_regular`).

The chart of the capped run after `ℓ + 1` instructions is `c.loewner Wr T` with `c` the run chart before `ℓ`
(`ExplState.launch`), so this is the explored-chain formula `GE ∘ fwdMap Wr T ∘ c.1 − χ (Im logDerivFwd … + c.2.2)` with
`GE = stopWord.mean`, on the chart domain.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mh

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The explored prefix's own mean after a capped piece**, for a boundary walk run with the regularized family. -/
theorem exists_capMean (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (A₂ : Ω → Set ℂ) (c' : Ω → Chart),
      Measurable[mΩ, hittingSigma] A₂ ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, A₂ ω = WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω) ∧
      IsLocalSet A₂ (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) A₂ (centredField h u₀) P ∧
      (∀ ω, (c' ω).IsConformal) ∧ (∀ ω, InnerProductSpace.HarmonicOnNhd (c' ω).2.2 (c' ω).dom) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        c' ω = (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        ((c' ω).dom : Set ℂ) ⊆ H \ A₂ ω ∧ IsOpen ((H \ A₂ ω) \ (c' ω).dom)) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
          tsupport φ ⊆ (c' ω).dom →
          g ω φ = (∫ z, ((stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))).mean ((c' ω).1 z) -
              chiC κ * (c' ω).2.2 z) * φ z) - ∫ z, u₀ z * φ z := by
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  set E' := StagedReg.regFam E w with hE'def
  have hEw : IsStagedHistory κ b jumps P h w E' := hE' w hw
  set w' := capSpec w ℓ θ (τ : ℝ≥0∞) with hw'
  have hS' : IsStagedHistory κ b jumps P h w' E' := isStagedHistory_capSpec hb hEw (hreg' w) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hav, ho, hloc⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hS' (hreg' w) hu₀
    (ℓ + 1)
  obtain ⟨B, hBm, hBc, hBae, hBloc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hS'.2.1 (ℓ + 1)⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho hav hloc
  have hBm' : Measurable[mΩ, hittingSigma] B := hBm.mono (hS'.2.1 (ℓ + 1)) le_rfl
  have hBl : IsLocalSet B (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hBm' (Eventually.of_forall hBc)).out 4 1).2 hBloc.isAvoidanceLocal
  obtain ⟨c', hc'c, hc'l, hc'h, hdom, hfwd, hCm, hliftm, hc'eq⟩ :=
    WalkInf.prefixChartVersionStatement_of_mem hθ right κ hκ hκ4 b jumps hb P h hh (fun spec => StagedReg.regFam E spec)
      hE' hR' hreg' ℓ τ
  have hPR := (hR' w hw).ae_pieceRegular
  have hAD : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E' ℓ τ →
      ((c' ω).dom : Set ℂ) ⊆ H \ B ω ∧ IsOpen ((H \ B ω) \ (c' ω).dom) := by
    filter_upwards [hc'eq, hBae, hPR, ho] with ω hcω hBω hPRω hBoω hω
    have hreg'' := pieceRegular_capSpec (fun j => E' j ω) hℓ.le hwℓ hPRω (τ : ℝ≥0)
    have hcc := (GW1RestartFinal.chart_boundaryRange_run w' (fun j => E' j ω) hreg'' (ℓ + 1)).1
    have hdis := prefixChartDomStatement κ b jumps w (fun j => E' j ω) ℓ θ τ hℓ hwℓ hω.1 hω.2 hPRω
    rw [hcω hω, hBω]
    refine ⟨fun z hz => ⟨hcc.dom_subset hz, fun hzB => Set.disjoint_left.1 hdis hz hzB.1⟩, ?_⟩
    refine isOpen_diff_dom hBoω fun z hzH hzcl hzD => ?_
    exact WalkLeaf.mem_stageSet_of_frontier w' E' ω hreg'' (ℓ + 1) z hzH hzcl hzD
  refine ⟨B, c', hBm', hBc, hBae, hBl, hBloc, hc'c, hc'h, hc'eq, hAD, fun g hg => ?_⟩
  obtain ⟨β, -, hmean⟩ := ae_capMean hκ hb hh hEw (hreg' w) hℓ hwℓ τ hu₀ hBm' hBl hBloc hc'c hc'l hdom hfwd hCm
    hliftm hc'eq hAD hg
  exact ⟨β, hmean⟩

/-- **The explored prefix's own mean after a capped piece, pointwise on the chart domain**: `exists_capMean` with the
per-test identities upgraded (rational bumps, harmonicity of the chart mean) to every harmonic representative. -/
theorem exists_capMean_pointwise (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (A₂ : Ω → Set ℂ) (c' : Ω → Chart),
      Measurable[mΩ, hittingSigma] A₂ ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, A₂ ω = WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω) ∧
      IsLocalSet A₂ (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) A₂ (centredField h u₀) P ∧
      (∀ ω, (c' ω).IsConformal) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        c' ω = (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        ((c' ω).dom : Set ℂ) ⊆ H \ A₂ ω ∧ IsOpen ((H \ A₂ ω) \ (c' ω).dom)) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
          ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g ω φ = ∫ z, v z * φ z) →
            EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
              (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))).mean ((c' ω).1 z) -
                chiC κ * (c' ω).2.2 z) (c' ω).dom := by
  obtain ⟨A₂, c', hAm, hAc, hAae, hAl, hAmark, hc'c, hc'h, hc'eq, hAD, hmean⟩ :=
    exists_capMean h12p h13 hθ right hκ hκ4 hb hh hE hER ℓ hℓ hwℓ τ hu₀
  refine ⟨A₂, c', hAm, hAc, hAae, hAl, hAmark, hc'c, hc'eq, hAD, fun g hg => ?_⟩
  obtain ⟨β, hφ⟩ := hmean g hg
  refine ⟨β, ?_⟩
  have hbumps := ae_all_iff.2 fun i : ℚ × ℚ × ℚ => hφ (ratBump i)
  filter_upwards [hbumps, hAD] with ω hbω hADω hω v hv hvg
  obtain ⟨hdomB, -⟩ := hADω hω
  have hβs := isSorted_stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
    (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))
  set β' := stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
    (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω)) with hβ'
  have hcm := harmonicOnNhd_chartMean (hc'c ω) (hc'h ω) hβs hu₀.1 (chiC κ)
  have hdH : ((c' ω).dom : Set ℂ) ⊆ H := (hc'c ω).dom_subset
  have hu₀c : ContinuousOn u₀ (c' ω).dom := fun z hz => (hu₀.1 z (hdH hz)).1.continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z) (c' ω).dom := by
    have h1 : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom :=
      fun z hz => (hcm z hz).1.continuousAt.continuousWithinAt
    refine (h1.add hu₀c).congr fun z _ => ?_
    simp only [Pi.add_apply]
    ring
  have heq : EqOn v (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom := by
    refine eqOn_of_ratBump (c' ω).dom.isOpen hdH (hv.mono hdomB) hcm fun i hi => ?_
    have hiB : tsupport (ratBump i) ⊆ H \ A₂ ω := hi.trans hdomB
    rw [← hvg _ hiB, hbω i hω hi, ← integral_sub (WholeField.integrable_mul_testOn hfc _ hi)
      (WholeField.integrable_mul_testOn hu₀c _ hi)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  intro z hz
  have e := heq hz
  simp only at e ⊢
  rw [e]
  ring

end InteractingSLE.Theorem14.SB.Mh
