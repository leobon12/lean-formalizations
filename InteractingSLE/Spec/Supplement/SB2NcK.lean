/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcGeo

/-!
# F2b′'s retained hull `K`

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). **`exists_retHull`**: a random compact set `K`, dyadic-hit
measurable for the completed line σ-algebra at time `0`, with `K ∪ {im ≤ 0}` preconnected at every sample, and a good
event `G₁` of the same σ-algebra containing almost every launch of B's stage `ℓ`, on which B launches, the retained
union `X = A ∪ B_{<ℓ}` is compact with a hull for its fill, `fill K = fill X`, and the filled version of the two stage
sets is `fill X`. As in REVIEW-FABLE-T14's `Qt.exists_hullLaw`: `K = Mo.retHull K₀ G₁` for the version `K₀` of
`exists_retVersion`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide LocalSets

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The filled version of the two stage sets at the start of B's stage `ℓ` (F2b′'s `A₁ 0`). -/
abbrev stageFill (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : Ω → Set ℂ :=
  fillVer (fun ω =>
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
    WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
      (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
      ℓ ω)

/-- **F2b′'s retained hull and its good event.** -/
theorem exists_retHull (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (K : Ω → Set ℂ) (G₁ : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P) K ∧
      (∀ ω, IsCompact (K ω)) ∧ (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧
      MeasurableSet[mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P] G₁ ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G₁) ∧
      ∀ ω ∈ G₁, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        IsCompact (retX κ b jumps E u l k ℓ ω) ∧ (∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im) ∧
        IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) ∧
        fillH (K ω) = fillH (retX κ b jumps E u l k ℓ ω) ∧
        stageFill κ b jumps E u l k ℓ ω = fillH (retX κ b jumps E u l k ℓ ω) := by
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  set Ew := StagedReg.regFam E w with hEwdef
  have hcap := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps) Ew hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at hcap
  have h𝓜le : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
    sup_le ((hE' _ (Lu.isBoundaryContinuedProgram_upperSpec hlθ)).2.1 k) (hcap.trans ((hE' w hw).2.1 (ℓ + 1)))
  have h𝓜C : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P :=
    le_inf h𝓜le fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
  obtain ⟨Bu, Bl, -, -, -, -, -, -, hK₀m, hK₀c, hK₀ae⟩ :=
    exists_retVersion h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hu₀
  set K₀ : Ω → Set ℂ := fillVer fun ω => Bu ω ∪ Bl ω with hK₀def
  have hgeo := ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  -- the launch event of B's stage `ℓ` (regularized family): an event of the line σ-algebra
  set L₀ : Set Ω := {ω | (ExplState.run κ b jumps w (fun j => Ew j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hL₀def
  have hL₀ : MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] L₀ := by
    have h1 := Lv.measurableSet_launch_pastSigma (κ := κ) (spec := w) hb (hE' w hw).1 (hreg' w) ℓ
    have hle : pastSigma κ b jumps w Ew ℓ ≤ lineSigma0 κ b jumps E u l k ℓ := by
      refine le_trans ?_ le_sup_right
      rw [← WalkSide.pastSigma_capSpec_of_le (θ := -(Real.pi / 2)) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le Ew le_rfl]
      exact pastSigma_mono _ _ (Nat.le_succ ℓ)
    exact hle _ h1
  -- the good samples
  set Gd : Ω → Prop := fun ω =>
    (∀ n, ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => E w j ω) n) ∧
    K₀ ω = stageFill κ b jumps E u l k ℓ ω ∧
    ((ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      IsCompact (retX κ b jumps E u l k ℓ ω) ∧ (∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im) ∧
      IsPreconnected (retX κ b jumps E u l k ℓ ω ∪ Restart.lowerHalf) ∧
      IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) ∧
      stageFill κ b jumps E u l k ℓ ω = fillH (retX κ b jumps E u l k ℓ ω)) with hGddef
  have hGd : ∀ᵐ ω ∂P, Gd ω := by
    filter_upwards [hrun w hw, hK₀ae, hgeo] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  set N : Set Ω := toMeasurable P {ω | ¬ Gd ω} with hNdef
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hGd
  set G₁ : Set Ω := L₀ \ N with hG₁def
  have hG₁good : ∀ ω ∈ G₁, Gd ω := fun ω hω => by
    by_contra hn
    exact hω.2 (subset_toMeasurable P _ hn)
  have hG₁C : MeasurableSet[mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P] G₁ := by
    rw [MeasurableSpace.measurableSet_inf]
    refine ⟨(h𝓜le _ hL₀).diff (measurableSet_toMeasurable P _), L₀, hL₀, ?_⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    exact propext ⟨fun h' => h'.1, fun h' => ⟨h', hω⟩⟩
  -- the facts on the good event
  have hfacts : ∀ ω ∈ G₁, (ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
      K₀ ω = fillH (retX κ b jumps E u l k ℓ ω) ∧ IsCompact (retX κ b jumps E u l k ℓ ω) ∧
      (∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im) ∧ IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) ∧
      stageFill κ b jumps E u l k ℓ ω = fillH (retX κ b jumps E u l k ℓ ω) := by
    intro ω hω
    obtain ⟨hr, hK, hg⟩ := hG₁good ω hω
    have hl : (ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [← hr (ℓ + 1)]; exact hω.1
    obtain ⟨hc, hH, -, hhull, hfill⟩ := hg hl
    exact ⟨hl, hK.trans hfill, hc, hH, hhull, hfill⟩
  have hHP : ∀ ω ∈ G₁, IsHPHull (K₀ ω) := fun ω hω => by
    rw [(hfacts ω hω).2.1]; exact (hfacts ω hω).2.2.2.2.1
  -- the retained hull
  set K : Ω → Set ℂ := Mo.retHull K₀ G₁ with hKdef
  have hKm : @IsDyadicHitMeasurable Ω (mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P) K :=
    @Mo.isDyadicHitMeasurable_retHull Ω K₀ G₁ (mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P)
      (hK₀m.mono h𝓜C le_rfl) (fun ω => (hK₀c ω).1) hG₁C
  have hKc : ∀ ω, IsCompact (K ω) := Mo.isCompact_retHull fun ω hω => (hHP ω hω).2.1
  have hXc : ∀ ω ∈ G₁, K₀ ω = closure (K₀ ω) ∩ H ∧ IsClosed (closure (K₀ ω)) ∧
      (∀ z ∈ closure (K₀ ω), 0 ≤ z.im) ∧ IsPreconnected (closure (K₀ ω) ∪ Restart.lowerHalf) := by
    intro ω hω
    refine ⟨(Sec7.SideHeight.closure_inter_H_eq (hK₀c ω).1 (hK₀c ω).2).symm, isClosed_closure, ?_,
      Sec5.Aux61Restart.isPreconnected_closure_union_lowerHalf (hHP ω hω)⟩
    have hcl : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    intro z hz
    exact (hcl.closure_subset_iff.2 fun v hv => show 0 ≤ v.im from le_of_lt ((hK₀c ω).1 hv)) hz
  have hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf) := Mo.isPreconnected_retHull_union hXc
  have hfK : ∀ ω ∈ G₁, fillH (K ω) = K₀ ω := fun ω hω => by
    rw [hKdef, Mo.fillH_retHull_of_mem (X := fun ω => closure (K₀ ω)) hω (hXc ω hω).1]
    exact Sec5.Aux61Restart.fillH_closure_of_isHPHull (hHP ω hω)
  refine ⟨K, G₁, hKm, hKc, hKp, hG₁C, ?_, fun ω hω => ?_⟩
  · filter_upwards [hGd, measure_eq_zero_iff_ae_notMem.1 hN0] with ω hg hN hl
    refine ⟨?_, hN⟩
    show (ExplState.run κ b jumps w (fun j => Ew j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
    rw [hg.1 (ℓ + 1)]; exact hl
  · obtain ⟨hl, hK, hc, hH, hhull, hfill⟩ := hfacts ω hω
    exact ⟨hl, hc, hH, hhull, (hfK ω hω).trans hK, hfill⟩

end

end InteractingSLE.Theorem14.SB.Nc
