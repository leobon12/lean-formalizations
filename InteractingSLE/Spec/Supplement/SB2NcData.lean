/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcPcDet
import InteractingSLE.Spec.Supplement.SB2NvAS

/-!
# F2b′'s stage objects and their good event

Packet PROVE-AUX61-NOJUMP (round 21, D34, components A–B). **`StageObj`**: the objects of F2b′ at a flow stage `ℓ`
of B with the facts they satisfy on a good event `Eg` of the completed line σ-algebra at time `0` (`lineC0`):

* the retained hull `K` (`exists_retHull`), the chart offset `x₀` (the entry read of `K` at B's point,
  `measurable_entryRead`), the live event `F` (`exists_liveEvent`), a regular version `Ê` of B's family
  (`Nv.exists_regular_version`);
* on `Eg ⊆ F`, containing almost every point of `F` (**`StageGoodAt`**): the walk facts, the tail launch, the
  retained union's geometry, `fill K = fill X`, the runs of the regularized families, the agreement with `Ê`,
  `x₀ = entryRead (fill K) (B's point)`, and the relative stage curve is driven with `x₀` the right entry value.

**`exists_stageObj`**: such objects exist (Theorems 1.2–1.3).
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

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide LocalSets Sec7.PocketTraversal Lk LuM

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

variable (P) in
/-- The completed line σ-algebra at time `0` (`lineFiltC P 𝓖 0` for F2b′'s line family). -/
abbrev lineC0 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : MeasurableSpace Ω :=
  mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P

/-- **F2b′'s good facts at a sample.** -/
structure StageGoodAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    Prop where
  walk : WalkGood κ b jumps E u l k ω
  stage : ω ∈ stageEvent κ b jumps E u l k ℓ
  off : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ
  pos : bLife b jumps E ℓ ω ≠ 0
  fill : fillH (K ω) = fillH (retX κ b jumps E u l k ℓ ω)
  retc : IsCompact (retX κ b jumps E u l k ℓ ω)
  retH : ∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im
  hull : IsHPHull (fillH (retX κ b jumps E u l k ℓ ω))
  stfill : stageFill κ b jumps E u l k ℓ ω = fillH (retX κ b jumps E u l k ℓ ω)
  runw : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
    ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n
  runu : ∀ n, ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) n =
    ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) n
  agree : Nv.AgreeAt κ (-(Real.pi / 2)) b jumps (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
    fun j => Ê j ω
  x0 : x₀ ω = entryRead (fillH (K ω))
    (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))
  driven : IsDrivenCurve (bRel κ b jumps E ℓ K x₀ ω)
  entry : IsRightEntryChart (retX κ b jumps E u l k ℓ ω) (realMax (retX κ b jumps E u l k ℓ ω))
    ((Mo.hullChart (fillH (retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω))

variable (P) in
/-- **F2b′'s stage objects** and their good event. -/
structure StageObj (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) where
  K : Ω → Set ℂ
  x₀ : Ω → ℝ
  F : Set Ω
  Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞
  Eg : Set Ω
  hK : @Restart.IsDyadicHitMeasurable Ω (lineC0 P κ b jumps E u l k ℓ) K
  hKc : ∀ ω, IsCompact (K ω)
  hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)
  hx₀ : Measurable[lineC0 P κ b jumps E u l k ℓ] x₀
  hF : MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] F
  hFae : ∀ᵐ ω ∂P, (ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
    relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
    0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
  hÊm : ∀ j, Measurable (Ê j)
  hÊreg : ∀ j ω, IsRegularDriver (Ê j ω)
  hÊP : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) fun j => Ê j ω
  hEg : MeasurableSet[lineC0 P κ b jumps E u l k ℓ] Eg
  hEgF : Eg ⊆ F
  hEgae : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Eg
  good : ∀ ω ∈ Eg, StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω

/-- **F2b′'s stage objects exist** (Theorems 1.2–1.3). -/
theorem exists_stageObj (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    Nonempty (StageObj P κ b jumps E u l k ℓ) := by
  classical
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  set θ : ℝ := -(Real.pi / 2) with hθ
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps θ true with hwdef
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  set Ew := StagedReg.regFam E w with hEwdef
  have hEwm : ∀ j, Measurable (Ew j) := (hE' w hw).1
  -- the σ-algebras
  have hcap := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps) Ew hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at hcap
  have h𝒢 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
    sup_le ((hE' su hsu).2.1 k) (hcap.trans ((hE' w hw).2.1 (ℓ + 1)))
  have h𝒢C : lineSigma0 κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ := le_inf h𝒢 (le_aeSigma _ P)
  have hwℓ𝒢 : pastSigma κ b jumps w Ew ℓ ≤ lineSigma0 κ b jumps E u l k ℓ := by
    refine le_trans ?_ le_sup_right
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := θ) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le Ew le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ ℓ)
  -- the components
  obtain ⟨K, G₁, hKm, hKc, hKp, -, hG₁ae, hG₁⟩ := exists_retHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ
    k ℓ hℓ hwℓ hu₀
  have hgood := ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  obtain ⟨F, hFm, hFae⟩ := exists_liveEvent hb hE hER hu hlθ k ℓ hℓ hwℓ hgood
  obtain ⟨Ê, GÊ, hÊm, hÊreg, hÊP, -, hGÊn, hGÊ⟩ := Nv.exists_regular_version (κ := κ) (θ := θ)
    (hE w hw).1 (hER w hw)
  have hGÊae : ∀ᵐ ω ∂P, ω ∈ GÊ := by rw [ae_iff]; exact hGÊn
  -- the offset
  set x₀ : Ω → ℝ := fun ω => entryRead (fillH (K ω)) (stPt (ExplState.run κ b jumps w (fun j => Ew j ω) ℓ))
    with hx₀def
  have hR : Measurable[lineC0 P κ b jumps E u l k ℓ]
      fun ω => stPt (ExplState.run κ b jumps w (fun j => Ew j ω) ℓ) :=
    (measurable_stPt_past (κ := κ) hb w hEwm (hreg' w) ℓ).mono (hwℓ𝒢.trans h𝒢C) le_rfl
  have hx₀m : Measurable[lineC0 P κ b jumps E u l k ℓ] x₀ := measurable_entryRead hKm hKc hKp hR
  -- the good event
  have hall : ∀ᵐ ω ∂P, (ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) < ℓ ∧
      0 < (E w ℓ ω).2)) ∧
      (ω ∈ Lu.upperLaunchSet κ b jumps E u l k → WalkGood κ b jumps E u l k ω) ∧
      ((ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G₁) ∧
      (∀ n, ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => E w j ω) n) ∧
      (∀ n, ExplState.run κ b jumps su (fun j => StagedReg.regFam E su j ω) n =
        ExplState.run κ b jumps su (fun j => E su j ω) n) ∧ ω ∈ GÊ := by
    filter_upwards [hFae, hgood, hG₁ae, hrun' w hw, hrun' su hsu, hGÊae] with ω h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨G, hGae, hGm, hGsub⟩ := hall.exists_measurable_mem
  have hG0 : MeasurableSet[lineC0 P κ b jumps E u l k ℓ] G :=
    ⟨hGm, ⟨univ, @MeasurableSet.univ Ω (lineSigma0 κ b jumps E u l k ℓ), ae_eq_univ.2 (mem_ae_iff.1 hGae)⟩⟩
  refine ⟨⟨K, x₀, F, Ê, F ∩ G, hKm, hKc, hKp, hx₀m, hFm, hFae, hÊm, hÊreg, hÊP, (h𝒢C _ hFm).inter hG0,
    inter_subset_left, ?_, ?_⟩⟩
  · filter_upwards [hGae] with ω hω hF
    exact ⟨hF, hω⟩
  · rintro ω ⟨hωF, hωG⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hGsub ω hωG
    obtain ⟨hst, hoff, hpos⟩ := h1.1 hωF
    have hg := h2 hst.1
    obtain ⟨hl, hc, hH, hhull, hfill, hsf⟩ := hG₁ ω (h3 hst.2)
    have hx0 : x₀ ω = entryRead (fillH (K ω)) (stPt (ExplState.run κ b jumps w (fun j => E w j ω) ℓ)) := by
      simp only [hx₀def, h4 ℓ]
    have hpos' : bLife b jumps E ℓ ω ≠ 0 := (pos_iff_ne_zero.1 hpos)
    obtain ⟨hdr, hent⟩ := bRel_driven hg hl hpos' hoff hfill hx0
    exact ⟨hg, hst, hoff, hpos', hfill, hc, hH, hhull, hsf, h4, h5, hGÊ ω h6, hx0, hdr, hent⟩

end

end InteractingSLE.Theorem14.SB.Nc
