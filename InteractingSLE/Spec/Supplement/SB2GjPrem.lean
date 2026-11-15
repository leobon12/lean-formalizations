/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GjLoc
import InteractingSLE.Spec.Supplement.SB2GjStmt
import InteractingSLE.Spec.Supplement.SB2FqHgt
import InteractingSLE.Spec.Supplement.SB2FpRoot

/-!
# NOJUMP's 9F premises for a word with `BaseLawForX`

Packet PROVE-GW2-GEOM2, round 17 (decision D79). NOJUMP's `Nf.SB2LowerRootVersionStatement9F` takes, for the word
`β₁` at B's stage `ℓ` and the line family's retained set `A₁ 0`:

* **F3's mean identity on the base region** `stageEvent ℓ ∩ {ℓ ≤ relOff}`: from the retained law of `BaseLawForX`
  (whose event covers that region) by F3LAW's `Fq.hmean_of_law`, the retained set being history-avoidance local for
  the law's marks (`Gj.hloc_rootLine`) — **`hmean9F_of_baseLawForX`**;
* **D34's heights clause on the root event**: F3LAW's `Fp.ae_heightClause_root` reads the mean identity only on the
  root event, which lies in the base region; its proof with the mean premise on the base region and the root facts of
  `BaseLawForX` — **`ae_heightClause_rootB`**, **`hheight9F_of_baseLawForX`**.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Gj

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Ms Fm Fp

/-- **D34's clause on the root event from the mean identity on the base region** (F3LAW's `Fp.ae_heightClause_root`
with its mean premise read only where `ℓ ≤ relOff`). -/
theorem ae_heightClause_rootB {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} (k ℓ : ℕ)
    {A₁ : Ω → Set ℂ} {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hAm : Measurable[mΩ, hittingSigma] A₁) (hloc : IsLocalSet A₁ (WholeField.centredField h u₀) P)
    {β₁ : Ω → BoundaryWord} (hβs : ∀ ω, (β₁ ω).IsSorted)
    (hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens,
      LocalSets.IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
          ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) -
                QuantumZipper.chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z) (H \ A₁ ω))
    {G : Set Ω}
    (hroot : ∀ᵐ ω ∂P, ω ∈ G → IsHPHull (A₁ ω) ∧ FreeRight (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β₁ ω) (entry (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω))))
    (hcov : ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G) :
    ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      Nb.HeightClause κ b jumps (A₁ ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  filter_upwards [Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hAm hloc hg₁, hmean g₁ hg₁, hg₁.2.1, hroot, hcov]
    with ω hw hid hharm hrω hcovω hωr
  obtain ⟨hev, hoff, -, -⟩ := hωr
  obtain ⟨hHP, hfree, hL⟩ := hrω (hcovω hev hoff.ge)
  obtain ⟨v, hv, hrep⟩ := hharm
  exact heightClause_of_meanIdentity hκ hHP hfree (hβs ω) hu₀ (hid hev hoff.ge v hv hrep) (hw v hv hrep) hL

/-- **NOJUMP's two 9F premises for a word with `BaseLawForX`**, on the root's line family (CONDFIN's
`Cx.RootSetsAt`), together with the retained law they come from. -/
theorem premises9F_of_baseLawForX (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {𝓖 : Filtration ℝ≥0 mΩ}
    {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t))
    {β₁ : Ω → BoundaryWord} (hX : BaseLawForX (κ := κ) b jumps P h E u l k ℓ β₁) :
    ∃ (K' : Ω → Set ℂ) (G' : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
      Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) K' G' Y β₁ M ∧
      (∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G') ∧
      (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
          ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
              (H \ A₁ 0 ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
        Nb.HeightClause κ b jumps (A₁ 0 ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω)) := by
  obtain ⟨hAm, -, -, hAl, -, -, -, -, hAc, -, -⟩ := hfam 0
  have hA₁f : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
      ω := fun t => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, -⟩ := hfam t
    exact h10.mono fun ω h => h.1
  obtain ⟨K', G', Y, M, hmv, hcov, hroot⟩ := hX.2.2 𝓖 A₁ h𝓖 hA₁f
  have hloc := hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ h𝓖 hfam
  have hmeanS := Fq.hmean_of_law hh hu₀ ((lineFiltC P 𝓖).le 0) hAm hAc hloc hmv
    (S := {ω | ω ∈ Ms.stageEvent κ b jumps E u l k ℓ ∧
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)})
    (hcov.mono fun ω h hω => h hω.1 hω.2)
  have hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
            (H \ A₁ 0 ω) := fun g₁ hg₁ =>
    (hmeanS g₁ hg₁).mono fun ω h hst hoff => h ⟨hst, hoff⟩
  exact ⟨K', G', Y, M, hmv, hcov, hmean,
    ae_heightClause_rootB hκ hh k ℓ hu₀ hAm hAl hmv.2.2.2.2.2.2.2.2.1 hmean hroot hcov⟩

end InteractingSLE.Theorem14.SB.Gj
