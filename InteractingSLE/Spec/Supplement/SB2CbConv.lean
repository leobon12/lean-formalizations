/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbLaw

/-!
# (P1)'s per-stage clauses from the induction's stage data (D80 item 2)

Packet PROVE-SB2-CANON, round 8. **`stageLawClauses_of_exact`**: the clauses `Cz.StageLawClauses` of a flow stage `ℓ`
for every line family `(𝓖, A₁)` with `A₁ 0` measurable (relatively closed complement) and a.s. the filled retained
set, from the induction's stage data for one exact version `Â` of `A₁ 0` (measurable, history-avoidance local for
`lineFiltC P 𝓖 0`) — the content of F3LAW's `Fs.StageLawOn` on the launch event, unpacked: the retained law on `Â`
covering B's launches, the word measurable for the completed retained past, countably many word profiles containing the
word's on the launches, and the left heights on the tail live event — the law's cover and the profiles at the launches
at an upper launch (D82 item 3). The types are the angle types of the profiles
(`Lv.angleWordType_shift_mem`), the law moves to `A₁ 0` (`mvLaw_congr_set`), F3's mean identity is `Fq.hmean_of_law`
read through the a.s. equality of the two local-set means (`GW4Fix.ae_localSetMean_eq_of_ae_set_eq`), and the heights
clause is `Fq.hheight_of_law`.

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

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Lv Lk Mf Ms

/-- **(P1)'s clauses at a stage from the induction's stage data for an exact version of the retained set.** -/
theorem stageLawClauses_of_exact (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    -- the target line family
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ}
    (hA0 : ∀ᵐ ω ∂P, A₁ 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (hA₁m : Measurable[mΩ, hittingSigma] (A₁ 0)) (hA₁c : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    -- an exact version of the retained set
    {Â : Ω → Set ℂ} (hÂm : Measurable[mΩ, hittingSigma] Â) (hÂc : ∀ ω, Â ω ⊆ H ∧ IsOpen (H \ Â ω))
    (hÂloc : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) Â (centredField h u₀) P)
    (hÂe : ∀ᵐ ω ∂P, Â ω = A₁ 0 ω)
    -- the induction's stage data on the launch event
    {K : Ω → Set ℂ} {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    {S : Set Lv.WordProfile} (hlaw : Fl.MvLaw κ (lineFiltC P 𝓖 0) P h Â K G Y β M)
    (hcov : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G)
    (hβ : Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β) (hS : S.Countable)
    (hprof : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lv.wordProfile (β ω) ∈ S)
    (hL : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Fm.LeftAdm κ (β ω) (Fm.entry (Â ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))) :
    StageLawClauses κ b jumps P h E u l k ℓ 𝓖 A₁ := by
  have hSG : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ G := by
    filter_upwards [hcov] with ω h1 hω using h1 hω.1 hω.2
  have h𝓗 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  refine ⟨K, G, Y, β, M, angleType κ (-(Real.pi / 2)) '' profileTypes κ S, mvLaw_congr_set hlaw hÂe, hβ, hcov,
    (countable_profileTypes κ hS).image _, ?_, fun u₀ hu₀ g₁ hg₁ => ?_, ?_⟩
  · filter_upwards [hprof] with ω hω hU hl x using angleWordType_shift_mem κ _ x (hω hU hl)
  · -- F3's mean identity, through the exact version
    have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
    have hÂl : IsLocalSet Â (centredField h u₀) P :=
      ((isLocalSet_tfae hh0 hÂm (Eventually.of_forall hÂc)).out 4 1).2 (hÂloc u₀ hu₀).isAvoidanceLocal
    obtain ⟨ĝ, hĝ⟩ := IsLocalSet.exists_isLocalSetMean hh0 hÂm hÂl
    have hgg := GW4Fix.ae_localSetMean_eq_of_ae_set_eq hh0 hÂm hA₁m (Eventually.of_forall fun ω => (hÂc ω).2)
      (Eventually.of_forall fun ω => (hA₁c ω).2) hÂe hĝ hg₁
    have hm := Fq.hmean_of_law hh hu₀ h𝓗 hÂm hÂc (hÂloc u₀ hu₀) hlaw hSG ĝ hĝ
    filter_upwards [hm, hgg, hÂe] with ω h1 h2 h3 hω w₁ hw₁ hrep
    rw [← h3] at hw₁ hrep ⊢
    exact h1 hω w₁ hw₁ fun φ hφ => by rw [h2]; exact hrep φ hφ
  · -- the heights clause
    obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    have hÂA : ∀ᵐ ω ∂P, Â ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω := by
      filter_upwards [hÂe, hA0] with ω h1 h2 using h1.trans h2
    have hH := Fq.hheight_of_law h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hÂA hu₀ h𝓗 hÂm hÂc
      (hÂloc u₀ hu₀) hlaw hSG hL
    filter_upwards [hH, hÂe] with ω h1 h2 hω hoff hpos
    rw [← h2]
    exact h1 hω hoff hpos

end InteractingSLE.Theorem14.SB.Cz
