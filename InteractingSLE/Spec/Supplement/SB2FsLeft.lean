/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoThr
import InteractingSLE.Spec.Supplement.SB2FoTail
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Exist.StagedLaw3Path
import InteractingSLE.Spec.Supplement.SB2FmSeed
import InteractingSLE.Spec.Supplement.SB2FoAsm

/-!
# The left heights' step at every next launch (zero next lifetimes included)

Worker PROVE-SB2-F3LAW (round 6, D80). `Fo.ae_leftAdm_succ_succ` and `Fm.ae_seed_freeRight` conclude only for a
positive next lifetime (the latter also identifies B's seed `bSeed`, which needs it). The induction's invariant `hL`
must hold at every tail launch, since a following zero-lifetime stage reads it (`Fo.ae_leftAdm_zero`). The free ray
at the seed needs no lifetime: same proofs without that premise.

* `Fs.ae_seed_freeRight'`, **`Fs.ae_leftAdm_succ_succ'`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fs

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide Fm Fo Qw Fl

/-- **The free ray right of B's point at a tail launch** (any lifetime). -/
theorem ae_seed_freeRight' (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁ : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω) :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      FreeRight (A₁ ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) := by
  by_cases hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length
  swap
  · refine Eventually.of_forall fun ω hω => absurd (Nc.flow_of_launch hω.2).1 hℓ
  filter_upwards [Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft,
    Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ, hA] with ω hg hgeo hAω hev hoff
  have hgω := hg hev.1
  obtain ⟨hXc, -, -, -, hfill⟩ := hgeo hev.2
  have hA' : A₁ ω = fillH (Nc.retX κ b jumps E u l k ℓ ω) := hAω.trans hfill
  have heven := Nc.even_of_launch hev.2
  have hmax := Nc.realMax_retX_eq hgω hev.2 hoff heven
  rw [hA', ← hmax]
  exact freeRight_fillH_realMax hXc

/-- **The left heights' step `ℓ → ℓ + 2`** at every launch at `ℓ + 2` (as `Fo.ae_leftAdm_succ_succ`). -/
theorem ae_leftAdm_succ_succ' (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    -- stage `ℓ`
    (h𝓜 : 𝓜 ≤ mΩ) {K : Ω → Set ℂ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {F : Set Ω}
    (hc : Measurable[𝓜] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
    (hZ : Measurable fun ω => Fl.canonField κ h x₀ hKc hKp ω) (hF : MeasurableSet[𝓜] F)
    (hlawx : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) (Fl.canonField κ h x₀ hKc hKp)
      (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps)
    (hFev : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Ms.stageEvent κ b jumps E u l k ℓ) {p : Ω → ℝ}
    (hp : ∀ᵐ ω ∂P, ω ∈ F → FreeRight (fillH (K ω)) (p ω) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) ≤ p ω)
    (hx₀le : ∀ᵐ ω ∂P, ω ∈ F → x₀ ω ≤ entry (fillH (K ω)) (p ω))
    (hL : ∀ᵐ ω ∂P, ω ∈ F → LeftAdm κ (β₁ ω) (entry (fillH (K ω)) (p ω)))
    (hread : ∀ᵐ ω ∂P, ω ∈ F → ∀ x, p ω < x → x ∉ jumps → bdryVal (fillH (K ω)) x ∉ (β₁ ω).jumps →
      (β₁ ω).fn (bdryVal (fillH (K ω)) x) = b x)
    (hseedF : ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0
        (-(Real.pi / 2)))
      (flowLineRhoR κ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0
        (-(Real.pi / 2))) 0
      (flowLineXL (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0)
      (flowLineXR (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0))
    -- the step's outputs at `ℓ + 2`
    {A₁' : Ω → Set ℂ} (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    {K₂ : Ω → Set ℂ} {G₂ : Set Ω} (hG₂F : G₂ ⊆ F)
    (hζ₂ : ∀ ω ∈ G₂, (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)).2 ≠ ⊤)
    (hhull₂ : ∀ᵐ ω ∂P, ω ∈ G₂ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)))) →
      fillH (K₂ ω) = stepHull (fillH (K ω)) (x₀ ω) (Qw.recDrv (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)))
        ((driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)).2.toNNReal : ℝ))
    (hK₂A : ∀ᵐ ω ∂P, ω ∈ G₂ → fillH (K₂ ω) = A₁' ω) :
    ∀ᵐ ω ∂P, ω ∈ G₂ → ω ∈ Ms.stageEvent κ b jumps E u l k (ℓ + 2) →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ + 2 →
      LeftAdm κ (stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
        (Fl.maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) ω)
        (entry (A₁' ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)))) := by
  have hE2 := ae_markPos_zero_driverOf h12p h13 hκ (-(Real.pi / 2)) h𝓜 hc hZ hF hlawx
  filter_upwards [hFev, hp, hx₀le, hL, hread, hseedF, hE2, hhull₂, hK₂A,
    Fs.ae_seed_freeRight' h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hleft hA',
    ae_free_between_seeds h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA']
    with ω hFevω hpω hx₀ω hLω hreadω hseedω hE2ω hhullω hK₂ω hseed2 hfree2 hωG hev2 hoff2
  have hωF : ω ∈ F := hG₂F hωG
  obtain ⟨hpfree, hpst⟩ := hpω hωF
  set D := driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)
    with hDdef
  have hfin : D.2 ≠ ⊤ := hζ₂ ω hωG
  have hLc : ∀ y, y < 0 → y ∉ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps →
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    have h1 : LeftAdm κ (β₁ ω) (x₀ ω) := fun y hy hyJ => hLω hωF y (lt_of_lt_of_le hy (hx₀ω hωF)) hyJ
    have h2 := leftAdm_shiftW h1 (x₀ ω)
    rw [sub_self] at h2
    exact h2
  obtain ⟨hgood, h0⟩ := hE2ω hωF (hseedω hωF) hLc hfin
  have hA'ω : stepHull (fillH (K ω)) (x₀ ω) (Qw.recDrv D) (D.2.toNNReal : ℝ) = A₁' ω :=
    (hhullω hωG hgood).symm.trans (hK₂ω hωG)
  have hfreeR := hseed2 hev2 hoff2
  have hlow : ∀ x, p ω < x → x < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)) →
      (∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (stepHull (fillH (K ω)) (x₀ ω) (Qw.recDrv D) (D.2.toNNReal : ℝ))) →
      x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ := fun x hpx hxp' hfr hxJ =>
    hfree2 (hFevω hωF) hev2.2 x (lt_of_le_of_lt hpst hpx) hxp' (by rwa [← hA'ω]) hxJ
  have hstep := Fo.leftAdm_stepWord_entry (e := fun ω => driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) (ω := ω) hκ
    (Mo.isHPHull_fillH hKc hKp ω) hpfree (hx₀ω hωF) (hLω hωF) (hreadω hωF) (Mz.isRegularDriver_driverOf h12p hκ _ _)
    hgood hfin h0 (by rw [hA'ω]; exact hfreeR) hlow
  rw [hA'ω] at hstep
  have hw : stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
      (Fl.maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) ω =
      stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
        (fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Fl.canonField κ h x₀ hKc hKp ω)) ω := by
    unfold stepWord
    rw [Fl.maskDrv_of_mem hωF]
  rw [hw]
  exact hstep

end InteractingSLE.Theorem14.SB.Fs
