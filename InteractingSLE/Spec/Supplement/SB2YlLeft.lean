/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YlBase
import InteractingSLE.Spec.Supplement.SB2FqHgt
import InteractingSLE.Spec.Supplement.SB2FoAsm
import InteractingSLE.Spec.Supplement.SB2FoInp

/-!
# The left heights two stages after a zero root

Packet PROVE-T14-SB2LIFT (round 36, decision D80: the zero-root step of F3LAW's (P1)). At a zero root, B's stage
`ℓ = relOff + 2` carries the base law (`Sz.sb2LowerBaseWordStatementZ_of_thms`). The induction also carries D34's left
heights `hL` at the seed `stPt (run ℓ)` (the input of `Fo.tail_step` at `ℓ` and of `Fq.hheight_of_law`).

* **`ae_zeroRoot_facts`**: almost surely, at an upper launch with a zero root, `Sx.zeroRoot_facts` for the actual lower
  walk with `A` the upper prefix.
* **`ae_leftAdm_zeroRoot`**: for any retained law `Fl.MvLaw … A₁ K G Y β M` of a locally measurable set `A₁` carrying
  the base's root facts on `G` (`A₁` a hull, free right of `R`, `LeftAdm β (entry A₁ R)`), almost surely on
  `G ∩ stageEvent ℓ ∩ {relOff + 2 = ℓ} ∩ {zero root}` we have `LeftAdm β (entry A₁ (stPt (run ℓ)))`. The seed moves
  from `R` to the first restart mark `m = stPt (run ℓ)` over a low connector, and the word reads the original heights
  right of `R` (F3's mean identity, `Fo.ae_read_of_meanIdentity` with `Fq.hmean_of_law`). This is F3LAW's
  `Fo.leftAdm_entry_mono`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sx

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P Lk Ms
  WalkSide LocalSets WholeField Fm

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}

/-- **The walk at a zero root, almost surely** (`zeroRoot_facts` with `A` the upper prefix). -/
theorem ae_zeroRoot_facts (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2)) ∩ H ⊆
        fillH (upperPrefix κ b jumps E u l k ω) ∧
      ((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 3)).2.2.2.1
          (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2) ≠ none →
        realMax (upperPrefix κ b jumps E u l k ω) < stPt (ExplState.run κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2)) ∧
        ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω) < x →
          x < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
            (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2)) →
          x ∉ jumps → b x + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hSD := GW1WalkExit.walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hCo := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _
    hE' hreg' true
  filter_upwards [Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft, hSD, hCo,
    hrun _ hwbc] with ω hg hSω hdω hrw hup hZ
  have hgω := hg hup
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  have hr' : ∀ n, ExplState.run κ b jumps w D n =
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n := fun n => (hrw n).symm
  have hX : RunExitData κ b jumps θ D := runExitData_of_run_eq hr' (runExitData_of_stageData hSω)
  have hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps w D n) := fun n hn => by
    rw [hr' n]
    exact (allowedSt_run hSω n).1 hn
  have hdone : stStatus (ExplState.run κ b jumps w D w.2.2.length) = GW1Conn.stDone := by
    rw [hr']
    exact hdω
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hgω.upath
  obtain ⟨β₀, hβ, hβ0, hβr, hS1, -⟩ := hgω.proper
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β₀ := by rw [hpA]; exact hS1
  have hK : ∀ tL : ℝ≥0, β₀ tL = realMax (upperPrefix κ b jumps E u l k ω) →
      β₀ '' Icc 0 tL ⊆ hullK (upperPrefix κ b jumps E u l k ω) := by
    intro tL hβL
    obtain ⟨-, tR, htR, -, hKR, -⟩ := s2HullRight hpc hp0 hpH hβ hβ0 hS1'
    have e : tR = tL := hβ.2.1 (htR.trans (by rw [hβL, hpA]))
    subst e
    rw [← hpA]
    exact hKR
  exact zeroRoot_facts hb hX hgω.reg hgω.chain hgω.noLeftMove hgω.noLeftHit hallow hdone hβ hβ0 hβr hK hZ

/-- **D34's left heights two stages after a zero root**, almost surely. See the module docstring. -/
theorem ae_leftAdm_zeroRoot (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (h𝓗 : 𝓗 ≤ mΩ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A₁ : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A₁) (hAc : ∀ ω, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hloc : IsHistoryAvoidanceLocal 𝓗 A₁ (centredField h u₀) P)
    {K : Ω → Set ℂ} {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → Restart.BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ 𝓗 P h A₁ K G Y β M)
    (hroot : ∀ᵐ ω ∂P, ω ∈ G → IsHPHull (A₁ ω) ∧ FreeRight (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β ω) (entry (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)))) :
    ∀ᵐ ω ∂P, ω ∈ G → ω ∈ stageEvent κ b jumps E u l k ℓ →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2 = ℓ →
      ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      LeftAdm κ (β ω) (entry (A₁ ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ))) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : IsLocalSet A₁ (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hloc.isAvoidanceLocal
  have hread0 := Fo.ae_read_of_meanIdentity hh hu₀ hAm hl hlaw.2.2.2.2.2.2.2.2.1
    (Fq.hmean_of_law hh hu₀ h𝓗 hAm hAc hloc hlaw (S := G) (Eventually.of_forall fun _ h => h))
  filter_upwards [hread0, hroot, ae_zeroRoot_facts h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft]
    with ω hrd hrt hzf hωG hst hrel hZ
  obtain ⟨hHP, hfree, hLR⟩ := hrt hωG
  obtain ⟨-, hzf2⟩ := hzf hst.1 hZ
  subst hrel
  obtain ⟨hRm, hlow⟩ := hzf2 hst.2
  refine Fo.leftAdm_entry_mono (b := b) (jumps := jumps) hHP hfree hRm.le hLR (fun x hx hxJ hyJ => ?_)
    (fun x hx hxm hxJ => ?_)
  · obtain ⟨r, hr, hd⟩ := hfree x hx
    exact hrd hωG hHP x r hr hd hxJ hyJ
  · have h1 := hlow x hx hxm hxJ
    have h2 := Sec4.sleLambda_pos hκ
    linarith

end InteractingSLE.Theorem14.SB.Sx
