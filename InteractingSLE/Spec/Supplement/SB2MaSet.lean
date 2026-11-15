/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MaRun
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.WalkMarkSeedLaw
import InteractingSLE.Spec.Supplement.SB4RLift
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# The lower walk's GW1-type inputs in SB2(2)'s setting

Packet PROVE-T14-SB2LIFT (round 15; items 1–2 of handoff §R14.2). SB2(2)'s setting (`Lf.SB2LowerSetting`) has staged
histories whose launched pieces are regular almost surely (`StagedPiecesRegular`, ruling R51), not regular at every
sample as GW1's stage data asks. This file transfers the walk inputs from the regularized family
(`StagedReg.regFam_spec`) to the original one:

* `stopDrv_canonDrv`, `stopTime_canonDrv`, **`lHit_canonDrv`**: a launch's hit predicate only sees the retained datum
  of its driver;
* **`noLeftMove_of_run_eq`**, **`noLeftHit_of_run_eq`**: `NoLeftMove` and `NoLeftHit` pass to a driver family with the
  same runs and, at launches, the same retained data;
* `fin_of_not_done`, `fin_before_first_done`, `exists_first_done`: before the first done stage every launched
  lifetime is finite (`RunInputs.fin₁` with `N + o` the first done stage);
* **`ae_walkInputs_of_theorem13`**: almost surely the lower walk `boundaryWalkSpec b jumps (−π/2) true` of the original
  family has, at every step, no left move, no left hit (the strong form), and no zero lifetime at a later launch
  (`WalkMarkSeed.ae_noZeroLaterLaunchData`), with Theorem 1.3 at universe `0`;
* **`sb2LowerWalkInputs`**: the inputs of `ae_walkInputs_of_theorem13`, almost surely under the retained kernel of
  every retained launch, in the form of `Lf.SB2LowerSetting` (the quantifiers of PROVE-SB2-LIFTSET's `RelDriverAt`:
  the fields `lm₁`, `lh₁` of `RunInputs` and the zero-lifetime input of the actual walk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem stopDrv_canonDrv (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    stopDrv t (canonDrv t D) = stopDrv t D := by
  funext x
  show (canonDrv t D).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t (canonDrv t D).2)).toNNReal =
    D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t D.2)).toNNReal
  rw [min_canonDrv]
  exact stopped_canonDrv t D _

theorem stopTime_canonDrv (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    stopTime t (canonDrv t D) = stopTime t D := by
  unfold stopTime
  rw [min_canonDrv]

/-- **A launch's hit predicate only sees the retained datum of its driver.** -/
theorem lHit_canonDrv (c : Chart) (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (z : ℂ) :
    lHit c t (canonDrv t D) z ↔ lHit c t D z := by
  unfold lHit lAlive
  rw [stopDrv_canonDrv, stopTime_canonDrv]

/-- **`NoLeftMove` passes to a driver family with the same runs.** -/
theorem noLeftMove_of_run_eq {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hrun : ∀ k, ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' k =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) {n : ℕ}
    (h : NoLeftMove κ b jumps θ D' n) : NoLeftMove κ b jumps θ D n := by
  intro w m
  simpa only [hrun] using h w m

/-- **`NoLeftHit` passes to a driver family with the same runs and, at launches, the same retained data.** -/
theorem noLeftHit_of_run_eq {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hrun : ∀ k, ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' k =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) {n : ℕ}
    (hc : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none →
      canonDrv ⊤ (D' n) = canonDrv ⊤ (D n))
    (h : NoLeftHit κ b jumps θ D' n) : NoLeftHit κ b jumps θ D n := by
  rintro hl ⟨x, hx, hhit⟩
  have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' (n + 1)).2.2.2.1 n ≠ none := by
    rw [hrun]; exact hl
  refine h hl' ⟨x, by rw [hrun]; exact hx, ?_⟩
  rw [hrun, ← lHit_canonDrv, hc hl, lHit_canonDrv]
  exact hhit

/-- **A launch with an infinite lifetime finishes the walk**: a launch followed by a status other than done has a finite
lifetime. -/
theorem fin_of_not_done {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {j : ℕ}
    (hnd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)) ≠ stDone)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none) :
    (D j).2 ≠ ⊤ := by
  intro htop
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl'
  rw [Lx.instrTime_boundaryWalk_of_launch hl'] at he
  have e := launch_eq_of_top (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D j) j (D j) θ' ⊤
    (by rw [htop, min_self])
  exact hnd (by rw [he]; exact e.2.2.2.2.1)

/-- **Finite launched lifetimes before the first done stage** (the form of `RunInputs.fin₁` with `M = N + o`). -/
theorem fin_before_first_done {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {M : ℕ}
    (hM : ∀ i, i < M → stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D i) ≠ stDone) :
    ∀ j, j + 1 < M → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ :=
  fun j hj hl => fin_of_not_done (hM (j + 1) hj) hl

/-- **The first done stage** of a walk that is done at some stage. -/
theorem exists_first_done {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h : ∃ M, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D M) = stDone) :
    ∃ M, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D M) = stDone ∧
      ∀ i, i < M → stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D i) ≠ stDone := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun i hi => Nat.find_min h hi⟩

/-- **The lower walk's GW1-type inputs, almost surely, for the original staged family** (pieces regular almost surely,
`StagedPiecesRegular`): no left move, no left hit and no zero lifetime at a later launch, at every step (Theorem 1.3
at universe `0`). -/
theorem ae_walkInputs_of_theorem13 (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, ∀ n,
      NoLeftMove κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
      NoLeftHit κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
      (0 < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (n + 1)).2.2.2.1 n ≠ none →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ 0) := by
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  filter_upwards [ae_noLeftMove_noLeftThr_of_theorem13 h13₀ hκ hκ4 hb hh hcf hζ' hE' hreg',
    ae_noLeftHit_of_theorem13 h13₀ hκ hκ4 hb hh hcf hζ' hE' hreg',
    WalkMarkSeed.ae_noZeroLaterLaunchData hκ hb hh (hE' _ hlwp) (hreg' _),
    hrun _ hlwp, hER _ hlwp] with ω hlm hlh hnz hr hpr n
  refine ⟨noLeftMove_of_run_eq hr (hlm n).1, noLeftHit_of_run_eq hr (fun hl => ?_) (hlh n), fun hn hl => ?_⟩
  · obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
    have hspec := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ _ hl').1
    obtain ⟨h0, hcont, -⟩ := hpr n θ' _ c hspec hl'
    have ht := Lx.instrTime_boundaryWalk_of_launch hl'
    change canonDrv ⊤ (StagedReg.regularize (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω)) = _
    rw [ht] at hcont ⊢
    exact StagedReg.canonDrv_regularize h0 hcont
  · have hl' := hl
    rw [← hr] at hl'
    have := hnz n hn hl'
    rwa [StagedReg.regFam, StagedReg.regHist_snd] at this

/-- **The lower walk's GW1-type inputs under the retained kernel** in SB2(2)'s setting (`Lf.SB2LowerSetting`, the
quantifiers of PROVE-SB2-LIFTSET's `RelDriverAt`): almost surely under the retained kernel of every retained launch, the
actual lower walk has no left move, no left hit and no zero lifetime at a later launch, at every step. -/
theorem sb2LowerWalkInputs (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀), ∀ n,
        NoLeftMove κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
        NoLeftHit κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
        (0 < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (n + 1)).2.2.2.1 n ≠ none →
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ 0) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (ae_walkInputs_of_theorem13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER)] with ω₀ hω₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact hω₀

end InteractingSLE.Theorem14.SB.Lk
