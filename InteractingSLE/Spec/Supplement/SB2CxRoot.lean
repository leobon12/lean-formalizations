/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CxPost
import InteractingSLE.Spec.Supplement.SB2CxFam
import InteractingSLE.Spec.Supplement.SB2CsJm

/-!
# The root's line mean (D66: (M) and the root line-mean assembly)

Packet PROVE-SB2-CONDFIN, round 12. **`hmean_root`**: the `hmean` input of K2 at the root (`Cr.ae_k2_root`) — the
line mean of the JOINT union `A₁ t ∪ A₂J t` at every version, word type, B-time and test function, at positive
relative clock before the stop — for the root's line family (`Cx.exists_rootLineFamily`) and a root version over it
(NOJUMP's `Ne.SB2LowerRootVersionStatement8`), from:

* SB2LIFT's S2 clause in the post-head chart (`Sx.ae_isStageS2_root`'s conclusion, `hS2`);
* the post-head stage pull-back (`hpb`, D66/D67's (P), PROVE-GW2-NOTHR's; the exact Prop is
  `PostHeadPullbackStatement` below);
* F3's mean identity for `A₁` and the hull (`hF3`, `hfill`), as for the tails (`Ci.hmean_of_stageS2`);
* the entrance time `τE` before `t` on the cells at positive clock (`hC`).

Proof: B's own union mean by the engine `Cx.ae_lineMean_pos_rootG` in the post-head chart, its explored mean read
through the head (`Cx.postHead_explored`, from LCMEAN's stage-chart mean in `RootSetsAt`), the record of B's piece
(`isDrvGood_recOf_of_lt`, `recDrv_eq_stopDrv`) and the a.s. conformality of B's stage charts; then the transfer to the
joint union (`Cs.hmean_joint_of_hmeanB`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cx

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Mk Cr Om Lv Ms
open Supp8.Q3Stop Sec7.PocketTraversal Restart.DomainMarkov
open Supp8.Q3Chain (flowedData flowedJumps)

section Defs

variable (κ : ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (b : ℝ → ℝ) (jumps : Finset ℝ) (ℓ : ℕ)
  (τE : Ω → ℝ≥0)

/-- **The post-head chart** (SB2LIFT's, D51 item 3): B's stage chart at `ℓ` followed by the Loewner map of the head,
the piece stopped at the entrance `τE`. -/
def phChart (ω : Ω) : Chart :=
  (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
    (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)
    (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω)

/-- The post-head driver at the B-time `t`: B's stopped driver shifted at the entrance. -/
def phDrv (t : ℝ≥0) (ω : Ω) : ℝ → ℝ := shiftDrive (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω) (τE ω : ℝ)

/-- The post-head time at the B-time `t`. -/
def phTime (t : ℝ≥0) (ω : Ω) : ℝ := Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω - (τE ω : ℝ)

end Defs

section Stop

variable {e : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The stopped piece before its lifetime** (deterministic): the stopped drivers at `τ ≤ t < ζ` are continuous,
start at `0`, agree on `[0, τ]`, stop at `τ` and `t`, and the record at `t` reads the stopped driver. -/
theorem stop_facts (he : IsRegularDriver e) {τ t : ℝ≥0} (hτt : τ ≤ t) (ht : (t : ℝ≥0∞) < e.2) :
    Continuous (stopDrv (t : ℝ≥0∞) e) ∧ stopDrv (t : ℝ≥0∞) e 0 = 0 ∧ Continuous (stopDrv (τ : ℝ≥0∞) e) ∧
      (∀ r ∈ Icc (0 : ℝ) τ, stopDrv (τ : ℝ≥0∞) e r = stopDrv (t : ℝ≥0∞) e r) ∧
      stopTime (τ : ℝ≥0∞) e = τ ∧ stopTime (t : ℝ≥0∞) e = t ∧
      rdrv (recOf (t : ℝ≥0∞) e) = stopDrv (t : ℝ≥0∞) e ∧ rtime (recOf (t : ℝ≥0∞) e) = stopTime (t : ℝ≥0∞) e := by
  have hτ' : (τ : ℝ≥0∞) < e.2 := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτt) ht
  refine ⟨(continuous_retOf he (isDrvGood_recOf_of_lt he ht)).comp continuous_real_toNNReal, stopDrv_zero he _,
    (continuous_retOf he (isDrvGood_recOf_of_lt he hτ')).comp continuous_real_toNNReal, fun r hr => ?_, ?_, ?_,
    recDrv_eq_stopDrv he (isDrvGood_recOf_of_lt he ht), rfl⟩
  · have h1 : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ τ := ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)
    have h2 : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ t := h1.trans (ENNReal.coe_le_coe.2 hτt)
    change e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) e.2)).toNNReal =
      e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) e.2)).toNNReal
    rw [min_eq_left hτ'.le, min_eq_left ht.le, min_eq_left h1, min_eq_left h2]
  · change (((min (τ : ℝ≥0∞) e.2).toNNReal : ℝ≥0) : ℝ) = τ
    rw [min_eq_left hτ'.le, ENNReal.toNNReal_coe]
  · change (((min (t : ℝ≥0∞) e.2).toNNReal : ℝ≥0) : ℝ) = t
    rw [min_eq_left ht.le, ENNReal.toNNReal_coe]

end Stop

/-- **Named statement (for PROVE-GW2-NOTHR, D66/D67 item (P)): the post-head stage pull-back.** In SB2(2)'s setting,
for the root's line family (`Cx.exists_rootLineFamily`, any family with its facts), at every B-stage `ℓ` and B-time
`t`, almost surely on B's capped launch at `t` with the entrance `Na.rootEntry` at or before `t` and `ℓ` the relative
root's stage (`Cf.RootEv`), the post-head chart pulls back B's own set: `Ln.IsStagePullback` with the shifted driver
and time. -/
def PostHeadPullbackStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ (ℓ : ℕ) (u₀ : ℂ → ℝ) (A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ),
        (∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) →
        ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
          Cf.RootEv κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (Mz.lowerD b jumps E ω) ℓ →
          Na.rootEntry κ b jumps E u l k ℓ ω ≤ t →
          ∃ gb : ℂ → ℂ, Ln.IsStagePullback (phChart κ E b jumps ℓ (Na.rootEntry κ b jumps E u l k ℓ) ω) gb
            (A₁ t ω) (A₂ t ω) {z | (phChart κ E b jumps ℓ (Na.rootEntry κ b jumps E u l k ℓ) ω).2.1 z ∈ A₁ t ω}
            (fwdHull (phDrv E b jumps ℓ (Na.rootEntry κ b jumps E u l k ℓ) t ω)
              (phTime E b jumps ℓ (Na.rootEntry κ b jumps E u l k ℓ) t ω))

section Root

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The root's line mean** (K2's `hmean` at the root, for the JOINT union of NOJUMP's version): from the root's line
family, SB2LIFT's post-head S2 clause, the post-head pull-back, F3's mean identity and the entrance before `t`. -/
theorem hmean_root (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t))
    {Fr : Set Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
    {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL
      L relLife)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hfill : ∀ t, ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ t ω)
    (hF3 : ∀ t, ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ t) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Fr → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ t ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z) (fun z => (β₁ ω).mean ((Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z) -
          chiC κ * (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) (H \ A₁ t ω))
    (τE : Ω → ℝ≥0)
    (hC : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
      ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ∧ τE ω ≤ t)
    (hpb : ∀ t, ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t → τE ω ≤ t →
      ∃ gb : ℂ → ℂ, Ln.IsStagePullback (phChart κ E b jumps ℓ τE ω) gb (A₁ t ω) (A₂ t ω)
        {z | (phChart κ E b jumps ℓ τE ω).2.1 z ∈ A₁ t ω}
        (fwdHull (phDrv E b jumps ℓ τE t ω) (phTime E b jumps ℓ τE t ω)))
    (hS2 : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
      IsStageS2 (phChart κ E b jumps ℓ τE ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (phDrv E b jumps ℓ τE t ω)
        (phTime E b jumps ℓ τE t ω) (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) :
    ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂J t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
        ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w → 0 < (S.ver m).a t ω → (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w))
              (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  intro g hg m w hw t φ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the stage charts of B's regularized walk are a.s. conformal
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw' := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hw') (hreg' _)
  have hconf : ∀ᵐ ω ∂P, (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).IsConformal := by
    filter_upwards [GW1W.regLaunches_of_stagedPiecesRegular hRw] with ω hω
    exact SB.LuM.isConformal_runChart_of_reg _ hω ℓ
  -- the explored mean of B's own set, read in the post-head chart
  have hind₂ : ∀ t', ∀ g₂ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (A₂ t') (WholeField.centredField h u₀) P g₂ →
      ∃ GE : Ω → ℂ → ℝ, ∀ᵐ ω ∂P, ω ∈ {ω | ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t' ∧ τE ω ≤ t'} →
        (∃ (nL' nR' : ℕ) (ρL' : Fin nL' → ℝ) (ρR' : Fin nR' → ℝ) (xL' : Fin nL' → ℝ) (xR' : Fin nR' → ℝ),
          (∀ i, xL' i ≤ 0) ∧ (∀ j, 0 ≤ xR' j) ∧
          ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension
              (flowedData κ ρL' ρR' xL' xR' (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω))
              (flowedJumps xL' xR' (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω)) G →
            EqOn G (fun z => GE ω z + -(Real.pi / 2) * chiC κ) H) ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ t' ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t' ω → g₂ ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z) (fun z => GE ω (fwdMap (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω)
              ((phChart κ E b jumps ℓ τE ω).1 z)) -
            chiC κ * ((logDerivFwd (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω)
              ((phChart κ E b jumps ℓ τE ω).1 z)).im + (phChart κ E b jumps ℓ τE ω).2.2 z)) (H \ A₂ t' ω) := by
    intro t' g₂ hg₂
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcl, -, hmean₂, -⟩ := hfam t'
    obtain ⟨β, hβ⟩ := hmean₂ g₂ hg₂
    refine ⟨fun ω => (stopWord κ (β ω, -(Real.pi / 2), recOf (t' : ℝ≥0∞)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))).mean, ?_⟩
    filter_upwards [hβ, hcl, hconf] with ω hβω hclω hcω hCω
    obtain ⟨hcap, hτt⟩ := hCω
    obtain ⟨hWc, hW0, hVc, hVW, hτtime, htime, hrw, hrt⟩ :=
      stop_facts (StagedReg.isRegularDriver_regHist ℓ ω) hτt hcap.2
    obtain ⟨-, hcorr, hdom⟩ := hclω hcap
    have hτs : ((τE ω : ℝ≥0) : ℝ) ≤ Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω := by
      exact (show ((τE ω : ℝ≥0) : ℝ) ≤ (t' : ℝ) by exact_mod_cast hτt).trans_eq htime.symm
    obtain ⟨hdata, hform⟩ := postHead_explored (κ := κ) (θ := -(Real.pi / 2)) (W :=
      Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t' ω) (V := Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ
      (τE ω) ω) (s := Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω) hWc hW0 hVc (τE ω).coe_nonneg hτs
      hVW hrw hrt hcω hdom hcorr
    have hph : phChart κ E b jumps ℓ τE ω = (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
        (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω) ((τE ω : ℝ≥0) : ℝ) := by
      unfold phChart
      rw [show Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω = ((τE ω : ℝ≥0) : ℝ) from hτtime]
    refine ⟨hdata, fun v hv hvφ z hz => ?_⟩
    rw [hβω hcap v hv hvφ hz, hph]
    exact hform z hz
  -- B's own union mean (the engine in the post-head chart)
  obtain ⟨hA₁m0, hA₂m0, hd₁0, hl₁0, hl₂0, hlU0, hUm0, hUloc0, hc₁0, hc₂0, hform0, -, -, -, -, -, hformJ0, -, -, -,
    hJm0, hJc0, -, hJloc0⟩ := hfam t
  have hUmΩ : ∀ t', Measurable[mΩ, hittingSigma] (fun ω => A₁ t' ω ∪ A₂ t' ω) := fun t' => by
    obtain ⟨-, -, -, -, -, -, hUm, -⟩ := hfam t'
    exact hUm.mono (by rw [← h𝓖 t']; exact 𝓖.le t') le_rfl
  have hcU : ∀ t', ∀ ω, A₁ t' ω ∪ A₂ t' ω ⊆ H ∧ IsOpen (H \ (A₁ t' ω ∪ A₂ t' ω)) := fun t' ω => by
    obtain ⟨-, -, -, -, -, -, -, -, hc₁, hc₂, -⟩ := hfam t'
    refine ⟨union_subset (hc₁ ω).1 (hc₂ ω).1, ?_⟩
    have e : H \ (A₁ t' ω ∪ A₂ t' ω) = (H \ A₁ t' ω) ∩ (H \ A₂ t' ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, mem_union]
      tauto
    rw [e]
    exact (hc₁ ω).2.inter (hc₂ ω).2
  obtain ⟨gB, hgB⟩ : ∃ gB : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      ∀ t', IsLocalSetMean (fun ω => A₁ t' ω ∪ A₂ t' ω) (WholeField.centredField h u₀) P (gB t') := by
    choose gB hgB using fun t' => IsLocalSet.exists_isLocalSetMean hh0 (hUmΩ t') (hfam t').2.2.2.2.2.1
    exact ⟨gB, hgB⟩
  have hB := ae_lineMean_pos_rootG (κ := κ) hκ hh hu₀ S hKc hKp hsort (fun t' => (hfam t').1)
    (fun t' => (hfam t').2.1) (fun t' => (hfam t').2.2.1) (fun t' => (hfam t').2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.1) (fun t' => (hfam t').2.2.2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.2.1) (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.2.2.1)
    (c := phChart κ E b jumps ℓ τE) (wB := phDrv E b jumps ℓ τE) (sB := phTime E b jumps ℓ τE)
    (C := fun t' => {ω | ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t' ∧ τE ω ≤ t'})
    (fun t' => by filter_upwards [hpb t'] with ω h1 h2; exact h1 h2.1 h2.2) hind₂ hfill hF3 hC hS2 gB hgB m w hw t
  -- the transfer to the joint union
  have hXH : ∀ ω, (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ⊆ H := fun ω =>
    union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)
  have hYH : ∀ ω, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
      (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω ⊆
        H := fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω
  have hXY : (fun ω => (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) =
      fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω := by
    funext ω
    have hsub := WalkLaw.stageSet_mono (κ := κ) (b := b) (jumps := jumps)
      (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω (Nat.le_succ ℓ)
    rw [union_assoc, union_eq_right.2 hsub]
  have hJ := Cs.hmean_joint_of_hmeanB hh0 hKc hKp (S.ver m) hw t hXH hYH
    (hform0.mono fun ω h => h.1) (hform0.mono fun ω h => h.2) (by rw [hXY]; exact hformJ0)
    (by rw [h𝓖 t]; exact hUm0) (by rw [h𝓖 t]; exact hJm0) (hcU t) hJc0 (by rw [h𝓖 t]; exact hUloc0)
    (by rw [h𝓖 t]; exact hJloc0) (hgB t) (hg t) (fun ω => h ω - WholeField.centredField h u₀ ω)
    (-(Real.pi / 2) * chiC κ) (chiC κ) (fun ω => ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω)
      ((S.ver m).a t ω).toNNReal (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W
        (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w)) (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w))
        ω ((S.ver m).a t ω).toNNReal) z * φ z) φ (by
      filter_upwards [hB] with ω h1 hcell hpos hlt hdis
      exact h1 hcell hlt hpos φ hdis)
  exact hJ

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **K2's joint-set inputs from the root's line family** (`hBm`, `hBc`, `hBl`, `hloc` of `Cr.ae_k2_root` for the
joint union). -/
theorem k2Inputs_of_rootSets {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
    {u₀ : ℂ → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) :
    (∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂J t ω)) ∧
      (∀ t ω, A₁ t ω ∪ A₂J t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂J t ω))) ∧
      (∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂J t ω) (WholeField.centredField h u₀) P) ∧
      ∀ t, IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂J t ω) (WholeField.centredField h u₀) P := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJm, -⟩ := hfam t
    exact hJm.mono (by rw [← h𝓖 t]; exact 𝓖.le t) le_rfl
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJc, -⟩ := hfam t
    exact hJc
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJl, -⟩ := hfam t
    exact hJl
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJloc⟩ := hfam t
    rw [h𝓖 t]
    exact hJloc

end Root

end InteractingSLE.Theorem14.SB.Cx
