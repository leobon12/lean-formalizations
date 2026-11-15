/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideAncZero
import InteractingSLE.Spec.Sec5.WordSafeWire

/-! # Aux. 122 and zeroed side data on the two-angle family

Adapter of the committed SideAncWire and SideAncZero proofs. The walls are
regularized by WordSafe.regTwo; only Cond44 determination is used (R74).
The raw reference and collar assertions keep every valid local-set mean.
-/
set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm

open Wire Current Sec7 LocalSets WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls
  Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.RefWire Sec7.PocketWordIn StripSysField
open Sec5.Prop59Pieces Sec5.Prop59NodeTree Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand
  Sec5.Prop513Bridge
open Sec7.Aux119Heights Sec7.PhaseSel
open Exist.Staged (IsRegularDriver)
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract Sec5.Prop513Asm
  Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit Sec5.Prop59Nodes
open Restart Exist Exist.Staged Exist.StagedLaw


open Sec7.StripMarks

variable (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
variable (Ωw : BothLow → Type) [mWord : ∀ i, MeasurableSpace (Ωw i)]
    [hWordBorel : ∀ i, StandardBorelSpace (Ωw i)]
    (word : ∀ i, Now.StripObjects (Ωw i)) [hWordProbability : ∀ i, IsProbabilityMeasure (word i).measure]
    (wordSide : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
variable (hWordT : ∀ i, let x := word i; Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa)
      x.boundary x.jumps x.measure x.field
      x.driver x.lifetime x.experiment)
variable (hWordleft : ∀ i, let x := word i; ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
variable (hWordright : ∀ i, let x := word i; ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
variable (hWordθ₁ : ∀ i, let x := word i; x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
variable (hWordθ₂ : ∀ i, let x := word i; x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
variable (hWorde : ∀ i, let x := word i; ∀ ω, IsRegularDriver (x.experiment StripSys.leftExtremalSpec 0 ω))
variable (hWordu₀ : ∀ i, let x := word i; IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
variable (hWordvα : ∀ i, let x := word i; IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1
      x.rightWall)
variable (hWordvL : ∀ i, let x := word i; ∀ q, IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt
      (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
variable (hWordβc : ∀ i, let x := word i; ∀ ω, Continuous (x.outerWall ω))
variable (hWordβ0 : ∀ i, let x := word i; ∀ ω, x.outerWall ω 0 = 0)
variable (hWordβm : ∀ i, let x := word i; ∀ t, Measurable fun ω => x.outerWall ω t)
variable (hWordβtr : ∀ i, let x := word i; ∀ᵐ ω ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec
      0 ω).1 ⊤ (x.outerWall ω))
variable (hWordηc : ∀ i, let x := word i; ∀ ω, ContinuousOn (x.curve ω) (Ici 0))
variable (hWordηH : ∀ i, let x := word i; ∀ ω, ∀ t : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
variable (hWordη0 : ∀ i, let x := word i; ∀ ω, x.curve ω 0 = 0)
variable (hWordηm : ∀ i, let x := word i; ∀ t : ℝ, 0 ≤ t → Measurable fun ω => x.curve ω t)
variable (hWordηtr : ∀ i, let x := word i; ∀ᵐ ω ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0
      => x.curve ω t))
variable (hWordu : ∀ i, let x := word i; InnerProductSpace.HarmonicOnNhd x.harmonic H)
variable (hWordub : ∀ i, let x := word i; ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
variable (hWord𝔥 : ∀ i, let x := word i; ∀ φ : TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
variable (hSidepre : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤
        (mWord index))
variable (hSideFo : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
variable (hSideRawReference : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event
        target.curve target.domain (refs.sets i) target.zeroField refs.level)
variable (hSideLattice : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife
        (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
variable (hSideCollar : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀
        gB : ℕ → (Ωw index) → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
          target.zeroField target.measure (gB i)) →
      ∀ g : (Ωw index) → DistOn upperHalfPlaneOpens, IsLocalSetMean ((activeCompl target.event target.curve
          target.baseChart) q) target.zeroField target.measure g →
      ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart)
            q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (activeCompl target.event target.curve
              target.baseChart) q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve
                ω) q)
            (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve
                ω) q) →
            ∃ (i : ℕ) (b d : ℝ),
              let inv := (relChart target.baseChart target.curve q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt target.event target.curve target.domain (refs.sets i)
                  refs.level ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + target.harmonic (inv y) + chiC target.kappa * refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) - refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
                (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver
                    (target.curve ω) q)
                (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver
                    (target.curve ω) q)
                ξ + refs.phase q ω * (Ioo
                  (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                    zL q ω - segDriver (target.curve ω) q)
                  (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset)

section
include h44 hWordProbability hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα
  hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar

/-- **The late side phase vanishes** (Aux. lemma 122 in the bounded sector of the both-low late pockets): on every
Ready late side test, at every positive time, almost surely on the live event. From the raw reference laws (R.5 up to
phase) and the strip system's walls. -/
theorem sidePhaseZero : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂target.measure, ω ∈ target.event →
          (q : ℝ≥0∞) < capLife (target.curve ω) → refs.phase q ω = 0 := by
  intro index
  have hS := hWordT index
  have hu₀ := hWordu₀ index
  have hvα := hWordvα index
  have hk4 : 4 < index.kappa := index.kappa_gt_four
  have hdual : 16 / (16 / index.kappa) = index.kappa := by field_simp
  have hk0 : 0 < 16 / index.kappa := div_pos (by norm_num) (by linarith)
  have hk4' : 16 / index.kappa < 4 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have hrL' : index.leftWeight < 16 / (16 / index.kappa) - 6 := by rw [hdual]; linarith [index.left_lt]
  have hrR' : index.rightWeight < 16 / (16 / index.kappa) - 6 := by rw [hdual]; linarith [index.right_lt]
  have hκ' : 0 < 16 / (16 / index.kappa) := by rw [hdual]; linarith
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hX := counterflowObjects_measurable hS.counterflow
  have hh := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hZ := isZeroBoundaryGFF_centredField hC hu'
  intro i x d j hj
  have hpre := hSidepre index j hj
  have hFo := hSideFo index j hj
  have hRaw := hSideRawReference index j hj
  have hLat := hSideLattice index j hj
  have hCol := hSideCollar index j hj
  rcases j with ⟨seed, outer, event, chart, infinite, twoLeft⟩
  obtain ⟨hq, hGm, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩ := hj
  have hvL : IsWallVersion (word index).measure
      ((word index).experiment (StripSys.betaSpec (StripSys.rt seed) (word index).thetaL)) (StripSys.rt seed)
      ((word index).leftWall seed) := by
    simpa only [positiveSeed_of_pos hq] using hWordvL index seed
  have hreg := Sec7.WordSafe.isTwoAngle_regTwo hS (hWordleft index) (hWordright index)
  obtain ⟨hdR, hlR, hdL, hlL⟩ := Sec7.WordSafe.wall_inputs h44 hreg
    (hWordleft index) (hWordright index)
    (Ioo_subset_Icc_self (hWordθ₁ index)) (Ioc_subset_Icc_self (hWordθ₂ index)) (positiveSeed_pos seed)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) hu₀
    (Sec7.WordSafe.isWallVersion_regTwo hS (hWordleft index) (hWordright index)
      StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self (hWordθ₁ index)) hvα)
    (Sec7.WordSafe.isWallVersion_regTwo hS (hWordleft index) (hWordright index)
      StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self (hWordθ₂ index)) (hWordvL index seed))
  have hRm' := measurable_right_wallsSigma (P := (word index).measure) hvα.continuous hvL.continuous
  have hLm' := measurable_left_wallsSigma (P := (word index).measure) hvα.continuous hvL.continuous
  have hGp := (measurableSet_rightLo_pos_and (mΩ := wallsSigma (word index).measure (word index).rightWall
    ((word index).leftWall seed)) hRm' hLm' hGm (fun ω hω => (hconf ω hω).1)).1
  have hG0 : MeasurableSet[wallsSigma (word index).measure (word index).rightWall ((word index).leftWall seed)]
      {ω | ω ∈ outer ∧ ¬ 0 < rightLo ((word index).rightWall ω) ((word index).leftWall seed ω) (StripSys.rt seed)} := by
    have e : {ω | ω ∈ outer ∧ ¬ 0 < rightLo ((word index).rightWall ω) ((word index).leftWall seed ω)
        (StripSys.rt seed)} = outer \ {ω | ω ∈ outer ∧ 0 < rightLo ((word index).rightWall ω)
        ((word index).leftWall seed ω) (StripSys.rt seed)} := by
      ext ω
      exact ⟨fun h => ⟨h.1, fun h' => h.2 h'.2⟩, fun h => ⟨h.1, fun h' => h.2 ⟨h.1, h'⟩⟩⟩
    rw [e]
    exact hGm.diff hGp
  cases infinite <;> cases twoLeft
  · intro target refs
    refine Sec7.SideAnc.late_zero_one (R := (word index).rightWall) (L := (word
      index).leftWall seed)
      (r := StripSys.rt seed) (η := (word index).curve)
      (G := {ω | ω ∈ outer ∧ 0 < rightLo ((word index).rightWall ω) ((word index).leftWall seed ω)
        (StripSys.rt seed)}) (A := event) (ψ := chart) hk0 hk4' index.left_gt hrL' index.right_gt hrR'
      hT hTr hu₀.1 hh hC hκ' hu' hX hS.lifetime hvα.continuous hvL.continuous hvα.zero hvL.zero hvα.measurable
      hvL.measurable hdR hdL hlR hlL (hWordηm index) hGp (fun ω hω => hcfg ω hω.1 hω.2) (fun ω hω => hζG ω hω.1)
      (hWordu index) (hWordub index) hA hAG hPA hJordan hPoint (n := fun _ => 0) (a' := refs.offset)
      measurable_const fun q => ?_
    simp only [Sec7.SideAnc.shiftChart_zero]
    exact PocketStopSide.pocketStopPhaseSideLimit_of_raw_reference_germs hZ hpre
        (fun ω _ => isOpen_image_negInv' (hconf ω (hAG ‹_›).1).1.isOpen_changePocket
          (hconf ω (hAG ‹_›).1).1.changePocket_subset_H) hFo hRaw (hLat q) (hCol q)
  · intro target refs
    refine Sec7.SideAnc.late_zero_two (R := (word index).rightWall) (L := (word
      index).leftWall seed)
      (r := StripSys.rt seed) (η := (word index).curve)
      (G := {ω | ω ∈ outer ∧ 0 < rightLo ((word index).rightWall ω) ((word index).leftWall seed ω)
        (StripSys.rt seed)}) (A := event) (ψ := chart) hk0 hk4' index.left_gt hrL' index.right_gt hrR'
      hT hTr hu₀.1 hh hC hκ' hu' hX hS.lifetime hvα.continuous hvL.continuous hvα.zero hvL.zero hvα.measurable
      hvL.measurable hdR hdL hlR hlL (hWordηm index) hGp (fun ω hω => hcfg ω hω.1 hω.2) (fun ω hω => hζG ω hω.1)
      (hWordu index) (hWordub index) hA hAG hPA hJordan hPoint hShape (n := fun _ => 0) (a' := refs.offset)
      measurable_const fun q => ?_
    simp only [Sec7.SideAnc.shiftChart_zero]
    exact PocketStopSide.pocketStopPhaseSideLimit_of_raw_reference_germs hZ hpre
        (fun ω _ => isOpen_image_negInv' (hconf ω (hAG ‹_›).1).1.isOpen_changePocket
          (hconf ω (hAG ‹_›).1).1.changePocket_subset_H) hFo hRaw (hLat q) (hCol q)
  · intro target refs
    refine Sec7.SideAnc.late_zero_oneInf (R := (word index).rightWall) (L := (word
      index).leftWall seed)
      (r := StripSys.rt seed) (η := (word index).curve)
      (G := {ω | ω ∈ outer ∧ ¬ 0 < rightLo ((word index).rightWall ω) ((word index).leftWall seed ω)
        (StripSys.rt seed)}) (A := event) (ψ := chart) hk0 hk4' index.left_gt hrL' index.right_gt hrR'
      hT hTr hu₀.1 hh hC hκ' hu' hX hS.lifetime hvα.continuous hvL.continuous hvα.zero hvL.zero hvα.measurable
      hvL.measurable hdR hdL hlR hlL (hWordηm index) hG0
      (fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).1.changeCorner_props.1.1))) (fun ω hω =>
      hζG ω hω.1)
      (hWordu index) (hWordub index) hA hAG hPA hJordan hPoint (n := fun _ => 0) (a' := refs.offset)
      measurable_const fun q => ?_
    simp only [Sec7.SideAnc.shiftChart_zero]
    exact PocketStopSide.pocketStopPhaseSideLimit_of_raw_reference_germs hZ hpre
        (fun ω _ => isOpen_image_negInv' (hconf ω (hAG ‹_›).1).1.isOpen_changePocket
          (hconf ω (hAG ‹_›).1).1.changePocket_subset_H) hFo hRaw (hLat q) (hCol q)
  · intro target refs
    refine Sec7.SideAnc.late_zero_twoInf (R := (word index).rightWall) (L := (word
      index).leftWall seed)
      (r := StripSys.rt seed) (η := (word index).curve)
      (G := {ω | ω ∈ outer ∧ ¬ 0 < rightLo ((word index).rightWall ω) ((word index).leftWall seed ω)
        (StripSys.rt seed)}) (A := event) (ψ := chart) hk0 hk4' index.left_gt hrL' index.right_gt hrR'
      hT hTr hu₀.1 hh hC hκ' hu' hX hS.lifetime hvα.continuous hvL.continuous hvα.zero hvL.zero hvα.measurable
      hvL.measurable hdR hdL hlR hlL (hWordηm index) hG0
      (fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).1.changeCorner_props.1.1))) (fun ω hω =>
      hζG ω hω.1)
      (hWordu index) (hWordub index) hA hAG hPA hJordan hPoint hShape (n := fun _ => 0) (a' := refs.offset)
      measurable_const fun q => ?_
    simp only [Sec7.SideAnc.shiftChart_zero]
    exact PocketStopSide.pocketStopPhaseSideLimit_of_raw_reference_germs hZ hpre
        (fun ω _ => isOpen_image_negInv' (hconf ω (hAG ‹_›).1).1.isOpen_changePocket
          (hconf ω (hAG ‹_›).1).1.changePocket_subset_H) hFo hRaw (hLat q) (hCol q)

end

section
include hSideLattice

/-- The lattice binder for the zeroed side data. -/
theorem zeroedLattice : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife
        (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa := by
  intro index
  dsimp only
  intro j hj q
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq | hq
  · subst hq
    filter_upwards [hSideLattice index j hj 0] with ω hω hωA hl
    obtain ⟨m, hm⟩ := hω hωA hl
    exact ⟨m, by rw [Late.SideData.zeroed_phase_zero]; exact hm⟩
  · exact Eventually.of_forall fun ω _ _ => ⟨0, by rw [Late.SideData.zeroed_phase_of_pos _ hq]; simp⟩
end

section
include h44 hWordProbability hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα
  hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar

/-- The collar binder for the zeroed side data, from the original one and `sidePhaseZero`. -/
theorem zeroedCollar : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
        ∀ q : ℝ≥0, ∀
        gB : ℕ → (Ωw index) → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
          target.zeroField target.measure (gB i)) →
      ∀ g : (Ωw index) → DistOn upperHalfPlaneOpens, IsLocalSetMean ((activeCompl target.event target.curve
          target.baseChart) q) target.zeroField target.measure g →
      ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart)
            q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (activeCompl target.event target.curve
              target.baseChart) q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve
                ω) q)
            (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve
                ω) q) →
            ∃ (i : ℕ) (b d : ℝ),
              let inv := (relChart target.baseChart target.curve q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt target.event target.curve target.domain (refs.sets i)
                  refs.level ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + target.harmonic (inv y) + chiC target.kappa * refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) - refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
                (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver
                    (target.curve ω) q)
                (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver
                    (target.curve ω) q)
                ξ + refs.phase q ω * (Ioo
                  (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                    zL q ω - segDriver (target.curve ω) q)
                  (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset := by
  intro index
  dsimp only
  intro j hj q gB hgB g hg
  have hcol := hSideCollar index j hj q gB hgB g hg
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq | hq
  · subst hq
    filter_upwards [hcol] with ω hω hωA hl v hv hvr ξ hξ
    obtain ⟨i', b, d', h1, h2, h3, h4⟩ := hω hωA hl v hv hvr ξ hξ
    exact ⟨i', b, d', h1, h2, h3, by rw [Late.SideData.zeroed_phase_zero]; exact h4⟩
  · have hz := sidePhaseZero h44 Ωw word wordSide hWordT hWordleft hWordright hWordθ₁ hWordθ₂
      hWordu₀ hWordvα hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice
      hSideCollar index j hj q hq
    filter_upwards [hcol, hz] with ω hω hz' hωA hl v hv hvr ξ hξ
    obtain ⟨i', b, d', h1, h2, h3, h4⟩ := hω hωA hl v hv hvr ξ hξ
    refine ⟨i', b, d', h1, h2, h3, ?_⟩
    rw [Late.SideData.zeroed_phase_of_pos _ hq]
    rw [hz' hωA hl] at h4
    exact h4
end

/-- The probe binder for the zeroed side data (constant probes). -/
theorem zeroedProbes : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧
          refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t := by
  intro index
  dsimp only
  intro j hj N
  refine Eventually.of_forall fun ω _ => ⟨continuousOn_const, continuousOn_const, continuousOn_const,
    fun t ht => ⟨one_pos, ?_⟩⟩
  show (0 : ℝ) - 0 = (wordSide index j).zeroed.phase t ω * 1
  rw [Late.SideData.zeroed_phase_of_pos _ ht.1]
  ring

/-- The visit binder for the zeroed side data (a positive rational live time). -/
theorem zeroedVisits : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i := by
  intro index
  dsimp only
  intro j hj
  refine Eventually.of_forall fun ω _ hpos => ?_
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn hr0'
  have hq0' : 0 < ((q : ℝ)).toNNReal := Real.toNNReal_pos.2 hq0
  refine ⟨q, hq0', lt_trans (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe hq0.le).2 hqr)) hr, ?_⟩
  show (wordSide index j).zeroed.phase ((q : ℝ)).toNNReal ω = 0
  exact Late.SideData.zeroed_phase_of_pos _ hq0' ω

end InteractingSLE.Wire.T12Asm
