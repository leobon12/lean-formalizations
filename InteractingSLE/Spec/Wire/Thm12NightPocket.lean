/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightInputs

/-!
# Lemma 7.25's strip determination from the shared Figure 5.1 killed-law input

PROVE-WIRE-PARTA. Reuses StripMarks513K's exact field transport and Hsd's
universal Figure 5.1 assembly. No abstract reference experiments are required.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire
open Sec7 Sec7.StripMarks Sec7.PocketWordIn Sec7.StripSysField
open Sec5 Sec5.Prop513Bridge Sec5.StripRevVisit Sec7.AdmCode
open WholeField Restart Sec4 Exist.Staged Exist.StagedLaw
open Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target

theorem night_h513_of_stripSystem
    (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hFH : StagedPrefixFirstHitStatement.{0})
    {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem (16 / k) b J P h W ζ E) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (f : Frame) (hκ : 0 < 16 / k) (hκ4 : 16 / k < 4) (hb : IsFig51Bounds (16 / k) f.a f.b f.a' f.b')
    (hword : ∀ x ∉ counterflowJumps J ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      counterflowData (16 / k) b x = stripCounterflowData (16 / k) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') x)
    (hlaws : Hsd.Fig51CandLawsStatement h44)
    (u : ℂ → ℝ) :
    let d := counterflowObjects hS.counterflow
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField d.field d.mean ω + smoothDist upperHalfPlaneOpens u) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
  intro d
  have hfl := stripCounterflow_isFlowLineDriver hS
  have hbP := isPiecewiseConstant_counterflowData (16 / k) hS.boundaryData
  have hG := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
    (div_pos (by norm_num) hκ) hbP hfl
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hG hword
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * f.x₀)))
      (-1) (-(π * chiC (16 / k))) (chiC (16 / (16 / k))) (fig51Source (16 / k) f.x₀ d.field ω) (d.field ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (d.field ω)
  have hcf : IsStripCounterflowDriver (16 / k) 0 (Real.exp (π * f.x₀)) P
      (fig51Source (16 / k) f.x₀ d.field) W ζ := by
    refine ⟨counterflowData (16 / k) b, counterflowJumps J, d.field, hbP, ?_, hfl⟩
    simpa only [zero_add] using hTF
  have htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t : ℝ≥0 => η ω t) := by
    filter_upwards [hηtr, hS.lifetime] with ω hω hζ
    rw [hζ]
    exact hω
  rw [comap_centredField_add]
  obtain ⟨Γ', hm, he⟩ := Hsd.prop513_path_of_fig51CandLaws h44 hA hFH hlaws hκ hκ4 hb
    (𝒢 := MeasurableSpace.comap (fig51Source (16 / k) f.x₀ d.field) inferInstance) (comap_measurable _)
    hGF hcf htr
  refine ⟨Γ', ?_, he⟩
  intro t
  rw [← comap_eq_strip_parameter (Real.exp_pos _) hTF]
  exact hm t

open Current WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls
open Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan
open Sec7.PocketMarks Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
open Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
open Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt

theorem night_pocketChartField {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hQ : FrameQ.QScheduleFirstHitStatement.{0})
    (haux7 : Sec4.Aux7Statement.{0} i.kappa)
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (hsw : Sec5.RestartGen.SwitchedWallFirstHitStatement.{0})
    (hS : StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime
      x.experiment)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθ₁ : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
    (hr : ∀ j ω, IsRegularDriver (x.experiment (StripSys.alphaSpec x.thetaR) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (x.experiment (StripSys.betaSpec (StripSys.rt q) x.thetaL) j ω))
    (he : ∀ ω, IsRegularDriver (x.experiment StripSys.leftExtremalSpec 0 ω))
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hvα : IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall)
    (hvL : ∀ q, IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
    (hβc : ∀ ω, Continuous (x.outerWall ω))
    (hβ0 : ∀ ω, x.outerWall ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => x.outerWall ω t)
    (hβtr : ∀ᵐ ω ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec 0 ω).1 ⊤ (x.outerWall ω))
    (hηc : ∀ ω, ContinuousOn (x.curve ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
    (hη0 : ∀ ω, x.curve ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => x.curve ω t)
    (hηtr : ∀ᵐ ω ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0 => x.curve ω t))
    (hu : InnerProductSpace.HarmonicOnNhd x.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
    (hside : let d := Now.wordObjects i x hS
      ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)] G →
      0 < d.measure G →
      (∀ ω ∈ G, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, d.lifetime ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
        IsCfPocketConfig (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
          (d.curve ω)) →
      (∀ ω ∈ G, rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
          (d.curve ω)) →
      PocketSideLimitInput0 (16 / i.kappa) i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall q))
          d.measure d.rightWall (d.leftWall q) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)}
          (centredField d.translatedField d.coupledMean) d.harmonic ∧
        PocketSideLimitInputInf0 (16 / i.kappa) i.leftWeight i.rightWeight
          (wallsSigma d.measure d.rightWall (d.leftWall q)) d.measure d.rightWall (d.leftWall q) (StripSys.rt q)
          d.curve {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)}
          (centredField d.translatedField d.coupledMean) d.harmonic)
    (f : Frame) (hb : IsFig51Bounds (16 / i.kappa) f.a f.b f.a' f.b')
    (hword : ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      counterflowData (16 / i.kappa) x.boundary y = stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') y)
    (hlaws : Hsd.Fig51CandLawsStatement (late_theorem12ParamCond44Statement hCore hCoreEight)) :
    Lemma725RefSafe.PocketChartFieldStatement.{0} i.kappa i.leftWeight i.rightWeight := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by
    field_simp
  have hA := late_partAInputs hCore hCoreEight
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := late_theorem12ParamCond44Statement hCore hCoreEight
  have hFH := FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have h513 := night_h513_of_stripSystem h44 hA hFH hS hηtr f (sixteen_div_kappa_pos i)
    (sixteen_div_kappa_lt_four i) hb hword hlaws x.harmonic
  have hp := pocketChartFieldStatement_of_stripSystem_restartGen h44
    (by rw [hdual]; exact haux7) h411 h47 hsw hS hleft hright hθ₁ hθ₂
    i.left_gt (by simpa only [hdual] using i.left_lt)
    i.right_gt (by simpa only [hdual] using i.right_lt)
    hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr hηc hηH hη0 hηm hηtr hu hub
    (by
      intro q hq G hG hPG hconf hζG hcfg hcfgI
      have hs := hside q hq G hG hPG hconf hζG hcfg hcfgI
      constructor
      · convert hs.1 using 1 <;> simp only [Now.wordObjects, hdual]
      · convert hs.2 using 1 <;> simp only [Now.wordObjects, hdual])
    h513
  simpa only [hdual] using hp

end InteractingSLE.Wire
