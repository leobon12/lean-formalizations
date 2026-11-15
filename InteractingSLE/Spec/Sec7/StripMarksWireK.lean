/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripMarksWire
import InteractingSLE.Spec.Sec7.StripMarks513K

/-!
# Lemma 7.25's reference from the strip objects, with Proposition 5.13's experiments constructed

Packet PROVE-STRIPMARKS. As `StripMarksWire`, with Proposition 5.13 for the strip's counterflow taken from the killed
laws of the fixed concrete root and node candidates (`StripMarks.h513_of_stripSystem_candLaws`) instead of abstract
`HistExp` experiments. Also: the two localized GB8 crossing comparisons of PROVE-WIRE-PARTA
    (`Wire.Late.CrossLeftKStatement`,
`Wire.Late.CrossRightKStatement`) are exactly PROVE-STAGED9's proved `compPremiseFarK_crossL/R`.

* **`late_crossLeftK`**, **`late_crossRightK`**: the crossing statements, proved;
* `sixteen_div_kappa_pos`, `sixteen_div_kappa_lt_four`: `0 < 16/κ' < 4` for a both-low pair;
* **`late_pocketChartField_stripK`**: `PocketChartFieldStatement κ' rL rR` (in `Type`) from the pocket word's binders,
  the Figure 5.1 frame of the strip word and the killed laws of the concrete candidates.

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.StripMarks

open Wire Current WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt Sec7.PocketWordIn
  StripSysField
open Exist.Staged (IsRegularDriver)
open Sec5 Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Exist.StagedLaw Exist.Staged
  Sec7.AdmCode Restart Sec4 Theorem14.StagedReg Sec5.GlueCond Sec5.CrossCond.Word49 LawUnique
  Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.Prop59Nodes Sec5.Prop59NodeTree Sec5.Prop59Tips
  Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand Sec5.Prop59Sched Sec5.StripRevVisit
  Sec5.Prop513Asm Sec5.Prop513Bridge

/-- **The localized GB8 left crossing comparison** of Theorem 1.2's wiring (`Wire.Late.CrossLeftKStatement`) is
PROVE-STAGED9's `CrossCond.StagedK2.compPremiseFarK_crossL`. -/
theorem late_crossLeftK : Late.CrossLeftKStatement := fun hκ hκ4 hnL hnR _ _ hw =>
  compPremiseFarK_crossL hκ hκ4 hnL hnR hw

/-- **The localized GB8 right crossing comparison** of Theorem 1.2's wiring (`Wire.Late.CrossRightKStatement`) is
PROVE-STAGED9's `CrossCond.StagedK2.compPremiseFarK_crossR`. -/
theorem late_crossRightK : Late.CrossRightKStatement := fun hκ hκ4 hnL hnR _ _ hw =>
  compPremiseFarK_crossR hκ hκ4 hnL hnR hw

theorem sixteen_div_kappa_pos (i : BothLow) : 0 < 16 / i.kappa :=
  div_pos (by norm_num) (by linarith [i.kappa_gt_four])

theorem sixteen_div_kappa_lt_four (i : BothLow) : 16 / i.kappa < 4 :=
  (div_lt_iff₀ (by linarith [i.kappa_gt_four])).2 (by linarith [i.kappa_gt_four])

/-- **Lemma 7.25's field reference from the pocket word's strip objects, with Proposition 5.13's experiments
constructed** (as `late_pocketChartField_strip`; Proposition 5.13 by `h513_of_stripSystem_candLaws`). -/
theorem late_pocketChartField_stripK {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
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
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (noise₀ : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base₀ : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase₀ : ∀ q, base₀ q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw₀ : let hP := fig51Source (16 / i.kappa) f.x₀ (counterflowObjects hS.counterflow).field
      ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK (16 / i.kappa) (x.measure.prod Pa)
      (canonQ (base₀ q) (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos
          i) (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime)
          (canonXL f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime)
        (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _)
            (rootNR_pos _)
        (rootStart f.x₀ (sixteen_div_kappa_pos i) hb (canonXL f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime)
            (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) q) j t)
      (canonR (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime)
        (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _)
            (rootNR_pos _)
        (rootStart f.x₀ (sixteen_div_kappa_pos i) hb (canonXL f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime)
            (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) q) univ j t)
      (stageρL (16 / i.kappa) (rootρL (16 / i.kappa) (sourceWord (x₀ := f.x₀) (sixteen_div_kappa_pos i) hb)) j)
      (stageρR (16 / i.kappa) (rootρR (16 / i.kappa) (sourceWord (x₀ := f.x₀) (sixteen_div_kappa_pos i) hb)) j)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
      (canonY (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime)
        (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) noise₀ (Ωa := Ωa) q) (rootStart f.x₀
            (sixteen_div_kappa_pos i) hb (canonXL f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime)
          (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) q) j t)
      (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver
          x.lifetime)
        noise₀ (Ωa := Ωa) q j t).W
      (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver
          x.lifetime)
        noise₀ (Ωa := Ωa) q j t).VL
      (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver
          x.lifetime)
        noise₀ (Ωa := Ωa) q j t).VR
      (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver
          x.lifetime)
        noise₀ (Ωa := Ωa) q j t).B
      (rootCand f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime (canonLam x.driver x.lifetime) (canonXL
          f.x₀ (sixteen_div_kappa_pos i) hb x.driver x.lifetime) (canonXR f.x₀ (sixteen_div_kappa_pos i) hb x.driver
          x.lifetime)
        noise₀ (Ωa := Ωa) q j t).ζ)
    (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : let hP := fig51Source (16 / i.kappa) f.x₀ (counterflowObjects hS.counterflow).field
      ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, IsStageLawFarK (16 / i.kappa) (x.measure.prod Pa)
      (canonQ (nodeBase f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise base n q)
        (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
            (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q) ratGrid
        (nodeNL_pos f.x₀ (sixteen_div_kappa_pos i) hb n) (nodeNR_pos f.x₀ (sixteen_div_kappa_pos i) hb n) (nodeStart
            f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
            (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q) j t)
      (canonR (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos
          i) (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q) ratGrid (nodeNL_pos f.x₀
          (sixteen_div_kappa_pos i) hb n)
        (nodeNR_pos f.x₀ (sixteen_div_kappa_pos i) hb n) (nodeStart f.x₀ (late_theorem12ParamCond44Statement hCore
            hCoreEight) (sixteen_div_kappa_pos i) (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime
            noise n q)
        (nodeR0 f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
            (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q) j t)
      (stageρL (16 / i.kappa) (nodeρL (16 / i.kappa) (sourceWord (x₀ := f.x₀) (sixteen_div_kappa_pos i) hb)
          (scheduleAt n)) j)
      (stageρR (16 / i.kappa) (nodeρR (16 / i.kappa) (sourceWord (x₀ := f.x₀) (sixteen_div_kappa_pos i) hb)
          (scheduleAt n)) j)
      (farL (Nat.lt_of_lt_of_le (nodeNL_pos f.x₀ (sixteen_div_kappa_pos i) hb n) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (nodeNR_pos f.x₀ (sixteen_div_kappa_pos i) hb n) (Nat.le_add_right _ j)))
      (canonY (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos
          i) (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q)
        (nodeStart f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
            (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q) j t)
      (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q j t).W
      (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q j t).VL
      (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q j t).VR
      (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q j t).B
      (nodeCand (Ωa := Ωa) f.x₀ (late_theorem12ParamCond44Statement hCore hCoreEight) (sixteen_div_kappa_pos i)
          (sixteen_div_kappa_lt_four i) hb x.measure hP x.driver x.lifetime noise n q j t).ζ) :
    Lemma725RefSafe.PocketChartFieldStatement.{0} i.kappa i.leftWeight i.rightWeight := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by
    field_simp
  have hA := late_partAInputs hCore hCoreEight
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := late_theorem12ParamCond44Statement hCore hCoreEight
  have hFH := FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have h513 := h513_of_stripSystem_candLaws h44 hA hFH hS hηtr f (sixteen_div_kappa_pos i)
    (sixteen_div_kappa_lt_four i) hb hword noise₀ base₀ hbase₀ hlaw₀ noise base hbase hlaw x.harmonic
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

end InteractingSLE.Sec7.StripMarks
