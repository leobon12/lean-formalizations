/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LatePocket
import InteractingSLE.Spec.Sec7.StripMarks513
import InteractingSLE.Spec.Sec7.StripMarksULift

/-!
# Lemma 7.25's determination reference from the pocket word's own strip objects

Packet PROVE-STRIPMARKS. Theorem 1.2's wiring (`Wire.theorem12Statement_late`, PROVE-WIRE-PARTA) supplies the pocket
word (`Wire.late_pocketWordFamily`) from one strip experiment per both-low pair (`word`, `hWord*`, `wordSide`,
`hSide*`), and Lemma 7.25's determination reference (`Wire.late_determinationReferenceFamily`, the `hStripMarks` slot)
from a second, independent family of reference objects with its own ~45 source, side and Proposition 5.13 inputs.
Lemma 7.25's proof (pp. 413–414) uses ONE construction: the strip coupling of Aux. lemma 130. Here the reference is read
off the pocket word's own strip objects:

* **`late_pocketChartField_strip`**: `PocketChartFieldStatement κ' rL rR` (in `Type`) from the pocket word's exact
  binders (the side input in the collector form of `Wire.late_pocketSideInput`), the Figure 5.1 frame of the strip word,
  and the canonical schedules' experiments and killed laws (`StripMarks.h513_of_stripSystem`);
* **`late_determinationReferenceFamily_strip`**: `Aux50Hit.Lemma725DetReferenceStatement.{u}` for every universe, from
  the same families (`lemma725DetReferenceStatement_ulift`).

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the restricted
determination `h44` is derived from the A.1 cores through Lemma 4.7Q and A.2 (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

universe u v

namespace InteractingSLE.Sec7.StripMarks

open Wire Current WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt Sec7.PocketWordIn
  StripSysField
open Exist.Staged (IsRegularDriver)
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract
  Sec5.Prop513Asm Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit
  Sec5.Prop59Nodes Sec5.Prop513Bridge
open Restart Exist Exist.StagedLaw

/-- **Lemma 7.25's field reference from the pocket word's strip objects** (Aux. lemma 130's strip coupling): the
source binders are exactly those of `Wire.late_pocketWordEvolution` (the side input in the form produced by
`Wire.late_pocketSideInput` from the side collector), and Proposition 5.13 for the strip's own counterflow comes from
the Figure 5.1 frame of the strip word with the canonical schedules' experiments and fixed-candidate killed laws. -/
theorem late_pocketChartField_strip {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement)
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
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp (16 / i.kappa) x.measure Pa
      (rootTgt x.driver (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) i.kappa_gt_four f.toLate hb
          (counterflowObjects hS.counterflow).field))) treeTime))
      (fun _ => univ))
    (hReg₀ : ∀ r : ℚ, 0 < r → IsRegFam (X₀.cand r))
    (hStart₀ : ∀ r : ℚ, 0 < r → Measurable (X₀.y₀ r))
    (hEvent₀ : ∀ r : ℚ, 0 < r → MeasurableSet[X₀.base r] (X₀.R₀ r))
    (hLaw₀ : ∀ r : ℚ, 0 < r → Late.CandidateLaw X₀ r)
    (X : ∀ n, HistExp (16 / i.kappa) x.measure Pa
      (nodeTgt x.driver (extremeAngleTreeDescendants (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) i.kappa_gt_four f.toLate hb
          (counterflowObjects hS.counterflow).field)))
        treeTime descendantIndex n))
      (nodeAct (fun ω t => x.curve ω t) (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) i.kappa_gt_four f.toLate hb
          (counterflowObjects hS.counterflow).field))) treeTime n)))
    (hReg : ∀ n, ∀ r : ℚ, 0 < r → IsRegFam ((X n).cand r))
    (hStart : ∀ n, ∀ r : ℚ, 0 < r → Measurable ((X n).y₀ r))
    (hEvent : ∀ n, ∀ r : ℚ, 0 < r → MeasurableSet[(X n).base r] ((X n).R₀ r))
    (hLaw : ∀ n, ∀ r : ℚ, 0 < r → Late.CandidateLaw (X n) r) :
    Lemma725RefSafe.PocketChartFieldStatement.{0} i.kappa i.leftWeight i.rightWeight := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by
    field_simp
  have hA := late_partAInputs hCore hCoreEight
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := late_theorem12ParamCond44Statement hCore hCoreEight
  have h513 := h513_of_stripSystem hCrossLeft hCrossRight hCore hCoreEight hQ i.kappa_gt_four hS hηtr f hb hword
    X₀ hReg₀ hStart₀ hEvent₀ hLaw₀ X hReg hStart hEvent hLaw x.harmonic
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
