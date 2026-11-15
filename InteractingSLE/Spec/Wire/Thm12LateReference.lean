/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LateFrame
import InteractingSLE.Spec.Sec5.Prop513Bridge
import InteractingSLE.Spec.Wire.Thm12NowReference

/-! # Actual reference determination from corrected candidate laws and the concrete frame -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper LQGMetric
open SupercriticalConformalCovariance.GM24 (smoothDist)
universe u v
namespace InteractingSLE.Wire
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract
  Sec5.Prop513Asm Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit
  Sec5.Prop59Nodes Sec5.Prop513Bridge Sec5.CrossCond.StagedAdapt Sec5.CrossCond.StagedCand
open Restart Exist Exist.Staged Exist.StagedLaw

/-- Restricted determination, derived acyclically from the two rectangle cores. -/
theorem late_theorem12ParamCond44Statement
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ) :
    Sec7.AdmCode.Theorem12ParamCond44Statement.{u} :=
  theorem12ParamCond44Statement_of_lemma47Q_of_A2
    (late_lemma47QHitStatement (late_partAInputs hCore hCoreEight))
    (late_fourForceCrosscutG3LifeStatement hCore) (late_threeForceCrosscutEightStatement hCoreEight)

namespace Late

/-- Numerical frame and recorded word, without laws. -/
structure Frame where
  x₀ : ℝ
  a : ℝ
  b : ℝ
  a' : ℝ
  b' : ℝ
  boundary : ℝ → ℝ
  jumps : Finset ℝ

def schedules {Ω : Type u} (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {k : ℝ} (hk : 4 < k) (f : Frame)
    (hb : IsFig51Bounds (16 / k) f.a f.b f.a' f.b') (hP : Ω → DistOn upperHalfPlaneOpens) :=
  targetSched h44 (x₀ := f.x₀) (div_pos (by norm_num) (by linarith : 0 < k))
    ((div_lt_iff₀ (by linarith : 0 < k)).2 (by linarith)) hb (fig51Source (16 / k) f.x₀ hP)

/-- The exact per-candidate killed law on the canonical history tree. -/
def CandidateLaw {κ : ℝ} {Ω : Type u} {Ωa : Type v} [MeasurableSpace Ω] [MeasurableSpace Ωa]
    {P : Measure Ω} {Pa : Measure Ωa} [IsProbabilityMeasure P] [IsProbabilityMeasure Pa]
    {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : HistExp κ P Pa D A) (r : ℚ) : Prop :=
  ∀ j t, Sec5.CrossCond.StagedKill.IsStageLawFarK κ (P.prod Pa) (canonQ (X.base r) (X.cand r) (X.times r) (X.posL r) (X.posR r) (X.y₀ r) j t) (canonR (X.cand r) (X.times r) (X.posL r) (X.posR r) (X.y₀ r) (X.R₀ r) j t)
      (stageρL κ (X.rhoL r) j) (stageρR κ (X.rhoR r) j)
      (farL (Nat.lt_of_lt_of_le (X.posL r) (Nat.le_add_right (X.nL r) j)))
      (farR (Nat.lt_of_lt_of_le (X.posR r) (Nat.le_add_right (X.nR r) j)))
      (canonY (X.cand r) (X.y₀ r) j t) ((X.cand r) j t).W ((X.cand r) j t).VL ((X.cand r) j t).VR ((X.cand r) j t).B ((X.cand r) j t).ζ

end Late

/-- The adaptive killed stage law is supplied by fixed-candidate laws, with the
canonical tree consistency and the mixture step proved in StagedCandFar. -/
theorem late_histExp_stageLaw {κ : ℝ} {Ω : Type u} {Ωa : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} {Pa : Measure Ωa}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Pa]
    {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : HistExp κ P Pa D A) (r : ℚ)
    (hReg : IsRegFam (X.cand r)) (hStart : Measurable (X.y₀ r))
    (hEvent : MeasurableSet[X.base r] (X.R₀ r)) (hLaw : Late.CandidateLaw X r) :
    Late.StageLawK κ (P.prod Pa) (X.posL r) (X.posR r)
      (X.rhoL r) (X.rhoR r) (X.system r) :=
  fun rr j => Sec5.CrossCond.StagedCand.isCompLaw_histSys_canon
    (Φ := fun j => farPath κ (stageρL κ (X.rhoL r) j) (stageρR κ (X.rhoR r) j))
    (g := fun _ => stageObsRec)
    (Prem := fun j S p => Sec5.CrossCond.StagedKill.CompPremiseFarK κ
      (stageρL κ (X.rhoL r) j) (stageρR κ (X.rhoR r) j)
      (farL (Nat.lt_of_lt_of_le (X.posL r) (Nat.le_add_right (X.nL r) j)))
      (farR (Nat.lt_of_lt_of_le (X.posR r) (Nat.le_add_right (X.nR r) j))) univ S p)
    hReg hStart hEvent hLaw rr j

/-- The literal ambient reference determination leaf, expanded to its source word,
canonical schedules, root/node experiments and fixed-candidate killed laws. -/
theorem late_reference513
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement)
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hQ : FrameQ.QScheduleFirstHitStatement.{u})
    {k : ℝ} (hk : 4 < k) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (d : Now.ReferenceObjects Ω) [IsProbabilityMeasure d.measure]
    (f : Late.Frame) (hb : IsFig51Bounds (16 / k) f.a f.b f.a' f.b')
    (hbP : IsPiecewiseConstantBoundaryData f.boundary f.jumps)
    (hfl : IsFlowLineDriver k f.boundary f.jumps 0 d.measure d.translatedField d.driver d.lifetime)
    (hword : ∀ x ∉ f.jumps ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      f.boundary x = stripCounterflowData (16 / k) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') x)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (htrace : ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp (16 / k) d.measure Pa
      (rootTgt d.driver (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) hk f hb d.translatedField))) treeTime))
      (fun _ => univ))
    (hReg₀ : ∀ r : ℚ, 0 < r → IsRegFam (X₀.cand r))
    (hStart₀ : ∀ r : ℚ, 0 < r → Measurable (X₀.y₀ r))
    (hEvent₀ : ∀ r : ℚ, 0 < r → MeasurableSet[X₀.base r] (X₀.R₀ r))
    (hLaw₀ : ∀ r : ℚ, 0 < r → Late.CandidateLaw X₀ r)
    (X : ∀ n, HistExp (16 / k) d.measure Pa
      (nodeTgt d.driver (extremeAngleTreeDescendants (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) hk f hb d.translatedField)))
        treeTime descendantIndex n))
      (nodeAct (fun ω t => d.curve ω t) (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) hk f hb d.translatedField))) treeTime n)))
    (hReg : ∀ n, ∀ r : ℚ, 0 < r → IsRegFam ((X n).cand r))
    (hStart : ∀ n, ∀ r : ℚ, 0 < r → Measurable ((X n).y₀ r))
    (hEvent : ∀ n, ∀ r : ℚ, 0 < r → MeasurableSet[(X n).base r] ((X n).R₀ r))
    (hLaw : ∀ n, ∀ r : ℚ, 0 < r → Late.CandidateLaw (X n) r) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => WholeField.centredField d.translatedField d.coupledMean ω +
        smoothDist upperHalfPlaneOpens d.harmonic) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂d.measure, Γ' ω = fun t : ℝ≥0 => d.curve ω t := by
  have hA := late_partAInputs hCore hCoreEight
  have h47 : Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have hA2 := late_fourForceCrosscutG3LifeStatement hCore
  have hA2' := late_threeForceCrosscutEightStatement hCoreEight
  have hFH := FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have hdual : 16 / (16 / k) = k := by field_simp
  have hfl' : IsFlowLineDriver (16 / (16 / k)) f.boundary f.jumps 0
      d.measure d.translatedField d.driver d.lifetime := by rwa [hdual]
  have htr : ∀ᵐ ω ∂d.measure, IsGeneratingTrace (fun t => d.driver t ω) (d.lifetime ω)
      (fun t : ℝ≥0 => d.curve ω t) := by
    filter_upwards [htrace, hLife] with ω hω hζ
    simpa only [hζ, Real.toNNReal_coe] using generatingTrace_of_loewner hω
  exact late_prop513_comap_centred_of_sched_frame hCrossLeft hCrossRight h47 hA2 hA2' hFH
    (div_pos (by norm_num) (by linarith : 0 < k))
    ((div_lt_iff₀ (by linarith : 0 < k)).2 (by linarith)) hb hbP hfl' hword
    htr
    X₀ (fun r hr => late_histExp_stageLaw X₀ r (hReg₀ r hr) (hStart₀ r hr) (hEvent₀ r hr) (hLaw₀ r hr))
    X (fun n r hr => late_histExp_stageLaw (X n) r (hReg n r hr) (hStart n r hr) (hEvent n r hr) (hLaw n r hr))
    d.coupledMean d.harmonic

end InteractingSLE.Wire
