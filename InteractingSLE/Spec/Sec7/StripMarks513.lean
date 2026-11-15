/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LateReference
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Sec7.StripMarksSource

/-!
# Proposition 5.13 for the strip system's own counterflow

Packet PROVE-STRIPMARKS. The Lemma 7.25 reference of `StripMarksSource` needs Proposition 5.13's measurable version of
the counterflow (`h513`) for the strip system's own centred counterflow (Lemma 7.25's proof, p. 413: "Construct the
non-boundary centered counterflow …"; Proposition 5.13, the non-boundary determination of the counterflow by the field).
`Wire.late_reference513` takes it from a separately supplied flow-line driver `hRefFlow`, a piecewise-constant recorded
word `hRefPiecewise` and the Figure 5.1 word identity `hRefWord` of that word. For the strip system these become:

* the flow-line driver and its piecewise-constant word: **proved** — the word is the explicit counterflow word
  `counterflowData κ b` of the strip word `b` (`Theorem14.GW2Cone.isFlowLineDriver_counterflowData`), and its field is
  the chosen counterflow field of `PocketWordIn.counterflowObjects` (`IsChartTransport.unique`);
* the infinite lifetime and the Loewner trace: **proved** from the strip system;
* the Figure 5.1 identity: a deterministic identity of the strip word, `counterflowData κ b = stripCounterflowData …`
    off a
  finite set (`hword`, the strip heights of Aux. lemma 130, p. 408);
* the canonical schedules' root/node experiments and their fixed-candidate killed laws (R78): unchanged.

* **`stripCounterflow_isFlowLineDriver`**: the flow-line driver of the chosen counterflow field;
* **`h513_of_stripSystem`**: `h513` of `StripMarksSource` from the frame, `hword`, and the experiments.

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

universe u v

namespace InteractingSLE.Sec7.StripMarks

open WholeField PocketWordIn StripSysField Wire
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract
  Sec5.Prop513Asm Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit
  Sec5.Prop59Nodes Sec5.Prop513Bridge
open Restart Exist Exist.Staged Exist.StagedLaw

/-- The numerical frame of Figure 5.1 for the strip system (`z₀ = x₀ + i`, lower heights `−a, b`, upper heights
`−a', b'`): data only. -/
structure Frame where
  x₀ : ℝ
  a : ℝ
  b : ℝ
  a' : ℝ
  b' : ℝ

/-- The frame in the form of `Wire.Late.Frame` (its recorded word is not used by `Wire.Late.schedules`). -/
def Frame.toLate (f : Frame) : Wire.Late.Frame := ⟨f.x₀, f.a, f.b, f.a', f.b', fun _ => 0, ∅⟩

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The chosen counterflow field of the strip system is the field of the angle-0 flow line of the explicit
counterflow word** (FD11.1, FD12.1–FD12.2): `Theorem14.GW2Cone.isFlowLineDriver_counterflowData`, with its transported
field identified with `(counterflowObjects hS.counterflow).field` (uniqueness of the transport through the conformal
infinity-source chart, and the translation by `0` with constant `0` is the identity). -/
theorem stripCounterflow_isFlowLineDriver (hS : StripSys.IsStripSystem κ b J P h W ζ E) :
    IsFlowLineDriver (16 / κ) (counterflowData κ b) (counterflowJumps J) 0 P
      (counterflowObjects hS.counterflow).field W ζ := by
  obtain ⟨h', htr', hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hS.kappa_pos hS.boundaryData
    hS.gff hS.counterflow
  obtain ⟨hT, hTr, -, -⟩ := counterflowObjects_spec hS.counterflow
  have e : h' = (counterflowObjects hS.counterflow).field := by
    funext ω
    rw [IsChartTransport.unique Chart.isConformal_infinitySourceChart (htr' ω) (hT ω)]
    exact (Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (hTr ω)).symm
  rw [← e]
  exact hfl

/-- **Proposition 5.13 for the strip system's counterflow** (`h513` of `StripMarksSource`): the measurable version of
the counterflow for the centred chosen counterflow field, from the Figure 5.1 frame of the strip word (`hb`, `hword`),
the canonical schedules' root and node experiments and their fixed-candidate killed laws. The flow-line driver, the
piecewise-constant word, the lifetime and the trace are derived from the strip system. -/
theorem h513_of_stripSystem
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement)
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hQ : FrameQ.QScheduleFirstHitStatement.{u})
    {k : ℝ} (hk : 4 < k) (hS : StripSys.IsStripSystem (16 / k) b J P h W ζ E)
    {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (f : Frame) (hb : IsFig51Bounds (16 / k) f.a f.b f.a' f.b')
    (hword : ∀ x ∉ counterflowJumps J ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      counterflowData (16 / k) b x = stripCounterflowData (16 / k) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') x)
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp (16 / k) P Pa
      (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) hk f.toLate hb
          (counterflowObjects hS.counterflow).field))) treeTime))
      (fun _ => univ))
    (hReg₀ : ∀ r : ℚ, 0 < r → IsRegFam (X₀.cand r))
    (hStart₀ : ∀ r : ℚ, 0 < r → Measurable (X₀.y₀ r))
    (hEvent₀ : ∀ r : ℚ, 0 < r → MeasurableSet[X₀.base r] (X₀.R₀ r))
    (hLaw₀ : ∀ r : ℚ, 0 < r → Late.CandidateLaw X₀ r)
    (X : ∀ n, HistExp (16 / k) P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) hk f.toLate hb
          (counterflowObjects hS.counterflow).field)))
        treeTime descendantIndex n))
      (nodeAct (fun ω t => η ω t) (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement hCore hCoreEight) hk f.toLate hb
          (counterflowObjects hS.counterflow).field))) treeTime n)))
    (hReg : ∀ n, ∀ r : ℚ, 0 < r → IsRegFam ((X n).cand r))
    (hStart : ∀ n, ∀ r : ℚ, 0 < r → Measurable ((X n).y₀ r))
    (hEvent : ∀ n, ∀ r : ℚ, 0 < r → MeasurableSet[(X n).base r] ((X n).R₀ r))
    (hLaw : ∀ n, ∀ r : ℚ, 0 < r → Late.CandidateLaw (X n) r) (u : ℂ → ℝ) :
    let d := counterflowObjects hS.counterflow
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField d.field d.mean ω + smoothDist upperHalfPlaneOpens u) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
  intro d
  have hA := late_partAInputs hCore hCoreEight
  have h47 : Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have hA2 := late_fourForceCrosscutG3LifeStatement hCore
  have hA2' := late_threeForceCrosscutEightStatement hCoreEight
  have hFH := FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t : ℝ≥0 => η ω t) := by
    filter_upwards [hηtr, hS.lifetime] with ω hω hζ
    rw [hζ]
    exact hω
  exact late_prop513_comap_centred_of_sched_frame hCrossLeft hCrossRight h47 hA2 hA2' hFH
    (div_pos (by norm_num) (by linarith : 0 < k))
    ((div_lt_iff₀ (by linarith : 0 < k)).2 (by linarith)) hb
    (isPiecewiseConstant_counterflowData (16 / k) hS.boundaryData)
    (stripCounterflow_isFlowLineDriver hS) hword htr
    X₀ (fun r hr => late_histExp_stageLaw X₀ r (hReg₀ r hr) (hStart₀ r hr) (hEvent₀ r hr) (hLaw₀ r hr))
    X (fun n r hr => late_histExp_stageLaw (X n) r (hReg n r hr) (hStart n r hr) (hEvent n r hr) (hLaw n r hr))
    d.mean u

end InteractingSLE.Sec7.StripMarks
