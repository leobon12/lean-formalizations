/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompSched
import InteractingSLE.Spec.Sec5.StagedS4Inst
import InteractingSLE.Spec.Sec5.RestartGenOne
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# (SW3) for a flag candidate at every rational time after its last switch

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S4's `ae_cand_charIdent` was written for PIECES' root flags (`stageFlag`,
first angle `π/2`). A node experiment's candidates are the candidates of the node flags `nodeFlag s` (first angle
`flagAngle (nodeFlag s 0) = ±π/2`). Here PROVE-STAGED-S3's `ae_s3_charIdent` is instantiated at the flag schedule
`mkSchedF fl ℓ t q` for arbitrary flags `fl`:

* `rootFieldT θ h = qField + θχ`, the coupling field of the angle-`θ` flow line of `qField` (at `θ = π/2` REP2's
  `rootField`); **`exists_rootCouplingT`**: at `θ = flagAngle b` the field-determined stage driver realises an
  optional hull coupling with `rootFieldT θ h` (at `−π/2` by reflection, `Prop59Sched.isFlowLineDriver_stageDriver`);
* `glueMeasure_rootFieldT`: the glued space does not depend on the first angle (it is S4's `candMu`);
* the flag candidate objects `candWF`, `candEgF`, `candTsF`, `candAngF`, `candSigmaF`;
* **`ae_candF_charIdent`**: (SW3) at the end `q` of piece `ℓ` of `mkSchedF fl ℓ t q` for the restarted word of the
  flag candidate, all hypotheses of DEPTH and S3 discharged.

R48: the only named input is `h44 : Theorem12ParamCond44Statement` (R74); nothing uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedCand StagedDepth StagedS3
open Prop59Pieces Prop59NodeTree StagedRepLater StagedS4
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.StripSysField (counterflowData counterflowJumps)
open Sec7.Lemma71C (capClock)
open CrossCond.Staged (cumT)

/-! ### The root coupling at a flag angle -/

section Coupling

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The coupling field of the angle-`θ` flow line of `qField`**: `qField + θχ` (at `θ = π/2` REP2's `rootField`). -/
def rootFieldT (κ x₀ θ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : DistOn upperHalfPlaneOpens :=
  Exist.flowField 0 (θ * chiC κ) (qField x₀ κ h ω)

omit mΩ [IsProbabilityMeasure P] in
theorem rootFieldT_pi_div_two : rootFieldT κ x₀ (π / 2) h = rootField (κ := κ) (x₀ := x₀) h := rfl

omit mΩ [IsProbabilityMeasure P] in
theorem cfFieldT_rootFieldT (θ : ℝ) (ω : Ω) : cfFieldT κ θ (rootFieldT κ x₀ θ h ω) = qField x₀ κ h ω := by
  rw [cfFieldT, rootFieldT, flowField_zero_flowField_zero, neg_add_cancel, flowField_zero_zero]

omit [IsProbabilityMeasure P] in
theorem measurable_rootFieldT (hhm : Measurable h) (θ : ℝ) : Measurable (rootFieldT κ x₀ θ h) :=
  (Exist.measurable_flowField 0 _).comp ((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm)

include h44 hκ4 in
/-- **The root flow line at a flag angle as an optional hull coupling**: the field-determined stage driver of
`qField` at `θ = flagAngle b` drives a coupling with `qField + θχ` for the angle-`θ` flow word (at `−π/2` the
reflection of the `π/2` statement for the reflected word). -/
theorem exists_rootCouplingT (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}) (fb : Bool) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
      (VL : Fin (flowLineNL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) →
        ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) →
        ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsOptionalHullCoupling κ (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle fb))
        (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle fb))
        P 𝓕 W' VL VR B ζ' (rootFieldT κ x₀ (flagAngle fb) h) := by
  set c := sourceWord (x₀ := x₀) hκ hb
  have hθ : flagAngle fb = -(π / 2) ∨ flagAngle fb = π / 2 := by
    cases fb
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hqm : Measurable (qField x₀ κ h) :=
    (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hEm : Measurable fun ω => Prop513Schedule.stageDriver h44 hκ hκ4 (flagAngle fb) (c, qField x₀ κ h ω) :=
    (Prop513Schedule.measurable_stageDriver h44 hκ hκ4 _).comp (measurable_const.prodMk hqm)
  obtain ⟨-, h', 𝓕, VL, VR, B, htr, hC⟩ := Prop59Sched.isFlowLineDriver_stageDriver h44 hκ hκ4 hθ
    (sourceWord_extreme hκ hb) (sourceWord_gff hκ hb hG) hEm (Eventually.of_forall fun _ => rfl)
  have e : h' = rootFieldT κ x₀ (flagAngle fb) h :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  rw [e] at hC
  exact ⟨𝓕, _, VL, VR, B, _, hC⟩

include hκ4 in
/-- **The admissibility of the counterflow at a flag angle** (`CfThetaBounds` does not depend on the angle). -/
theorem cfThetaBounds_flagAngle (fb : Bool) :
    CfThetaBounds κ (flagAngle fb)
      (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle fb))
      (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle fb))
      (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
      (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) :=
  RestartGen.cfThetaBounds_angle hκ (cfThetaBounds_of_cond44 hκ hκ4
    (Theorem15.isOrderedForceWord_flowLine _ _ 0) (cond44_upper hκ (sourceWord_extreme hκ hb))) _

end Coupling

/-! ### The flag candidate's objects -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

omit [StandardBorelSpace Ω] in
/-- **The glued space does not depend on the first angle**: it is S4's `candMu`. -/
theorem glueMeasure_rootFieldT (hhm : Measurable h) (θ : ℝ) :
    glueMeasure P (candK x₀ (κ := κ) P h W ζ) (fun ω => cfFieldT κ θ (rootFieldT κ x₀ θ h ω))
      ((measurable_cfFieldT κ θ).comp (measurable_rootFieldT hhm θ)) = candMu x₀ (κ := κ) P h W ζ hhm := by
  have e : (fun ω => cfFieldT κ θ (rootFieldT κ x₀ θ h ω)) =
      fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω) := by
    funext ω
    rw [cfFieldT_rootFieldT, ← rootFieldT_pi_div_two, cfFieldT_rootFieldT]
  unfold candMu
  congr 1

/-- **The flag candidate's driver process**: the continued code driver of `qField` along `t` with the flags `fl`. -/
def candWF (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun r ω => qDrvF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) fl ℓ t ω r

/-- The switch own times of the flag candidate (`τs (j + 1) = oTime (t j)`). -/
def candTsF (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℕ → ℝ := startT (fun i => (schedD (candSchedF fl ℓ t) i : ℝ))

/-- The angles of the flag candidate's pieces. -/
def candAngF (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℕ → ℝ := schedAngle (scheduleList (candSchedF fl ℓ t))

/-- **DEPTH's conditioning σ-algebra for the flag schedule `mkSchedF fl ℓ t q`** (first angle `flagAngle (fl 0)`). -/
@[instance_reducible]
def candSigmaF (us : ℂ → ℝ) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (q : ℚ) (s : ℝ≥0) :
    MeasurableSpace (Ω × HistorySpace 0 0) :=
  germSigma (fun p : Ω × HistorySpace 0 0 =>
      recHull (mkSchedF fl ℓ t q) ℓ (pastMap κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps
        (scheduleSpec (mkSchedF fl ℓ t q))
        (Prop59Sched.schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (mkSchedF fl ℓ t q) (qField x₀ κ h))
        (ℓ + 1) p.1) ∪ cfHullQ s p.2)
    (fun p : Ω × HistorySpace 0 0 =>
      cenTT κ (flagAngle (fl 0)) (fun z => us z + flagAngle (fl 0) * chiC κ)
        (cfFieldT κ (flagAngle (fl 0)) (rootFieldT κ x₀ (flagAngle (fl 0)) h p.1))) ⊔
  ((inferInstance : MeasurableSpace (PastData (ℓ + 1))).prod (stopSigma s)).comap
    (fun p : Ω × HistorySpace 0 0 => (pastMap κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps
      (scheduleSpec (mkSchedF fl ℓ t q))
      (Prop59Sched.schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (mkSchedF fl ℓ t q) (qField x₀ κ h))
      (ℓ + 1) p.1, p.2))

/-- The good glued samples of the flag candidate's driver. -/
def candEgF (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  glueGood (candMu x₀ (κ := κ) P h W ζ hhm) s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)

include hκ4 in
/-- **(SW3) for the flag candidate `(ℓ, t)` at every rational time `q` after its last switch**, on S4's glued space:
almost surely on the alive event, with `q` before the first contact and the restarted chart-avoidance event at
`r_q = σ(q) − S₀`, the conditional characteristic value of the coupling field `qField + θ₀χ` (`θ₀ = flagAngle (fl 0)`)
given DEPTH's σ-algebra for `mkSchedF fl ℓ t q` is the chart formula of the flag candidate's restarted word. -/
theorem ae_candF_charIdent (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) {s : ℝ≥0} (hs : 0 < s)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      p ∈ s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) →
      (q : ℝ) ∈ gPre s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p →
      Sec7.Lemma71D.IsChartAvoid
        (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r p)
        (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) p)
        (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) p) φ
        ((capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
            (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p) (q : ℝ)).toNNReal -
          s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) p) →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootFieldT κ x₀ (flagAngle (fl 0)) h p'.1 φ : ℂ)) | candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t q s] p =
        Complex.exp (Complex.I * ((Sec7.Lemma71D.chartMean κ
            (imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn
              (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle (fl 0)))
              (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ)
            (imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn
              (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle (fl 0)))
              (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ)
            (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
              (lastO ℓ t : ℝ) r p)
            (fun i r => s3VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
              (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) i r p)
            (fun i r => s3VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
              (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) i r p)
            (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
              (lastO ℓ t : ℝ) p)
            (2 * Real.pi * chiC κ + (candAngF fl ℓ t ℓ - candAngF fl ℓ t 0) * chiC κ) (chiC κ) φ
            ((capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
                (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p) (q : ℝ)).toNNReal -
              s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
                (lastO ℓ t : ℝ) p) : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar
            (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
              (lastO ℓ t : ℝ) r p)
            (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
              (lastO ℓ t : ℝ) p) φ
            ((capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
                (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p) (q : ℝ)).toNNReal -
              s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
                (lastO ℓ t : ℝ) p) : ℝ) : ℂ)) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set θ₀ := flagAngle (fl 0) with hθ₀
  have hhm : Measurable h := hG.1
  obtain ⟨𝓕, W', VL, VR, B, ζ', hC⟩ := exists_rootCouplingT h44 hκ hκ4 hb (P := P) hhm hG (fl 0)
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) =
      P.map (qField x₀ κ h) ⊗ₘ candK x₀ (κ := κ) P h W ζ :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfFieldT κ θ₀ (rootFieldT κ x₀ θ₀ h ω)) = P.map (qField x₀ κ h) := by
    congr 1
    funext ω
    exact cfFieldT_rootFieldT θ₀ ω
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hθb := cfThetaBounds_flagAngle (x₀ := x₀) hκ hκ4 hb (fl 0)
  have hu₀ := isBoundedHarmonicExtension_flowWord_add hκ c.isPiecewiseConstantBoundaryData θ₀ hus
  have hcs : ∀ ω, centredField (qField x₀ κ h) us ω =
      centredField (rootFieldT κ x₀ θ₀ h) (fun z => us z + θ₀ * chiC κ) ω := fun ω =>
    (centredField_flowField_zero (qField x₀ κ h) hus.1 (θ₀ * chiC κ) ω).symm
  have hlt' : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  have hu₀s : ∀ z, us z + θ₀ * chiC κ = us z + schedAngle (scheduleList (mkSchedF fl ℓ t q)) 0 * chiC κ := by
    intro z; rw [schedAngle_mkSchedF_zero hv hq]
  set bd : ℝ → ℝ := fun x => forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ₀)
    (flowLineRhoR κ c.fn c.jumps 0 θ₀) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) x +
      -(θ₀ * chiC κ) with hbd
  obtain ⟨u', hu'⟩ : ∃ u' : ℂ → ℝ, IsBoundedHarmonicExtension
      (cfWordData κ bd (forceJumpFinset (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)))
      (cfWordJumps κ bd (forceJumpFinset (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))) u' := by
    obtain ⟨u', hu'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
      (flowLineRhoL (16 / κ) (counterflowData κ bd)
        (counterflowJumps (forceJumpFinset (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))) 0 0)
      (flowLineRhoR (16 / κ) (counterflowData κ bd)
        (counterflowJumps (forceJumpFinset (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))) 0 0)
      (flowLineXL (counterflowData κ bd)
        (counterflowJumps (forceJumpFinset (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))) 0)
      (flowLineXR (counterflowData κ bd)
        (counterflowJumps (forceJumpFinset (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))) 0)
    refine ⟨u', ?_⟩
    simp only [cfWordData, cfWordJumps, coe_forceJumpFinset]
    exact hu'
  have hτs : ∀ j : Fin ℓ, startT (fun i => (schedD (mkSchedF fl ℓ t q) i : ℝ)) ((j : ℕ) + 1) =
      candTsF fl ℓ t ((j : ℕ) + 1) := by
    intro j
    rw [candTsF, candSchedF, startT_schedD_mkSchedF hv hq j.2, startT_schedD_mkSchedF hv hlt' j.2]
  have hτsτ : ∀ j : Fin ℓ, 0 ≤ candTsF fl ℓ t ((j : ℕ) + 1) ∧ candTsF fl ℓ t ((j : ℕ) + 1) ≤ (lastO ℓ t : ℝ) := by
    intro j
    rw [candTsF, candSchedF, startT_schedD_mkSchedF hv hlt' j.2]
    exact ⟨by exact_mod_cast (oTime_pos hv _).le, by exact_mod_cast oTime_le_lastO hv _⟩
  have hτq : (lastO ℓ t : ℝ) ≤ ((cumT (schedD (mkSchedF fl ℓ t q)) ℓ : ℝ≥0) : ℝ) := by
    rw [coe_cumT_schedD_mkSchedF hv hq]; exact_mod_cast hq.le
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  have H := ae_s3_charIdent h44 hκ hκ4 hC hθb hcfc hlaw hk hu₀ hF.2.1 hF.2.2.2 hcs c (sourceWord_extreme hκ hb)
    hh hus (mkSchedF fl ℓ t q) hu₀s
    (Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSchedF fl ℓ t q))
    (Prop59Sched.schedDrivers_regular h44 hκ hκ4 c (mkSchedF fl ℓ t q) (qField x₀ κ h))
    (schedL_mkSchedF hv hq).ge hs hu' hτs hτsτ hτq φ
  rw [joinProc_mkSchedF_eq_qDrvF h44 hκ hκ4 c (qField x₀ κ h) fl hv hq, coe_cumT_schedD_mkSchedF hv hq,
    schedAngle_mkSchedF hv hq hlt', glueMeasure_rootFieldT x₀ P h W ζ hhm θ₀] at H
  exact H

end Cand

end InteractingSLE.Sec5.CrossCond.StagedNComp
