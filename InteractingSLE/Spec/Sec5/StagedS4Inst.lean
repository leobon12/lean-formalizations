/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Sched
import InteractingSLE.Spec.Sec5.StagedS3Ident
import InteractingSLE.Spec.Sec5.StagedS3Wire

/-!
# (SW3) for PROVE-PROP59-PIECES' candidate at every rational time after its last switch

Packet PROVE-STAGED-S4 (§5.1 of `planning/handoffs/PROVE-STAGED-S3.md`). In PIECES' root setting (Figure 5.1 strip
field `h`, counterflow `(W, ζ)`), the coupling field is `rootField = qField + (π/2)χ` with the root flow line
(`StagedRepLater.exists_rootCoupling`), the staged field is `qField` with the canonical code drivers, and the glued
space is `candMu` (the root coupling glued with the counterflow history through `condDistrib`). For an admissible list
`t` of depth `ℓ` and every rational `q` after its last switch, PROVE-STAGED-S3's `ae_s3_charIdent` is instantiated at
the schedule `mkSched ℓ t q`; every glued object is then the object of the **candidate's own driver** `candW ℓ t`
(`joinProc_mkSched_eq_qDrv`), the angles are the candidate's (`schedAngle_mkSched`), the first angle is `π/2`
(`hu₀s`), and only the conditioning σ-algebra `candSigma … q` depends on `q`.

* **`ae_cand_charIdent`**: (SW3) at the end `q` of piece `ℓ` of `mkSched ℓ t q`, for the restarted word of the
  candidate (`s3W`, `s3VL`, `s3VR`, `s3Chart` of `candW ℓ t`), with all of DEPTH's and S3's hypotheses discharged.

R48: the only named input is `h44 : Theorem12ParamCond44Statement` (R74); nothing uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedCand StagedDepth StagedS3
open Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.StripSysField (counterflowData counterflowJumps)
open Sec7.Lemma71C (capClock)
open CrossCond.Staged (cumT)

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-- **The candidate's driver process**: the continued code driver of `qField` along the list `t`. -/
def candW (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun r ω => qDrv h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) ℓ t ω r

/-- The conditional law of the counterflow history given the chart-`Q` field. -/
def candK : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0) :=
  condDistrib (Cond44Ref.cfHistory W ζ) (qField x₀ κ h) P

instance : IsMarkovKernel (candK x₀ (κ := κ) P h W ζ) := by
  unfold candK; infer_instance

/-- **The glued space of the root coupling** (the root flow line's field glued with the counterflow history). -/
def candMu (hhm : Measurable h) : Measure (Ω × HistorySpace 0 0) :=
  glueMeasure P (candK x₀ (κ := κ) P h W ζ) (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω))
    ((measurable_cfFieldT κ (π / 2)).comp (measurable_rootField hhm))

instance (hhm : Measurable h) : IsProbabilityMeasure (candMu x₀ (κ := κ) P h W ζ hhm) := by
  unfold candMu; infer_instance

/-- The switch own times of the candidate (`τs (j + 1) = oTime (t j)`). -/
def candTs (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℕ → ℝ := startT (fun i => (schedD (candSched ℓ t) i : ℝ))

/-- The angles of the candidate's pieces. -/
def candAng (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : ℕ → ℝ := schedAngle (scheduleList (candSched ℓ t))

/-- **DEPTH's conditioning σ-algebra for the schedule `mkSched ℓ t q`** (the past of the staged path through the end
`q` of piece `ℓ` and the counterflow history stopped at `s`, with the germ of the centred field on the union). -/
@[instance_reducible]
def candSigma (us : ℂ → ℝ) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (q : ℚ) (s : ℝ≥0) : MeasurableSpace (Ω × HistorySpace 0 0) :=
  germSigma (fun p : Ω × HistorySpace 0 0 =>
      recHull (mkSched ℓ t q) ℓ (pastMap κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps
        (scheduleSpec (mkSched ℓ t q))
        (Prop59Sched.schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (mkSched ℓ t q) (qField x₀ κ h))
        (ℓ + 1) p.1) ∪ cfHullQ s p.2)
    (fun p : Ω × HistorySpace 0 0 =>
      cenTT κ (π / 2) (fun z => us z + π / 2 * chiC κ) (cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h p.1))) ⊔
  ((inferInstance : MeasurableSpace (PastData (ℓ + 1))).prod (stopSigma s)).comap
    (fun p : Ω × HistorySpace 0 0 => (pastMap κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps
      (scheduleSpec (mkSched ℓ t q))
      (Prop59Sched.schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (mkSched ℓ t q) (qField x₀ κ h))
      (ℓ + 1) p.1, p.2))

/-- The good glued samples of the candidate's driver. -/
def candEg (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  glueGood (candMu x₀ (κ := κ) P h W ζ hhm) s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)

include hκ4 in
/-- **(SW3) for PIECES' candidate `(ℓ, t)` at every rational time `q` after its last switch**, on the glued space of
the root coupling: almost surely on the alive event (last switch before the first contact), with `q` before the first
contact and the restarted chart-avoidance event at `r_q = σ(q) − S₀`, the conditional characteristic value of the
root field given DEPTH's σ-algebra for `mkSched ℓ t q` is the chart formula of the candidate's restarted word. -/
theorem ae_cand_charIdent (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) {s : ℝ≥0} (hs : 0 < s)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      p ∈ s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) →
      (q : ℝ) ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p →
      Sec7.Lemma71D.IsChartAvoid
        (fun r => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r p)
        (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p)
        (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) p) φ
        ((capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p) (q : ℝ)).toNNReal -
          s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) p) →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) | candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s] p =
        Complex.exp (Complex.I * ((Sec7.Lemma71D.chartMean κ
            (imgStageRhoL κ (π / 2) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn
              (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
            (imgStageRhoR κ (π / 2) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn
              (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
            (fun r => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) r p)
            (fun i r => s3VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) i r p)
            (fun i r => s3VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) i r p)
            (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) p)
            (2 * Real.pi * chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * chiC κ) (chiC κ) φ
            ((capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p) (q : ℝ)).toNNReal -
              s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
                (lastO ℓ t : ℝ) p) : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar
            (fun r => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) r p)
            (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) p) φ
            ((capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p) (q : ℝ)).toNNReal -
              s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
                (lastO ℓ t : ℝ) p) : ℝ) : ℂ)) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hhm : Measurable h := hG.1
  obtain ⟨_, 𝓕, VL, VR, B, hC⟩ := exists_rootCoupling h44 hκ hκ4 hb (P := P) hhm hG
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) =
      P.map (qField x₀ κ h) ⊗ₘ candK x₀ (κ := κ) P h W ζ :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω)) = P.map (qField x₀ κ h) := by
    congr 1
    funext ω
    rw [cfFieldT_pi_div_two]
    exact cfField_rootField ω
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hθb := cfThetaBounds_of_cond44 hκ hκ4 hF h44'
  have hu₀ := isBoundedHarmonicExtension_flowWord_add hκ c.isPiecewiseConstantBoundaryData (π / 2) hus
  have hcs : ∀ ω, centredField (qField x₀ κ h) us ω =
      centredField (rootField (κ := κ) (x₀ := x₀) h) (fun z => us z + π / 2 * chiC κ) ω := fun ω =>
    (centredField_rootField h hus.1 ω).symm
  have hlt' : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  have hu₀s : ∀ z, us z + π / 2 * chiC κ = us z + schedAngle (scheduleList (mkSched ℓ t q)) 0 * chiC κ := by
    intro z; rw [schedAngle_mkSched_zero hv hq]
  -- the bounded harmonic extension of the counterflow word
  set bd : ℝ → ℝ := fun x => forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2))
    (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) x +
      -(π / 2 * chiC κ) with hbd
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
  have hτs : ∀ j : Fin ℓ, startT (fun i => (schedD (mkSched ℓ t q) i : ℝ)) ((j : ℕ) + 1) =
      candTs ℓ t ((j : ℕ) + 1) := by
    intro j
    rw [candTs, candSched, startT_schedD_mkSched hv hq j.2, startT_schedD_mkSched hv hlt' j.2]
  have hτsτ : ∀ j : Fin ℓ, 0 ≤ candTs ℓ t ((j : ℕ) + 1) ∧ candTs ℓ t ((j : ℕ) + 1) ≤ (lastO ℓ t : ℝ) := by
    intro j
    rw [candTs, candSched, startT_schedD_mkSched hv hlt' j.2]
    exact ⟨by exact_mod_cast (oTime_pos hv _).le, by exact_mod_cast oTime_le_lastO hv _⟩
  have hτq : (lastO ℓ t : ℝ) ≤ ((cumT (schedD (mkSched ℓ t q)) ℓ : ℝ≥0) : ℝ) := by
    rw [coe_cumT_schedD_mkSched hv hq]; exact_mod_cast hq.le
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  have H := ae_s3_charIdent h44 hκ hκ4 hC hθb hcfc hlaw hk hu₀ hF.2.1 hF.2.2.2 hcs c (sourceWord_extreme hκ hb)
    hh hus (mkSched ℓ t q) hu₀s
    (Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSched ℓ t q))
    (Prop59Sched.schedDrivers_regular h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h))
    (schedL_mkSched hv hq).ge hs hu' hτs hτsτ hτq φ
  rw [joinProc_mkSched_eq_qDrv h44 hκ hκ4 c (qField x₀ κ h) hv hq, coe_cumT_schedD_mkSched hv hq,
    schedAngle_mkSched hv hq hlt'] at H
  exact H

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
