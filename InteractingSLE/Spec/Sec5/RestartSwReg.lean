/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartSwMain
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueDet

/-!
# The switched-wall restart law without pathwise regularity of the staged history

Packet PROVE-SWITCHED. `RestartSwMain.ae_isFirstHitQ_switched_of_reg` asks the two-angle staged history to be regular
(`IsRegularDriver`) at every sample; `RestartGen.SwitchedWallFirstHitStatement` does not. Ruling R51: pathwise
regularity of a later piece cannot be read off its conditional laws on `P` (it is not a measurable event). Here the
history is replaced by its regularization (`Theorem14.StagedReg.regHist`):

* **`isStagedHistory_regHist_twoAngle`**: the regularized history of a two-angle staged history is again a staged
  history of the same program. Only the first piece's regularity is needed on `P` (the first piece is a frozen flow line
  of `h`, so it is almost surely continuous: `ae_firstPiece_regular`); the continuation's conditional flow-line law
  transfers under the conditional law, where it is almost surely continuous (`stageOK_regHist`). No
  `StagedPiecesRegular`.
* **`ae_wall_eq_of_regHist`**: a wall version of the history and one of its regularization agree almost surely — on the
  measurable event "agree at rational times", whose conditional probability given the first record is one (under the
  conditional law the continuation is continuous, so the two concatenated drivers agree and their traces coincide).
* **`switchedWallFirstHitStatement_of_input`**: `RestartGen.SwitchedWallFirstHitStatement` from Lemma 4.7 at every
  relative angle in `[−π/2, π/2]`, the §4.2 reference and Lemma 4.7's conditional law at the switch
  (`CounterflowGivenPrefixStatement`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.RestartSw

open Prop411Q (IsFirstHitQ)
open Sec7.Lemma71I (realPath)
open Sec7.StripSideHeightProb (catPath)
open Exist Exist.Staged Exist.StagedLaw Sec7.StripDet
open Theorem14.StagedReg (regHist regularize isRegularDriver_regHist measurable_regHist regHist_snd
  regularize_eq_of_le regularize_eq_of_lt regularize_zero canonDrv_regularize run_eq_of_canonDrv_eq_on_launch
  ae_condExpKernel_eq_of_ae_eq isFlowLineDriver_congr_ae)

section Reg

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {Es : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The first piece is almost surely continuous from `0` before its lifetime** (it is the frozen flow-line driver of
`h` at the angle `θ₀`). -/
theorem ae_firstPiece_regular (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J)
    (hE : IsStagedHistory κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es) :
    ∀ᵐ ω ∂P, (Es 0 ω).1 0 = 0 ∧ ContinuousOn (Es 0 ω).1 {s | (s : ℝ≥0∞) < (Es 0 ω).2} := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := Sec7.StripWall.isFlowLineDriver_stage_zero hκ hb hh hE
  filter_upwards [hC.1.2.2.2.2] with ω hp
  exact ⟨hp.1, hp.2.2.2.1⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] mΩ in
/-- **The regularized history runs through the same state after the first instruction** when the first piece is
continuous from `0` and lives forever. -/
theorem run_one_regHist {ω : Ω} (hz : (Es 0 ω).2 = ⊤) (hr0 : (Es 0 ω).1 0 = 0)
    (hrc : ContinuousOn (Es 0 ω).1 {s | (s : ℝ≥0∞) < (Es 0 ω).2}) :
    ExplState.run κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
        (fun j => regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es j ω) 1 =
      ExplState.run κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => Es j ω) 1 := by
  classical
  set D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j =>
    if j = 0 then regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 0 ω else Es j ω with hD'
  have h1 : ExplState.run κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (fun j => regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es j ω) 1 =
      ExplState.run κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) D' 1 := by
    refine CrossCond.StagedGlue.run_congr_of_lt_length _ fun j hj _ => ?_
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [hD', ↓reduceIte]
  have h2 := run_eq_of_canonDrv_eq_on_launch (κ := κ) (b := b) (jumps := J) (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
    (D := fun j => Es j ω) (D' := D') fun k c θ' _ => by
      by_cases hk : k = 0
      · subst hk
        simp only [hD', ↓reduceIte]
        exact canonDrv_regularize hr0 (hrc.mono fun s hs => by
          rw [hz]; exact ENNReal.coe_lt_top)
      · simp only [hD', hk, ↓reduceIte]
  rw [h1, h2 1]

/-- **A stage clause of the regularized history** from that of the history, when the two run through the same state
before the instruction almost surely and the regularized retained past is measurable. -/
theorem stageOK_regHist {spec : ExplSpec} (hE : IsStagedHistory κ b J P h spec Es) {k : ℕ}
    (hrun : ∀ᵐ ω ∂P, ExplState.run κ b J spec (fun j => regHist spec Es j ω) k =
      ExplState.run κ b J spec (fun j => Es j ω) k)
    (hpm' : Measurable (pastMap κ b J spec (regHist spec Es) k)) :
    StageOK κ b J P h spec (regHist spec Es) k := by
  have hpm : Measurable (pastMap κ b J spec Es k) := Measurable.of_comap_le (hE.2.1 k)
  have hpast : pastMap κ b J spec (regHist spec Es) k =ᵐ[P] pastMap κ b J spec Es k := by
    filter_upwards [hrun] with ω hω
    unfold pastMap
    rw [hω]
  filter_upwards [hE.2.2.2 k, ae_condExpKernel_eq_of_ae_eq hpm' hpm hpast, hrun] with ω₀ h4 hK hr c θ' hl
  rw [launches_run_succ_of_run_eq spec hr] at hl
  obtain ⟨b', J', h', hb', htr, hfl⟩ := h4 c θ' hl
  refine ⟨b', J', h', hb', htr, ?_⟩
  rw [pastSigma_eq_comap, hK]
  rw [pastSigma_eq_comap] at hfl
  have hζ : (fun ω => (regHist spec Es k ω).2) = fun ω => (Es k ω).2 := funext fun ω => regHist_snd k ω
  rw [hζ]
  refine isFlowLineDriver_congr_ae hfl
    (fun t => (measurable_pi_apply t).comp (measurable_fst.comp (measurable_regHist hE.1 k))) ?_
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  filter_upwards [hC.1.2.2.2.2] with ω hp
  exact ⟨regularize_zero _ hp.1, fun t ht => regularize_eq_of_lt _ hp.1 hp.2.2.2.1 ht⟩

/-- The two-angle program launches nothing from its third instruction on. -/
theorem stageOK_twoAngle_of_two_le {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : 2 ≤ k) : StageOK κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) E k := by
  refine Eventually.of_forall fun ω₀ c θ' hl => ?_
  have h1 := (eq_launch_of_launches _ _ hl).1
  have hnone : (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ).2.2[k]? = none := by
    simp only [Sec7.StripSys.twoAngleSpec, Sec7.StripSys.twoAngleProg]
    exact List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)
  rw [hnone] at h1
  exact absurd h1 (by simp)

/-- **The regularized history of a two-angle staged history is a staged history of the same program**, regular at every
sample. Only the first piece's regularity is used on `P`. -/
theorem isStagedHistory_regHist_twoAngle (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hE : IsStagedHistory κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    IsStagedHistory κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es) := by
  have hB := runMeasStatement.{u}
  have hm' : ∀ k, Measurable (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es k) := measurable_regHist hE.1
  have hpm' : ∀ k, Measurable (pastMap κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es) k) := fun k =>
    measurable_pastMap hB hb _ (fun j _ => hm' j) (fun j _ ω => isRegularDriver_regHist j ω) k le_rfl
  have hz0 := Sec7.StripWall.ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0
  have hr0 := ae_firstPiece_regular hκ hb hh hE
  refine ⟨hm', fun k => (hpm' k).comap_le, fun k => Eventually.of_forall fun ω =>
    (isRegularDriver_regHist k ω).2.2.2, fun k => ?_⟩
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk
  · exact stageOK_regHist hE (Eventually.of_forall fun ω => rfl) (hpm' 0)
  · refine stageOK_regHist hE ?_ (hpm' 1)
    filter_upwards [hz0, hr0] with ω hz hr
    exact run_one_regHist hz.1 hr.1 hr.2
  · exact stageOK_twoAngle_of_two_le hk

/-- **A wall version of the history is almost surely the wall version of its regularization.** The event "the two
agree at rational times" is measurable; under the conditional law given the first record the continuation is
continuous (it is a conditional flow-line driver), so the two concatenated drivers agree, and their generating traces
coincide; the event therefore has conditional probability one, hence probability one, and the walls agree by
continuity. -/
theorem ae_wall_eq_of_regHist (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hE : IsStagedHistory κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ) (hz1 : ∀ᵐ ω ∂P, (Es 1 ω).2 = ⊤)
    {R γ : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P Es t₀ R)
    (hγ : Sec7.StripWall.IsWallVersion P (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es) t₀ γ) :
    ∀ᵐ ω ∂P, R ω = γ ω := by
  have h𝒢 : pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1 ≤ mΩ := hE.2.1 1
  have hz0 := Sec7.StripWall.ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0
  have hr0 := ae_firstPiece_regular hκ hb hh hE
  have hSm : MeasurableSet {ω | ∀ q : ℚ, R ω (q : ℝ).toNNReal = γ ω (q : ℝ).toNNReal} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun q => measurableSet_eq_fun (hR.measurable _) (hγ.measurable _)
  have hG : ∀ᵐ ω ∂P, ((Es 0 ω).2 = ⊤ ∧ (Es 0 ω).1 0 = 0 ∧
        ContinuousOn (Es 0 ω).1 {s | (s : ℝ≥0∞) < (Es 0 ω).2}) ∧ (Es 1 ω).2 = ⊤ ∧
      IsGeneratingTrace (catPath (Es 0 ω).1 t₀ (Es 1 ω).1) ⊤ (R ω) ∧
      IsGeneratingTrace (catPath (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 0 ω).1 t₀
        (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1 ω).1) ⊤ (γ ω) := by
    filter_upwards [hz0, hr0, hz1, hR.ae_trace, hγ.ae_trace] with ω h1 h2 h3 h4 h5
    exact ⟨⟨h1.1, h2⟩, h3, h4.1, h5.1⟩
  have hGK := Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hG
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1) ω₀),
      ω ∈ {ω | ∀ q : ℚ, R ω (q : ℝ).toNNReal = γ ω (q : ℝ).toNNReal} := by
    filter_upwards [hE.2.2.2 1, hz0, hGK] with ω₀ hstg hz hGω₀
    have h0 : (t₀ : ℝ≥0∞) < (Es 0 ω₀).2 := by rw [hz.1]; exact ENNReal.coe_lt_top
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1
      (launch_one_of_lt (κ := κ) (b := b) (jumps := J) (θ₀ := θ₀) (θ := θ) (D := fun j => Es j ω₀) h0)
    obtain ⟨b', J', h', -, -, hfl⟩ := hstg c θ' hcθ
    obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
    filter_upwards [hC.1.2.2.2.2, hGω₀] with ω hp hω
    obtain ⟨⟨hz0ω, h00, hc0⟩, hz1ω, hRt, hγt⟩ := hω
    have e0 : ∀ s : ℝ≥0, s ≤ t₀ → (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 0 ω).1 s = (Es 0 ω).1 s :=
      fun s hs => regularize_eq_of_le h00
        (hc0.mono fun x _ => show (x : ℝ≥0∞) < (Es 0 ω).2 by rw [hz0ω]; exact ENNReal.coe_lt_top)
        (by rw [hz0ω, min_eq_left le_top]; exact ENNReal.coe_le_coe.2 hs)
    have e1 : ∀ s : ℝ≥0, (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1 ω).1 s = (Es 1 ω).1 s := fun s =>
      regularize_eq_of_lt _ hp.1 hp.2.2.2.1 (by rw [hz1ω]; exact ENNReal.coe_lt_top)
    have hcat : catPath (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 0 ω).1 t₀
        (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1 ω).1 = catPath (Es 0 ω).1 t₀ (Es 1 ω).1 := by
      funext t
      unfold catPath
      split_ifs with ht
      · exact e0 t ht
      · rw [e0 t₀ le_rfl, e1]
    have hc0' := Sec7.StripWall.continuous_of_isRegularDriver
      (isRegularDriver_regHist (spec := Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) (E := Es) 0 ω)
      ((regHist_snd 0 ω).trans hz0ω)
    have hc1' := Sec7.StripWall.continuous_of_isRegularDriver
      (isRegularDriver_regHist (spec := Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) (E := Es) 1 ω)
      ((regHist_snd 1 ω).trans hz1ω)
    have hcc := Sec7.StripSideHeightProb.continuous_catPath (T₀ := t₀) hc0' hc1'
      (isRegularDriver_regHist (spec := Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) (E := Es) 1 ω).2.1
    have hcc0 := Sec7.StripSideHeightProb.catPath_zero (T₀ := t₀)
      (w₁ := (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1 ω).1)
      (isRegularDriver_regHist (spec := Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) (E := Es) 0 ω).2.1
    rw [← hcat] at hRt
    intro q
    rw [← LP.traceAt_eq_of_isGeneratingTrace hRt hcc.continuousOn hcc0 ENNReal.coe_lt_top,
      LP.traceAt_eq_of_isGeneratingTrace hγt hcc.continuousOn hcc0 ENNReal.coe_lt_top]
  filter_upwards [Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hSm hker] with ω hω
  have hf : (fun s : ℝ => R ω s.toNNReal) = fun s : ℝ => γ ω s.toNNReal :=
    Continuous.ext_on Rat.denseRange_cast ((hR.continuous ω).comp continuous_real_toNNReal)
      ((hγ.continuous ω).comp continuous_real_toNNReal) (by rintro _ ⟨q, rfl⟩; exact hω q)
  funext t
  have := congrFun hf (t : ℝ)
  simpa only [Real.toNNReal_coe] using this

end Reg

/-! ### The general law -/

/-- **Lemma 4.7 at every relative angle in `(−π/2, π/2]`**: the landed `Prop411Q.Lemma47QHitStatement` at `π/2`, the
interior angles from their own statement. -/
theorem lemma47QHitT_Ioc (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ ∈ Ioo (-(π / 2)) (π / 2), RestartGen.Lemma47QHitTStatement.{u} θ) :
    ∀ θ ∈ Ioc (-(π / 2)) (π / 2), RestartGen.Lemma47QHitTStatement.{u} θ := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.2 with he | hlt
  · rw [he]
    exact RestartGen.lemma47QHitTStatement_pi_div_two h47
  · exact h47T θ ⟨hθ.1, hlt⟩

/-- **`RestartGen.SwitchedWallFirstHitStatement` from the inputs** (Lemma 5.7 with `ℓ = 2`): Lemma 4.7 in the chart `Q`
(the landed `Prop411Q.Lemma47QHitStatement`, relative angle `π/2`) and at every interior relative angle
(`RestartGen.Lemma47QHitTStatement θ`, `θ ∈ (−π/2, π/2)`; the angle `−π/2` goes by reflection to `π/2`), the §4.2
reference and Lemma 4.7's conditional law at the switch (`CounterflowGivenPrefixStatement`). The two-angle staged
history is replaced by its regularization (`isStagedHistory_regHist_twoAngle`), of which the wall is again a version
(`ae_wall_eq_of_regHist`), and `ae_isFirstHitQ_switched_of_reg` applies. -/
theorem switchedWallFirstHitStatement_of_input (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ ∈ Ioo (-(π / 2)) (π / 2), RestartGen.Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hcg : CounterflowGivenPrefixStatement.{u}) :
    RestartGen.SwitchedWallFirstHitStatement.{u} := by
  intro κ b J Ω _ _ P _ h W' ζ' E hS hleft hright θ₀ θ hθ₀ hθ t₀ R hR η hη q hqt
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 < Real.pi * chiC κ := mul_pos Real.pi_pos hχ
  have hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := fun y hy hyJ => by
    have := hleft θ₀ hθ₀ y hy hyJ; linarith
  have hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ := hright θ₀ hθ₀
  have hL : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := fun y hy hyJ => by
    have := hleft θ hθ y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ := fun y hy hyJ => by
    have := hright θ hθ y hy hyJ; linarith
  have hθπ : θ ≤ θ₀ + Real.pi := by linarith [hθ.2, hθ₀.1, Real.pi_pos]
  have hθπ' : θ₀ ≤ θ + Real.pi := by linarith [hθ₀.2, hθ.1, Real.pi_pos]
  have hE := hS.staged (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
    (Sec7.StripSys.isBoundaryContinuedProgram_twoAngleProg hθ₀ hθ t₀)
  have hE' := isStagedHistory_regHist_twoAngle hκ hκ4 hb hh hE hL0 hR0
  have hreg' : ∀ j ω, IsRegularDriver (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) j ω) := fun j ω => isRegularDriver_regHist j ω
  obtain ⟨γ, hγ, -⟩ := Sec7.StripWall.exists_isWallVersion_twoAngle hκ hκ4 hb hh hE' hreg' hL0 hR0 hL hRθ hθπ hθπ'
  have hz1 : ∀ᵐ ω ∂P, (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 1 ω).2 = ⊤ :=
    (Sec7.StripWall.ae_goodPath_one hκ hκ4 hb hh hE' hreg' hL0 hR0 hL hRθ hθπ hθπ').mono fun ω hω =>
      (regHist_snd 1 ω).symm.trans (Sec7.StripWall.mem_goodPathSet.1 hω).1
  have hRγ := ae_wall_eq_of_regHist hκ hκ4 hb hh hE hL0 hR0 hz1 hR hγ
  have hR' : Sec7.StripWall.IsWallVersion P (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ))) t₀ R :=
    ⟨hR.continuous, hR.zero, hR.measurable, by
      filter_upwards [hγ.ae_trace, hRγ] with ω h1 h2
      rw [h2]
      exact h1⟩
  exact ae_isFirstHitQ_switched_of_reg (lemma47QHitT_Ioc h47 h47T) href hcg hκ hκ4 hb hh hS.counterflow hS.lifetime
    hleft hright hθ₀ hθ hE' hreg' hR' hη q hqt

end InteractingSLE.Sec5.RestartSw
