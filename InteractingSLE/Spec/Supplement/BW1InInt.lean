/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LifeSafe
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Supplement.BW1InIntGauss

/-!
# Proposition BW1: the relative field is integrable on every record event

Packet PROVE-BW1-INPUTS. The third clause of the named input `BW1Life.BW1RelSafeSLStatement` (the relative field is
integrable under the conditioned joint law of the record and the relative variable) is PROVED here, with no input:

* conditionally on the retained past, BW1's post-piece field is the GFF of the stop word (`BW1Life.ae_bwField_gff`, the
  staged law), so its counterflow-frame reading `bwRelField` is the GFF of the relative word `bwRelWord (bwRec ω₀)`;
* the heights of the relative words lie in one finite set for every record (`BW1Life.retStopWord_bounded`), so by the
  maximum principle for piecewise-constant data the conditional means of a pairing are bounded uniformly, and the
  centred pairing has the fixed law `N(0, v_φ)` (`BW1In.lintegral_enorm_apply_le_of_isGFF`);
* disintegrating over the regular conditional laws (the record event is an event of the retained past) bounds
  `E[‖Hc φ‖; record event]` by that uniform constant.

Consequences: **`BW1RelSafeLawStatement`** (the named input reduced to K2's (S) and (L)),
**`bw1RelSafeSLStatement_of_law`** and **`bw1RelSafeStatement_of_law`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1In

open Exist Exist.StagedLaw Exist.Staged Restart Supp8.Q3Stop BW1Life

/-- **The relative words have uniformly bounded data**: there is `M ≥ 0` with `|(bwRelWord κ θ c₀ r).fn y| ≤ M` for
every record `r` and every `y` (the heights of returned stop words lie in one finite set). -/
theorem exists_abs_fn_bwRelWord_le (κ θ : ℝ) (c₀ : BoundaryWord) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (r : RecData) (y : ℝ), |(bwRelWord κ θ c₀ r).fn y| ≤ M := by
  obtain ⟨Hs, hHs, _, hN⟩ := retStopWord_bounded κ θ (Sec7.StripSysField.cfOffset κ -
    2 * Real.pi * Sec7.StripSysField.cfCoeff κ) (-Sec7.StripSysField.cfCoeff κ) (BoundaryWord.shiftW 0 c₀)
  obtain ⟨M, hM⟩ := (hHs.image fun x => |x|).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun r y => ?_⟩
  have hmem := (hN r).1 ((bwRelWord κ θ c₀ r).index y)
  exact (hM ⟨_, hmem, rfl⟩).trans (le_max_left _ _)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The relative field is integrable on every record event of the threshold event.** For a measurable record event
`F = bwRec⁻¹ B` almost surely inside BW1's threshold event, `E[‖Hc φ‖; F] < ∞`: conditionally on the retained past
the relative field is the GFF of a relative word with data bounded uniformly in the record. -/
theorem integrableOn_bwRelField (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {r : Bool}
    {B : Set RecData} (hB : MeasurableSet B)
    (hBF : ∀ᵐ ω ∂P, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ B → ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) (φ : TestOn upperHalfPlaneOpens) :
    IntegrableOn (fun ω => bwRelField κ b jumps (bwSpec gw2 θ t rest) h E ω φ)
      (bwRec κ b jumps (bwSpec gw2 θ t rest) E ⁻¹' B) P := by
  obtain ⟨hκ, -, hb, hh, -, -, -, hS⟩ := hset
  set spec := bwSpec gw2 θ t rest with hspec
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have h𝒢 : pastSigma κ b jumps spec E' 1 ≤ mΩ := (measurable_pastMap_one hb hEm' hreg').comap_le
  have hrec𝒢 : Measurable[pastSigma κ b jumps spec E' 1] (bwRec κ b jumps spec E) :=
    measurable_pastSigma_pastMap_one_last
  set F := bwRec κ b jumps spec E ⁻¹' B with hFdef
  have hF𝒢 : MeasurableSet[pastSigma κ b jumps spec E' 1] F := hrec𝒢 hB
  have hF : MeasurableSet F := h𝒢 _ hF𝒢
  have hHc : Measurable (bwRelField κ b jumps spec h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh.1 hEm' hreg')
  have hXm : Measurable fun ω => bwRelField κ b jumps spec h E ω φ :=
    (LQGMetric.measurable_distOn_apply φ).comp hHc
  obtain ⟨M, hM0, hM⟩ := exists_abs_fn_bwRelWord_le κ θ c₀
  set C : ℝ≥0∞ := ENNReal.ofReal (M * ∫ z, |φ z|) +
    ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal)
    with hC
  have hCtop : C < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, lintegral_enorm_gaussianReal_lt_top _⟩
  have hgff := (ae_bwField_gff (θ := θ) (t := t) (rest := rest) hκ hb hh rfl hEm' hreg' (stageOK_regHist_zero hS)
    hc₀J hc₀).2
  set f : Ω → ℝ≥0∞ := F.indicator fun ω => ‖bwRelField κ b jumps spec h E ω φ‖ₑ with hfdef
  have hfm : Measurable f := hXm.enorm.indicator hF
  have hbound : ∀ᵐ ω₀ ∂P, ∫⁻ ω, f ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀) ≤ C := by
    filter_upwards [KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hF𝒢, hgff, hBF] with ω₀ hc hg hf
    by_cases hω₀ : ω₀ ∈ F
    · have hfin : min t (E' 0 ω₀).2 ≠ ⊤ := by
        rw [StagedReg.regHist_snd]
        exact finStop_of_mem_bwEvent (hf hω₀)
      have hG := GW1Laws.isGFFWithBoundaryData_cfField_cfWordOf κ (isSorted_stopWord κ _) (hg hfin)
      calc ∫⁻ ω, f ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀)
          ≤ ∫⁻ ω, ‖bwRelField κ b jumps spec h E ω φ‖ₑ ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀) :=
            lintegral_mono (indicator_le_self _ _)
        _ ≤ C := lintegral_enorm_apply_le_of_isGFF
            (GW1Laws.cfWordOf κ (bwWord κ b jumps spec θ c₀ E' ω₀)).isPiecewiseConstantBoundaryData hG hM0
            (fun y _ => hM (bwRec κ b jumps spec E ω₀) y) φ
    · have h0 : condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀ F = 0 := hc.2 hω₀
      rw [hfdef, lintegral_indicator hF, setLIntegral_measure_zero _ _ h0]
      exact zero_le
  refine ⟨hXm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [← lintegral_indicator hF]
  change ∫⁻ ω, f ω ∂P < ⊤
  rw [← KernelTower.lintegral_lintegral_condExpKernel h𝒢 hfm]
  calc ∫⁻ ω₀, ∫⁻ ω, f ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀) ∂P ≤ ∫⁻ _, C ∂P :=
        lintegral_mono_ae hbound
    _ = C := by rw [lintegral_const, measure_univ, mul_one]
    _ < ⊤ := hCtop

/-- **The integrability clause of BW1's relative safe law, PROVED**: under the joint law of the record and the
relative variable conditioned on the record event of type `w`, every pairing of the relative field is integrable. -/
theorem integrable_canonFld_bw (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {r : Bool}
    {TS : Set RecData} (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hRm : ∀ s, Measurable (R s)) (hVm : Measurable V) (w : WordType)
    (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun y => canonFld y φ)
      ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
        Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) R V ω))[|
          typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) := by
  have hset' := hset
  obtain ⟨-, -, hb, hh, -, -, -, hS⟩ := hset'
  set spec := bwSpec gw2 θ t rest with hspec
  have hEm' : ∀ j, Measurable (StagedReg.regHist spec E j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist spec E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable (bwRec κ b jumps spec E) := measurable_pastMap_one_last hb hEm' hreg'
  have hHc : Measurable (bwRelField κ b jumps spec h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh.1 hEm' hreg')
  have hΦ : Measurable fun ω => (bwRec κ b jumps spec E ω,
      Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps spec h E) R V ω) :=
    hrec.prodMk (Supp8.GB6.RelDrv.measurable_relVar hHc hRm hVm)
  set B : Set RecData := TS ∩ {r | wordType (16 / κ) (bwRelWord κ θ c₀ r) = w} with hBdef
  have hB : MeasurableSet B :=
    hTS.inter ((measurable_wordType _).comp (measurable_bwRelWord κ θ c₀) (measurableSet_singleton w))
  have hSm : MeasurableSet (typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS) :=
    measurableSet_typeEvent (measurable_bwRelWord κ θ c₀) hTS
  have hBF : ∀ᵐ ω ∂P, bwRec κ b jumps spec E ω ∈ B → ω ∈ bwEvent κ b jumps spec E r := by
    filter_upwards [hFTS] with ω hω hωB
    exact hω.2 hωB.1
  have hon := integrableOn_bwRelField hset hB hBF hc₀J hc₀ φ
  have hφm : Measurable fun y : CanonSpace => canonFld y φ :=
    (LQGMetric.measurable_distOn_apply φ).comp measurable_canonFld
  have hi : IntegrableOn (fun y => canonFld y φ) (typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS)
      (P.map fun ω => (bwRec κ b jumps spec E ω, Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps spec h E) R V ω)) := by
    unfold IntegrableOn
    rw [Measure.restrict_map hΦ hSm]
    exact (integrable_map_measure hφm.aestronglyMeasurable hΦ.aemeasurable).2 hon
  by_cases h0 : (P.map fun ω => (bwRec κ b jumps spec E ω,
      Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps spec h E) R V ω)) (typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS) = 0
  · rw [cond_eq_zero_of_meas_eq_zero h0]
    exact integrable_zero_measure
  · unfold ProbabilityTheory.cond
    exact hi.smul_measure (ENNReal.inv_ne_top.2 h0)

/-- **Named input (the marked union law): BW1's relative safe law, K2's (S) and (L)** — `BW1RelSafeSLStatement`
without its integrability clause, which is proved (`integrable_canonFld_bw`). -/
def BW1RelSafeLawStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ (r : Bool) (TS : Set RecData), MeasurableSet TS →
    (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) →
    ∀ c₀ : BoundaryWord, c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ →
      ∀ (m : ℕ) (w : WordType),
        Restart.DomainMarkov.K2.HasSafeLaw (16 / κ) (typedRhoL w) (typedRhoR w)
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ canonStp canonDrv
          (Sec7.PocketTraversal.geomLW canonDrv fun y => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1))
          (Sec7.PocketTraversal.geomRW canonDrv fun y => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)) canonFld ∧
        Restart.DomainMarkov.K2.HasSafeMembers
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ canonStp canonDrv canonFld

/-- **`BW1RelSafeSLStatement` from K2's (S) and (L)** (the integrability clause is `integrable_canonFld_bw`). -/
theorem bw1RelSafeSLStatement_of_law (hL : BW1RelSafeLawStatement.{u}) : BW1RelSafeSLStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver m w
  obtain ⟨hlaw, hmem⟩ := hL κ b jumps P h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver m w
  exact ⟨hlaw, hmem, fun φ => integrable_canonFld_bw hset hTS hFTS hc₀J hc₀ (hver.1 m) (hver.2.2.2.2.1 m) w φ⟩

/-- **`BW1RelSafeStatement` from K2's (S) and (L)** (threshold clause: `ae_canonStp_le_thr_bw`; integrability:
`integrable_canonFld_bw`). -/
theorem bw1RelSafeStatement_of_law (hT13₀ : Exist.Theorem13Statement.{0}) (hL : BW1RelSafeLawStatement.{u}) :
    BW1RelSafeStatement.{u} :=
  bw1RelSafeStatement_of_SL hT13₀ (bw1RelSafeSLStatement_of_law hL)

end InteractingSLE.Theorem14.BW1In
