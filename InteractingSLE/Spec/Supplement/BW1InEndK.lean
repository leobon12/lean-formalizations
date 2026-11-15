/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1InEndWord
import InteractingSLE.Spec.Supplement.BW1InEndPath
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Supplement.GB6RestartProofData

/-!
# Proposition BW1, the endpoint: the protected tail under the conditional law (GB5)

Packet PROVE-BW1-INPUTS. The probabilistic half of BW1's endpoint argument (p. 614: "Consequently the whole
conditional word is admissible, and GB5 protects every finite incident image of the retained flow range"; p. 615:
"Every accessible image other than the selected `q`-end lies on the protected tail; GB5 excludes it").

**`ae_regTrace_bw`** (PROVED): let `Wr` be any measurable driver of the conditional centred counterflow of the field
read in BW1's state chart on the threshold event (`SB.IsCondCounterflowDriverOn`, the hypothesis of
`BW1Life.BW1EndpointStatement`), with infinite lifetime and continuous paths from `0` almost surely on the event. Then
almost surely on the event, `Wr` has a continuous transient generating trace on `[0, ∞)` (its regularized trace
`regTrace`), and this trace never visits the closed right tail `[jR, ∞)` when the left seed image of the record is
nondegenerate, nor the closed left tail `(−∞, jL]` when the right seed image is (`jR`, `jL` the junctions read from the
record, `Supp8.GB6.jROfRec`, `jLOfRec`).

Proof: under the regular conditional law given the retained past (of the regularized history), the transported field
is a.s. the post-piece field (`BW1Life.ae_bwField_gff`, uniqueness of chart transports), so the counterflow field is the
GFF of GB6's conditional word of the record (`bwRelWord_eq_gb6WordOfRec`); `Wr` therefore drives the flow line of that
word (`Exist.StagedLaw.isFlowLineDriver_word`), Theorem 1.3 at `16/κ` gives its trace, and GB6's tail exclusion
(`Supp8.GB6.ae_trace_ne_of_ge_word`, `ae_trace_ne_of_le_word`) applies with the word facts of `BW1InEndWord`. The
avoidance event is measurable for the regularized trace, so it passes back to `P`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1In

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The avoidance event of the regularized trace of `Wr` (measurable). -/
def bwAvoid (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (Wr : ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | TraceGood fun s => Wr s ω} ∩
    ({ω | markPosL (rdrv (bwRec κ b jumps spec E ω)) (rtime (bwRec κ b jumps spec E ω)) 0 < 0 →
        ∀ u, 0 < rightGap (jROfRec (bwRec κ b jumps spec E ω)) (regTrace (fun s => Wr s ω) u)} ∩
      {ω | 0 < markPos (rdrv (bwRec κ b jumps spec E ω)) (rtime (bwRec κ b jumps spec E ω)) 0 →
        ∀ u, 0 < leftGap (jLOfRec (bwRec κ b jumps spec E ω)) (regTrace (fun s => Wr s ω) u)})

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurableSet_bwAvoid {spec : ExplSpec} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) {Wr : ℝ≥0 → Ω → ℝ} (hWm : ∀ s, Measurable (Wr s)) :
    MeasurableSet (bwAvoid κ b jumps spec E Wr) := by
  have hEm' : ∀ j, Measurable (StagedReg.regHist spec E j) := StagedReg.measurable_regHist hEm
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist spec E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable (bwRec κ b jumps spec E) := measurable_pastMap_one_last hb hEm' hreg'
  have hmL : Measurable fun ω => markPosL (rdrv (bwRec κ b jumps spec E ω)) (rtime (bwRec κ b jumps spec E ω)) 0 :=
    measurable_markPosL_rec.comp hrec
  have hmR : Measurable fun ω => markPos (rdrv (bwRec κ b jumps spec E ω)) (rtime (bwRec κ b jumps spec E ω)) 0 :=
    measurable_markPos_rec.comp hrec
  refine (measurableSet_traceGood hWm).inter (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_setOfPred.2 ((measurableSet_setOfPred.1 (measurableSet_lt hmL measurable_const)).imp
      (measurableSet_setOfPred.1 (measurableSet_rightAvoid hWm (measurable_jROfRec.comp hrec))))
  · exact measurableSet_setOfPred.2 ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const hmR)).imp
      (measurableSet_setOfPred.1 (measurableSet_leftAvoid hWm (measurable_jLOfRec.comp hrec))))

/-- **Under the regular conditional law, a conditional counterflow driver drives the flow line of BW1's relative
word** (the transported field is a.s. the post-piece field, whose counterflow reading is the GFF of GB6's conditional
word of the record; `Exist.StagedLaw.isFlowLineDriver_word` replaces the driver's own data by the word's). -/
theorem ae_isFlowLineDriver_bwRelWord (h13 : Exist.Theorem13Statement.{u})
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) (r : Bool) {c₀ : BoundaryWord}
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {Wr : ℝ≥0 → Ω → ℝ} {ζr : Ω → ℝ≥0∞}
    (hcf : SB.IsCondCounterflowDriverOn (mΩ := mΩ) κ (pastSigma κ b jumps (bwSpec gw2 θ t rest) E 1) P
      (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r) h (bwChart κ b jumps (bwSpec gw2 θ t rest) E) Wr ζr) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
      ∃ h'' : Ω → DistOn upperHalfPlaneOpens, IsFlowLineDriver (16 / κ)
        (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω₀)).fn
        (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω₀)).jumps 0
        (condExpKernel P (pastSigma κ b jumps (bwSpec gw2 θ t rest)
          (StagedReg.regHist (bwSpec gw2 θ t rest) E) 1) ω₀) h'' Wr ζr := by
  obtain ⟨hκ, -, hb, hh, -, -, -, hS⟩ := hset
  set spec := bwSpec gw2 θ t rest with hspec
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have h𝒢 : pastSigma κ b jumps spec E' 1 ≤ mΩ := (measurable_pastMap_one hb hEm' hreg').comap_le
  have hM𝒢 : MeasurableSet[pastSigma κ b jumps spec E' 1] {ω | min t (E' 0 ω).2 ≠ ⊤} :=
    measurableSet_pastSigma_finStop (θ := θ) (rest := rest) rfl
  obtain ⟨hchart, hgff⟩ := ae_bwField_gff (θ := θ) (t := t) (rest := rest) hκ hb hh rfl hEm' hreg'
    (stageOK_regHist_zero hS) hc₀J hc₀
  filter_upwards [hcf, ae_condExpKernel_regHist_eq h13 hκ hb hh hS rfl rfl,
    ae_run_one_regHist h13 hκ hb hh hS rfl rfl, hchart, hgff,
    ae_ae_run_eq runMeasStatement hb spec (k := 1) (fun j _ => hEm' j) (fun j _ => hreg' j) (P := P),
    Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hchart, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hM𝒢]
    with ω₀ hcf₀ hK₀ hrun₀ hc₀' hg₀ hrunK hchK hmK hω₀
  have hfin : min t (E' 0 ω₀).2 ≠ ⊤ := by rw [StagedReg.regHist_snd]; exact finStop_of_mem_bwEvent hω₀
  obtain ⟨h', hh', hcd⟩ := hcf₀ hω₀
  rw [← hK₀] at hcd
  obtain ⟨hconf, -, -⟩ := hc₀' hfin
  have hch : bwChart κ b jumps spec E ω₀ =
      BW1.stateChart (ExplState.run κ b jumps spec (fun j => E' j ω₀) 1) := by
    unfold bwChart; rw [hrun₀]
  rw [hch] at hh'
  have hYe : bwField κ b jumps spec h E' =ᵐ[condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀] h' := by
    filter_upwards [hrunK, hchK, hmK hfin] with ω hr hc hm
    obtain ⟨-, -, hT⟩ := hc hm
    rw [hr] at hT
    exact hT.unique hconf (hh' ω)
  obtain ⟨b', J', h'', hb', htr', hfl'⟩ := hcd
  have hk : 0 < 16 / κ := by positivity
  have hRet := GW2JointKernel.isGFFWithBoundaryData_returnField_retWord (isSorted_stopWord κ _)
    (Real.pi * chiC κ) (chiC κ) (hg₀ hfin)
  have hh''m : Measurable h'' := (GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hfl').1
  have hG'' := isGFFWithBoundaryData_congr_ae hRet hh''m (hYe.mono fun ω hω => by
    show Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (bwField κ b jumps spec h E' ω) = h'' ω
    rw [eq_returnField_of_isChartTransport_R hκ (htr' ω), hω])
  refine ⟨h'', ?_⟩
  rw [bwRelWord_eq_gb6WordOfRec hκ θ c₀]
  exact isFlowLineDriver_word hk hG'' hb' hfl'

/-- **The protected tails under the conditional law, passed back to `P` (GB5)**: almost surely on BW1's threshold
event, a conditional counterflow driver with infinite lifetime and continuous paths from `0` is `TraceGood`, and its
regularized trace avoids the closed right tail when the record's left seed image is nondegenerate and the closed left
tail when its right seed image is. -/
theorem ae_mem_bwAvoid (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) (r : Bool) {Wr : ℝ≥0 → Ω → ℝ} {ζr : Ω → ℝ≥0∞}
    (hWm : ∀ s, Measurable (Wr s))
    (hcf : SB.IsCondCounterflowDriverOn (mΩ := mΩ) κ (pastSigma κ b jumps (bwSpec gw2 θ t rest) E 1) P
      (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r) h (bwChart κ b jumps (bwSpec gw2 θ t rest) E) Wr ζr)
    (hreg : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
      ζr ω = ⊤ ∧ Continuous (fun s => Wr s ω) ∧ Wr 0 ω = 0) :
    ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r →
      ω ∈ bwAvoid κ b jumps (bwSpec gw2 θ t rest) E Wr := by
  have hset' := hset
  obtain ⟨hκ, hκ4, hb, hh, hcfW, hζ', hθ, hS⟩ := hset'
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hκ hκ4 hb hh
    hcfW hζ'
  have hL : ∀ y, y < 0 → y ∉ c₀.jumps → c₀.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := fun y hy hyJ => by
    rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hambL y hy hyJ
  have hR : ∀ y, 0 < y → y ∉ c₀.jumps → -sleLambda κ < c₀.fn y + Real.pi / 2 * chiC κ := fun y hy hyJ => by
    rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hambR y hy hyJ
  set spec := bwSpec gw2 θ t rest with hspec
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have h𝒢 : pastSigma κ b jumps spec E' 1 ≤ mΩ := (measurable_pastMap_one hb hEm' hreg').comap_le
  set F' : Set Ω := bwEvent κ b jumps spec E' r with hF'
  have hF'm : MeasurableSet F' :=
    (isMeasState_run (κ := κ) hb spec hEm' hreg' 1).1 (Sum.inr (Sum.inr (Sum.inl (some r))))
  have hF'𝒢 : MeasurableSet[pastSigma κ b jumps spec E' 1] F' :=
    measurableSet_pastSigma_of_run runMeasStatement hb spec (fun j _ => hEm' j) (fun j _ => hreg' j) hF'm
      fun ω ω' he hω => by
        change BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E' j ω') 1) r
        rw [← he]
        exact hω
  have hFF' : ∀ᵐ ω ∂P, ω ∈ F' ↔ ω ∈ bwEvent κ b jumps spec E r := by
    filter_upwards [ae_run_one_regHist h13 hκ hb hh hS rfl rfl] with ω hrun
    change BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E' j ω) 1) r ↔
      BW1.EndsAtThresholdSide (ExplState.run κ b jumps spec (fun j => E j ω) 1) r
    rw [hrun]
  have hrec𝒢 : Measurable[pastSigma κ b jumps spec E' 1] (bwRec κ b jumps spec E) :=
    measurable_pastSigma_pastMap_one_last
  have hmL𝒢 : Measurable[pastSigma κ b jumps spec E' 1] fun ω =>
      markPosL (rdrv (bwRec κ b jumps spec E ω)) (rtime (bwRec κ b jumps spec E ω)) 0 :=
    measurable_markPosL_rec.comp hrec𝒢
  have hmR𝒢 : Measurable[pastSigma κ b jumps spec E' 1] fun ω =>
      markPos (rdrv (bwRec κ b jumps spec E ω)) (rtime (bwRec κ b jumps spec E ω)) 0 :=
    measurable_markPos_rec.comp hrec𝒢
  have hjR𝒢 : Measurable[pastSigma κ b jumps spec E' 1] fun ω => jROfRec (bwRec κ b jumps spec E ω) :=
    measurable_jROfRec.comp hrec𝒢
  have hjL𝒢 : Measurable[pastSigma κ b jumps spec E' 1] fun ω => jLOfRec (bwRec κ b jumps spec E ω) :=
    measurable_jLOfRec.comp hrec𝒢
  have key : ∀ᵐ ω₀ ∂P, ω₀ ∈ F' → ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀),
      ω ∈ bwAvoid κ b jumps spec E Wr := by
    filter_upwards [ae_isFlowLineDriver_bwRelWord h13 hset r hc₀J hc₀ hcf, hFF',
      Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hreg, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hFF',
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF'𝒢,
      Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hmL𝒢,
      Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hmR𝒢,
      Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hjR𝒢,
      Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hjL𝒢]
      with ω₀ hfl₀ hF₀ hregK hFFK hF'K hmLK hmRK hjRK hjLK hω₀'
    have hω₀ : ω₀ ∈ bwEvent κ b jumps spec E r := hF₀.1 hω₀'
    obtain ⟨h'', hfl⟩ := hfl₀ hω₀
    obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
    have hE := hC.1
    have hFν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀), ω ∈ bwEvent κ b jumps spec E r := by
      filter_upwards [hF'K hω₀', hFFK] with ω h1 h2
      exact h2.1 h1
    have hregν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀),
        ζr ω = ⊤ ∧ Continuous (fun s => Wr s ω) ∧ Wr 0 ω = 0 := by
      filter_upwards [hFν, hregK] with ω h1 h2
      exact h2 h1
    have hζν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀), ζr ω = ⊤ :=
      hregν.mono fun ω h => h.1
    have htrν := h13 (div_pos (by norm_num) hκ) (Theorem15.isOrderedForceWord_flowLine _ _ 0) hE
    have hgoodν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀),
        TraceGood (fun s => Wr s ω) ∧ IsGeneratingTrace (fun s => Wr s ω) ⊤ (regTrace fun s => Wr s ω) := by
      filter_upwards [hregν, htrν] with ω hω hω'
      obtain ⟨hζ, hc, h0⟩ := hω
      obtain ⟨-, η, hη, htr⟩ := hω'
      rw [hζ] at hη htr
      obtain ⟨hg, he⟩ := traceGood_of hc h0 hη (htr rfl)
      exact ⟨hg, he ▸ hη⟩
    have hη : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀),
        IsGeneratingTrace (fun s => Wr s ω) ⊤ (regTrace fun s => Wr s ω) := hgoodν.mono fun ω h => h.2
    have hadm := isGB6AdmData_bwRelWord hκ hκ4 hθ hL hR (bwRec κ b jumps spec E ω₀)
    have hR' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀),
        markPosL (rdrv (bwRec κ b jumps spec E ω₀)) (rtime (bwRec κ b jumps spec E ω₀)) 0 < 0 →
          ∀ (u : ℝ≥0) (y : ℝ), jROfRec (bwRec κ b jumps spec E ω₀) ≤ y → regTrace (fun s => Wr s ω) u ≠ y := by
      by_cases hm : markPosL (rdrv (bwRec κ b jumps spec E ω₀)) (rtime (bwRec κ b jumps spec E ω₀)) 0 < 0
      · have hp : 0 < jROfRec (bwRec κ b jumps spec E ω₀) := by
          unfold jROfRec; rw [← inv_neg]; exact inv_pos.2 (neg_pos.2 hm)
        exact (ae_trace_ne_of_ge_word hκ hadm hp (rightTail_bwRelWord hκ hκ4 hθ.1 c₀ hm) hE hζν hη).mono
          fun ω h _ => h
      · exact Eventually.of_forall fun ω h => absurd h hm
    have hL' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' 1) ω₀),
        0 < markPos (rdrv (bwRec κ b jumps spec E ω₀)) (rtime (bwRec κ b jumps spec E ω₀)) 0 →
          ∀ (u : ℝ≥0) (y : ℝ), y ≤ jLOfRec (bwRec κ b jumps spec E ω₀) → regTrace (fun s => Wr s ω) u ≠ y := by
      by_cases hm : 0 < markPos (rdrv (bwRec κ b jumps spec E ω₀)) (rtime (bwRec κ b jumps spec E ω₀)) 0
      · have hp : jLOfRec (bwRec κ b jumps spec E ω₀) < 0 := by
          unfold jLOfRec; exact neg_neg_of_pos (inv_pos.2 hm)
        exact (ae_trace_ne_of_le_word hκ hadm hp (leftTail_bwRelWord hκ hκ4 hθ.2 c₀ hm) hE hζν hη).mono
          fun ω h _ => h
      · exact Eventually.of_forall fun ω h => absurd h hm
    filter_upwards [hgoodν, hR', hL', hmLK, hmRK, hjRK, hjLK] with ω hg hr hl e1 e2 e3 e4
    refine ⟨hg.1, fun hm u => ?_, fun hm u => ?_⟩
    · rw [e1] at hm
      rw [e3]
      refine rightGap_pos_iff.2 fun hz => hr hm u _ hz.2 ?_
      exact Complex.ext (by simp) (by simp [hz.1])
    · rw [e2] at hm
      rw [e4]
      refine leftGap_pos_iff.2 fun hz => hl hm u _ hz.2 ?_
      exact Complex.ext (by simp) (by simp [hz.1])
  have hP := GW2Schedule.ae_of_ae_condExpKernel_on h𝒢 hF'𝒢 (measurableSet_bwAvoid hb hS.1 hWm) key
  filter_upwards [hP, hFF'] with ω h1 h2 hω
  exact h1 (h2.2 hω)

end InteractingSLE.Theorem14.BW1In
