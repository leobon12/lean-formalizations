/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContReg
import InteractingSLE.Spec.Supplement.GW2aStepBW1
import InteractingSLE.Spec.Supplement.GW2aStepConn

/-!
# Lemma GW2a, containment (R51 form): the induction with BW1 for regular drivers, and the assembly

Packet PROVE-GW2A-STEP. PROVE-GW2AC's induction (`GW2aCont.ae_hasStatePair_succ_of_launch`,
`GW2aCont.ae_hasStatePair_succ`, `GW2aCont.gw2aContainmentRegStatement_of_inputs`) consumes its BW1 input only for
staged drivers that are measurable, regular at every sample and continuous on the stopped interval at the
conditioning sample. Its named input `GW2aCont.BW1PrefixPairStatement` asks for more (arbitrary flow-line drivers,
read at the lifetime; see `GW2aStepBW1`). The same proofs run with the corrected `BW1PrefixPairRegStatement`
(`ae_hasStatePair_succ_of_launch_reg`, `ae_hasStatePair_succ_reg`, `gw2aContainmentRegStatement_of_inputs_reg`; the
only changes are the BW1 call, which now passes the staged driver, its measurability and regularity, and the piece's
regularity at the conditioning sample).

**`gw2aContainmentRegStatement_of_bw1`**: Lemma GW2a's containment in its R51 form from GB6's hull identity, Theorems
1.2–1.3 (universes `u` and `0`), the source-form Proposition BW1 (`BW1.BW1Statement`), the fixed-time input
(`FlowFixedTimeInteriorStatement`), BR6's forcing in the conditional world (`GW2aConnectorForcingStatement`) and
Corollary BR4a (`BR4a.BR4aStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aStep

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti GW2aCont

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **GW1's inductive step at a launch, with BW1 for regular drivers** (the proof of
`GW2aCont.ae_hasStatePair_succ_of_launch`, with `BW1PrefixPairRegStatement`). -/
theorem ae_hasStatePair_succ_of_launch_reg (hG : GB6PrefixPairStatement.{u})
    (hBW1 : BW1PrefixPairRegStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {spec : ExplSpec}
    (hθs : ∀ (k : ℕ) (θ : ℝ) (t : ℝ≥0∞), spec.2.2[k]? = some (Sum.inl (θ, t)) →
      θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (j : ℕ) :
    ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' spec E j ω₀ → ∀ (θ : ℝ) (t : ℝ≥0∞),
      spec.2.2[j]? = some (Sum.inl (θ, t)) →
      (∀ D, ExplState.run κ b jumps spec D j = ExplState.run κ b jumps spec (fun i => E i ω₀) j →
        ExplState.run κ b jumps spec D (j + 1) =
          ExplState.launch (ExplState.run κ b jumps spec (fun i => E i ω₀) j) j (D j) θ t) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), HasStatePair κ b jumps P h W' spec E (j + 1) ω := by
  have hle := hS.2.1
  have hEm := hS.1
  filter_upwards [hS.2.2.2 j, hR.ae_pieceRegular,
    ae_ae_run_eq runMeasStatement hb spec (fun i _ => hEm i) (fun i _ => hreg i) (k := j) (P := P),
    ae_ae_condExpKernel_succ_eq hle j,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hle j) hR.ae_pieceRegular,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hle j) (Sec7.Aux122Disint.ae_ae_condExpKernel (hle (j + 1))
      (ae_isClosed_counterflowCompletedRange hT13 hκ hcf hζ'))]
    with ω₀ hst hreg0 hrun hK hregν hclν hD θ t hj hlaunch
  have hinstr : instrTime spec j = t := by simp only [instrTime, hj]
  have hl0 : (ExplState.run κ b jumps spec (fun i => E i ω₀) (j + 1)).2.2.2.1 j =
      some ((ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1, θ) := by
    rw [hlaunch _ rfl, launches_launch, Function.update_self]
  have hterm := not_isTerminal_of_launch hl0
  obtain ⟨b', J', hj', hb', htrj, hfl⟩ := hst _ _ hl0
  obtain ⟨Wk, ζk, hWk, hζk, hidk⟩ := hD hterm hj' htrj
  have hθ := hθs j θ t hj
  have hconf := isConformal_runChart spec (fun i => E i ω₀) j fun i _ => hreg0 i
  have hext : GW1P.HasProperBdryExt (ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1 :=
    hasProperBdryExt_of_launch hreg0 hl0
  have hhj := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  have hgm : Measurable (lastRec κ b jumps spec E j) := measurable_lastRec hle j
  have hlaunchω : ∀ ω, ExplState.run κ b jumps spec (fun i => E i ω) j =
      ExplState.run κ b jumps spec (fun i => E i ω₀) j →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j =
        some ((ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1, θ) := fun ω hω => by
    rw [hlaunch _ hω, launches_launch, Function.update_self]
  have hgν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      lastRec κ b jumps spec E j ω = recOf t ((fun s => (E j ω).1 s), (E j ω).2) := by
    filter_upwards [hrun] with ω hω
    rw [lastRec_of_launch spec E j (by rw [hlaunchω ω hω]; exact Option.some_ne_none _), hinstr]
  have hBν := hBW1 κ hκ hκ4 θ hθ b' J' hb' _ hj' hhj Wk ζk hWk hζk (E j) (hEm j) (hreg j) hfl t _ hgm hgν
  have hGν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), t ≠ ⊤ → t < (E j ω).2 →
      IsInteriorStop (fun s => (E j ω).1 s) t →
      ∀ h₂ : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω', IsChartTransport (Chart.id.loewner (stopDrv t ((fun s => (E j ω).1 s), (E j ω).2))
          (stopTime t ((fun s => (E j ω).1 s), (E j ω).2))) 1 0 (QuantumZipper.chiC κ) (hj' ω') (h₂ ω')) →
        ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
          IsCenteredCounterflowDriver κ (condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
            (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω) h₂ W₂ ζ₂ ∧
          (∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
            (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ζ₂ ω' = ⊤) ∧
          ∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
            (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
            ((Chart.id.loewner (stopDrv t ((fun s => (E j ω).1 s), (E j ω).2))
              (stopTime t ((fun s => (E j ω).1 s), (E j ω).2))).trans infinitySourceChart).tipAt
                (fun s => W₂ s ω') r z →
              z ∈ counterflowCompletedRange (fun s => Wk s ω') := by
    by_cases ht : t = ⊤
    · exact Eventually.of_forall fun ω h => absurd ht h
    · filter_upwards [hG κ hκ hκ4 θ hθ b' J' hb' _ hj' hhj Wk ζk hWk hζk _ _ hfl t ht _ hgm hgν] with ω hω _
      exact hω
  have hzero := ae_condExpKernel_succ_eq_of_stop_zero hle hreg hK hgν (ae_lifetime_eq_zero_or_ne hfl)
  have hlift := KernelTower.ae_ae_condExpKernel_of_ae (P := condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
    (m := MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) hgm.comap_le
    ((GW2Later.ae_counterflow_regular hT13 hκ hWk hζk).and hidk)
  filter_upwards [hrun, hK, hregν, hclν, hBν, hGν, hzero, hlift] with ω hω hKω hregω hclω hBω hGω hzω hliftω
  intro hlive h'' htr''
  have hs1 := hlaunch _ hω
  have hrω := hregω j _ _ (hlaunchω ω hω)
  rw [hinstr] at hrω
  rw [hs1] at hlive htr'' ⊢
  by_cases htop : min t (E j ω).2 = ⊤
  · exact absurd (isTerminal_launch_of_top _ _ _ _ _ htop) hlive
  rw [chart_launch_eq _ _ _ _ _ htop] at htr'' ⊢
  by_cases h0 : min t (E j ω).2 = 0
  · -- a zero stop: the chart and the conditional law do not change
    have he0 : (E j ω).1 0 = 0 := (hreg j ω).2.1
    rw [stopDrv_of_stop_zero he0 h0, stopTime_of_stop_zero h0] at htr'' ⊢
    have htr0 : ∀ ω', IsChartTransport (ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1 1 0
        (QuantumZipper.chiC κ) (h ω') (h'' ω') := fun ω' =>
      (isChartTransport_loewner_zero_iff (W := fun _ => 0) continuous_const rfl).1 (htr'' ω')
    obtain ⟨W₂, ζ₂, hW₂, hζ₂, hid₂⟩ := hD hterm h'' htr0
    rw [hzω h0]
    refine ⟨W₂, ζ₂, hW₂, hζ₂, hid₂.mono fun ω' hω' r z hz => hω' r z ?_⟩
    exact (tipAt_loewner_zero_iff (W := fun _ => 0) continuous_const rfl).1 hz
  -- a finite positive stop: GB6 or BW1 in the conditional world
  have hpos : 0 < min t (E j ω).2 := pos_iff_ne_zero.2 h0
  have hU : Continuous (stopDrv t (E j ω)) := hrω.continuous_stoppedReal.1
  have hU0 : stopDrv t (E j ω) 0 = 0 := hrω.continuous_stoppedReal.2
  have hT : 0 ≤ stopTime t (E j ω) := NNReal.coe_nonneg _
  have hc₂ := Chart.isConformal_id.loewner hU hU0 hT
  have hℓ₂ := hc₂.continuousOn_lift_inv (Chart.continuousOn_lift_loewner hU hU0 hT)
  have htr₂ : ∀ ω', IsChartTransport (Chart.id.loewner (stopDrv t (E j ω)) (stopTime t (E j ω))) 1 0
      (QuantumZipper.chiC κ) (hj' ω') (h'' ω') := fun ω' =>
    IsChartTransport.of_trans hconf.1 hc₂ hconf.2 hℓ₂ (htrj ω') (by rw [← Chart.loewner_eq_trans]; exact htr'' ω')
  have hpair : ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ (condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
        (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω) h'' W₂ ζ₂ ∧
      (∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
        (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ζ₂ ω' = ⊤) ∧
      ∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
        (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
        ((Chart.id.loewner (stopDrv t (E j ω)) (stopTime t (E j ω))).trans infinitySourceChart).tipAt
          (fun s => W₂ s ω') r z → z ∈ counterflowCompletedRange (fun s => Wk s ω') := by
    by_cases hgb : t < (E j ω).2 ∧ IsInteriorStop (fun s => (E j ω).1 s) t
    · exact hGω (ne_top_of_lt hgb.1) hgb.1 hgb.2 h'' htr₂
    · refine hBω hpos htop ?_ hrω h'' htr₂
      by_cases hlt : t < (E j ω).2
      · right
        rw [min_eq_left hlt.le]
        exact fun hi => hgb ⟨hlt, hi⟩
      · exact Or.inl (not_lt.1 hlt)
  obtain ⟨W₂, ζ₂, hW₂, hζ₂, hid₂⟩ := hpair
  rw [hKω] at hW₂ hζ₂ hid₂ hliftω
  refine ⟨W₂, ζ₂, hW₂, hζ₂, ?_⟩
  have hB : HasBdryLimits (fwdMapInv (stopDrv t (E j ω)) (stopTime t (E j ω))) := hrω.hasBdryLimits htop
  filter_upwards [hid₂, GW2Later.ae_counterflow_regular hT13 hκ hW₂ hζ₂, hliftω, hclω]
    with ω' hid₂ω hreg₂ω hlω' hclω'
  obtain ⟨γ₂, hγ₂, hW₂c, hW₂0, -⟩ := hreg₂ω
  obtain ⟨⟨γk, hγk, hWkc, hWk0, htrk⟩, hidkω⟩ := hlω'
  intro r z hz
  exact mem_of_tipAt_loewner_trans hext hU hU0 hT hB hγk hWkc hWk0 htrk hclω' hidkω hγ₂ hW₂c hW₂0 hid₂ω r z hz


/-- **GW1's inductive step for a boundary-continued program from the root `0`** (module docstring). Named inputs: GB6
(`GW2Later.GB6PrefixPairStatement`), BW1 for regular drivers (`BW1PrefixPairRegStatement`), GW2a's connector step
(`GW2aConnectorStepStatement`), Theorem 1.3. -/
theorem ae_hasStatePair_succ_reg (hG : GB6PrefixPairStatement.{u}) (hBW1 : BW1PrefixPairRegStatement.{u})
    (hCon : GW2aConnectorStepStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {p : List Instr} (hp : IsBoundaryContinuedProgram p) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E) (hR : StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (j : ℕ) :
    ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E j ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E j) ω₀),
        HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E (j + 1) ω := by
  have hle := hS.2.1
  have hEm := hS.1
  have hθs : ∀ (k : ℕ) (θ : ℝ) (t : ℝ≥0∞), (⟨0, false, p⟩ : ExplSpec).2.2[k]? = some (Sum.inl (θ, t)) →
      θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := fun _ _ _ hk => angle_mem_Icc_of_getElem hp hk
  filter_upwards [ae_hasStatePair_succ_of_launch_reg hG hBW1 hT13 hκ hκ4 hb hcf hζ' hθs hS hR hreg j,
    hCon κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' p hp E hS hR hreg j,
    ae_ae_run_eq runMeasStatement hb ⟨0, false, p⟩ (fun i _ => hEm i) (fun i _ => hreg i) (k := j) (P := P),
    ae_ae_condExpKernel_succ_eq hle j] with ω₀ hL hC hrun hK hD
  rcases run_succ_cases (κ := κ) (b := b) (jumps := jumps) ⟨0, false, p⟩
      (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) j) j
    with hkeep | hdead | ⟨θ, t, hj, hl⟩ | ⟨s', hs', hmove⟩
  · -- the state is kept: the record is the empty record, the conditional law is the current one
    have hc : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E j) ω₀),
        lastRec κ b jumps ⟨0, false, p⟩ E j ω = readRec (fun _ => 0, 0, false) := by
      filter_upwards [hrun] with ω hω
      refine lastRec_of_noLaunch _ E j ?_
      rw [hkeep _ hω]
      exact launches_run_of_le (κ := κ) (b := b) (jumps := jumps) _ _ le_rfl
    filter_upwards [hrun, hK, ae_condExpKernel_comap_eq_self (measurable_lastRec hle j) hc] with ω hω h1 h2
    intro hlive h' htr
    rw [hkeep _ hω] at hlive htr ⊢
    rw [← h1, h2]
    exact hD hlive h' htr
  · -- the history dies
    filter_upwards [hrun] with ω hω hlive
    rw [hdead _ hω] at hlive
    exact absurd (isTerminal_setDead _) hlive
  · -- a launch
    exact hL hD θ t hj hl
  · -- a connector
    have hne : (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) (j + 1)).2.1 ≠
        (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) j).2.1 := by
      rw [hmove _ rfl]
      exact hs'
    filter_upwards [hC hD hne] with ω hω using hω.2

/-- **Lemma GW2a, containment, under ruling R51**, with BW1 for regular drivers (`BW1PrefixPairRegStatement`) in
place of the landed `BW1PrefixPairStatement` (the proof of `GW2aCont.gw2aContainmentRegStatement_of_inputs`). -/
theorem gw2aContainmentRegStatement_of_inputs_reg (hG : GB6PrefixPairStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hBW1 : BW1PrefixPairRegStatement.{u})
    (hCon : GW2aConnectorStepStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) : GW2aContainmentRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR p hp
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hbc : IsBoundaryContinuedProgram (⟨0, false, p⟩ : ExplSpec).2.2 := hp
  have hS := hE ⟨0, false, p⟩ hbc
  have hRs := hR ⟨0, false, p⟩ hbc
  -- the regularized history
  set E' := StagedReg.regHist ⟨0, false, p⟩ (E ⟨0, false, p⟩) with hE'
  have hS' : IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E' := StagedReg.isStagedHistory_regHist hb hS hRs
  have hR' : StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E' := WalkLaw.stagedPiecesRegular_regHist hRs
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hmain := ae_physSet_subset_of_steps hGB6 hGW0 hT13 hκ hκ4 hb hcf hζ' hp hS' hR' hreg'
    (fun j => ae_hasStatePair_succ_reg hG hBW1 hCon hT13 hκ hκ4 hb hh hcf hζ' hp hS' hR' hreg' j)
    (fun k => ae_arc_subset hCon hκ hκ4 hb hh hcf hζ' hp hS' hR' hreg' k)
  filter_upwards [hmain, StagedReg.ae_run_regHist hRs] with ω h1 h2
  rwa [← StagedReg.physSet_eq_of_run_eq (h2 _)]

/-- **Lemma GW2a, containment, under ruling R51, from GB6's hull identity**: as
`gw2aContainmentRegStatement_of_inputs_reg`, with GB6's two forms derived from `Supp8.GB6.GB6HullDetStatement` and
Theorems 1.2–1.3 (`BRLeaf.gb6PrefixPairStatement_of_hullDet`, `Wire.gb6RestartStatement_of_hullDet_now`). -/
theorem gw2aContainmentRegStatement_of_hullDet_reg (hD : Supp8.GB6.GB6HullDetStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBW1 : BW1PrefixPairRegStatement.{u}) (hCon : GW2aConnectorStepStatement.{u}) :
    GW2aContainmentRegStatement.{u} :=
  gw2aContainmentRegStatement_of_inputs_reg (BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀)
    (Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD) hBW1 hCon h13 h13₀


/-- **Lemma GW2a's containment (R51 form) from the source-level inputs**: GB6's hull identity, Theorems 1.2–1.3,
the source-form Proposition BW1, the fixed-time input, BR6's forcing in the conditional world and Corollary BR4a. -/
theorem gw2aContainmentRegStatement_of_bw1 (hD : Supp8.GB6.GB6HullDetStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBW1 : BW1.BW1Statement.{u}) (hFix : FlowFixedTimeInteriorStatement.{u})
    (hForce : GW2aConnectorForcingStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u}) :
    GW2aContainmentRegStatement.{u} :=
  gw2aContainmentRegStatement_of_hullDet_reg hD h12 h13 h12₀ h13₀ (bw1PrefixPairRegStatement_of_bw1 hBW1 hFix)
    (gw2aConnectorStepStatement_of_forcing hForce hBR4a h13)

end GW2aStep

end Theorem14

end InteractingSLE
