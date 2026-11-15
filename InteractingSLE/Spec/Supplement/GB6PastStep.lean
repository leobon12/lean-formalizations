/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Past

/-!
# GW1's inductive step (`GB6PastStepStatement`) from GB6 conditioned on the piece's own prefix

Packet PROVE-T14-BR7. **`gb6PastStepStatement_of_prefix`**: `GW2Later.GB6PastStepStatement` (GW1's induction, supplement
pp. 618–620, 623) follows from `GB6PrefixPairStatement` (GB6 for one flow line, conditioned on its own marked prefix)
and Theorem 1.3.

## Proof

Fix a launch `j` and a sample `ω₀` at which the pair is available (`HasLaunchPairInt`). Let `ν` be the regular
conditional law given the retained past before `j` at `ω₀`.

1. Under `ν` the retained past is that of `ω₀` (`Aux122Disint.ae_ae_condExpKernel_eq`); in particular the first `j`
   pieces were successful and had interior switching tips under `ν` exactly when they had at `ω₀` (the records and the
   regularity of the pieces fix the stopped drivers, `isInteriorStop_congr`). Otherwise the datum at `j + 1` is vacuous.
2. Under `ν`, the field `h_j` read in the launch chart `c_j` is a GFF, the piece launched at `j` is its angle-`θ_j`
   flow line (`IsStagedHistory`), and `HasLaunchPair` gives the counterflow pair `(W_k, ζ_k)` of `h_j`. GB6 given the
   piece's prefix (`GB6PrefixPairStatement`, in the world `ν`, with the measurable version `g = last ∘ pastMap (j+1)`
   of the piece's record) gives the new pair under `condExpKernel ν (comap g)`.
3. Under `ν` the retained past before `j + 1` is `snoc (pastMap j ω₀) g`, so `condExpKernel ν (pastSigma (j+1)) =
   condExpKernel ν (comap g)` `ν`-almost surely (`KernelTower.ae_condExpKernel_comap_eq`), and the kernel of a kernel
   (`KernelTower.ae_ae_condExpKernel_condExpKernel_eq`) identifies it with `condExpKernel P (pastSigma (j+1))`.
4. The launch chart at `j + 1` is `c_j.loewner U T` for the stopped driver `U` of the piece; the field read in it is the
   field `h_j` read in the Loewner chart (`IsChartTransport.of_trans`); the new tips, read through `c_j`, lie in the
   original range (`mem_of_tipAt_loewner_trans`, with the boundary limits of `c_j` from the regularity of the earlier
   pieces and the traces of both counterflows from Theorem 1.3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Later

open CounterflowRange GW2Schedule GW2aMulti GW2Sched Exist.StagedLaw Exist.Staged

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### The retained past one launch later -/

theorem pastMap_succ_castSucc {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω)
    (i : Fin j) : pastMap κ b jumps spec E (j + 1) ω (Fin.castSucc i) = pastMap κ b jumps spec E j ω i := by
  change readRec ((ExplState.run κ b jumps spec (fun k => E k ω) (j + 1)).2.2.1 i) =
    readRec ((ExplState.run κ b jumps spec (fun k => E k ω) j).2.2.1 i)
  rw [retained_run_of_lt spec _ (Nat.lt_succ_of_lt i.2), retained_run_of_lt spec _ i.2]

/-- The retained past before `j + 1` is the retained past before `j` followed by the last record. -/
theorem pastMap_succ_eq_snoc {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) :
    pastMap κ b jumps spec E (j + 1) ω =
      Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps spec E j ω)
        (pastMap κ b jumps spec E (j + 1) ω (Fin.last j)) := by
  conv_lhs => rw [← Fin.snoc_init_self (α := fun _ => RecData) (pastMap κ b jumps spec E (j + 1) ω)]
  congr 1
  funext i
  exact pastMap_succ_castSucc spec E j ω i

/-- On the success of the first `j` pieces of a GW2 schedule, the last record before `j + 1` is the record of the
piece launched at `j`. -/
theorem pastMap_succ_last {Ω : Type*} {x : ℝ} {l : List (ℝ × ℝ≥0)} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {j : ℕ}
    (hj : j < (scheduleProgram 0 l).length) {ω : Ω} (hs : AllSucc (schedDelta 0 l) (fun i => E i ω) j) :
    pastMap κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E (j + 1) ω (Fin.last j) =
      recOf (schedDelta 0 l j) (E j ω) := by
  change readRec ((ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun k => E k ω) (j + 1)).2.2.1 j) = _
  rw [retained_run_gw2 (spec := ⟨x, true, scheduleProgram 0 l⟩) rfl (isFlowProg_scheduleProgram 0 l)
    (schedDelta_ne_top 0 l) _ hj hs]
  rfl

theorem measurable_snoc_const {j : ℕ} (a : Fin j → RecData) :
    Measurable fun y : RecData => (Fin.snoc (α := fun _ => RecData) a y : Fin (j + 1) → RecData) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_id
  · simp only [Fin.snoc_castSucc]
    exact measurable_const

theorem instrTime_sched {x : ℝ} {gw : Bool} {l : List (ℝ × ℝ≥0)} {j : ℕ} (hj : j < (scheduleProgram 0 l).length) :
    instrTime ⟨x, gw, scheduleProgram 0 l⟩ j = schedDelta 0 l j := by
  have h := isFlowProg_scheduleProgram 0 l j hj
  simp only [instrTime, h]

/-! ### Interior stops depend only on the record -/

/-- **Two drivers with the same record and continuous up to a common successful stop have the same interior-stop
status.** -/
theorem isInteriorStop_congr {Δ : ℝ≥0∞} (hΔ : Δ ≠ ⊤) {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (hs : Δ < e.2) (hs' : Δ < e'.2)
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ Δ}) (hc' : ContinuousOn e'.1 {t | (t : ℝ≥0∞) ≤ Δ})
    (h : recOf Δ e = recOf Δ e') : IsInteriorStop e.1 Δ ↔ IsInteriorStop e'.1 Δ := by
  have hd := stopDrv_eq_of_recOf_eq hΔ hs hs' hc hc' h
  have hf : (fun r : ℝ≥0 => e.1 (min (r : ℝ≥0∞) Δ).toNNReal) =
      fun r : ℝ≥0 => e'.1 (min (r : ℝ≥0∞) Δ).toNNReal := by
    funext r
    have h1 := congrFun hd (r : ℝ)
    simp only [stopDrv, retOf, Real.toNNReal_coe, min_eq_left hs.le, min_eq_left hs'.le] at h1
    exact h1
  unfold IsInteriorStop
  rw [hf]

/-! ### The counterflow is regular almost surely -/

/-- **A complete centred counterflow has, almost surely, a continuous driver from `0` and a continuous transient
generating trace** (Theorem 1.3 at `16/κ`). -/
theorem ae_counterflow_regular (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {Ω : Type u}
    [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ Q h W ζ) (hζ : ∀ᵐ ω ∂Q, ζ ω = ⊤) :
    ∀ᵐ ω ∂Q, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧ Continuous (fun t => W t ω) ∧
      W 0 ω = 0 ∧ Tendsto (fun t => ‖γ t‖) atTop atTop := by
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  filter_upwards [GW2aSingle.ae_chosenTrace hT13 hk hfl, hζ, Supp8.GB6.ae_driver_zero_continuousOn hfl]
    with ω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  exact ⟨_, hγω.1, hWc, hdω.1, hγω.2 rfl⟩

/-! ### Regular pieces along a successful run -/

/-- Along a successful GW2 run whose launched pieces are regular, each piece is regular up to its own time. -/
theorem pieceRegular_of_allSucc {Ω : Type*} {x : ℝ} {l : List (ℝ × ℝ≥0)} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {ω : Ω}
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (E k ω).1 (min (instrTime ⟨x, true, scheduleProgram 0 l⟩ k) (E k ω).2))
    {n : ℕ} (hn : n ≤ (scheduleProgram 0 l).length) (hs : AllSucc (schedDelta 0 l) (fun j => E j ω) n) :
    ∀ i < n, GW1P.PieceRegular (E i ω).1 (min (schedDelta 0 l i) (E i ω).2) := by
  intro i hi
  have hil : i < (scheduleProgram 0 l).length := lt_of_lt_of_le hi hn
  have hl := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := ⟨x, true, scheduleProgram 0 l⟩) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) (fun j => E j ω) hil).1 (hs.mono hi.le)
  have h1 := hreg i _ _ hl
  rwa [instrTime_sched hil] at h1

/-- A regular piece that succeeded is continuous up to its own time. -/
theorem continuousOn_of_pieceRegular {Δ : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : GW1P.PieceRegular e.1 (min Δ e.2))
    (hs : Δ < e.2) : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ Δ} := by
  have h1 := he.2.1
  rwa [min_eq_left hs.le] at h1

/-! ### The step -/

/-- **GW1's inductive step from GB6 conditioned on the piece's own prefix** (supplement pp. 618–620, 623; module
docstring). -/
theorem gb6PastStepStatement_of_prefix (hG : GB6PrefixPairStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) :
    GB6PastStepStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER x hx l hlθ hlt j
  have hbc := isBoundaryContinuedProgram_scheduleProgram hlθ 0
  have hS := hE ⟨x, true, scheduleProgram 0 l⟩ hbc
  have hR := hER ⟨x, true, scheduleProgram 0 l⟩ hbc
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩ with hspec
  set E' := E spec with hE'
  have hgw : spec.2.1 = true := rfl
  have hprog : IsFlowProg spec.2.2 (schedAngle l) (schedDelta 0 l) := isFlowProg_scheduleProgram 0 l
  have hΔ : ∀ i, schedDelta 0 l i ≠ ⊤ := schedDelta_ne_top 0 l
  by_cases hj : j < spec.2.2.length
  swap
  · refine Eventually.of_forall fun ω₀ _ => Eventually.of_forall fun ω _ _ c θ hl => ?_
    rw [launches_run_succ_of_length_le κ b jumps spec _ (by omega)] at hl
    exact absurd hl (by simp)
  have hlen_le : j ≤ spec.2.2.length := hj.le
  have hpm : ∀ k, Measurable[pastSigma κ b jumps spec E' k] (pastMap κ b jumps spec E' k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hpmΩ : Measurable (pastMap κ b jumps spec E' (j + 1)) := (hpm (j + 1)).mono (hS.2.1 (j + 1)) le_rfl
  have hcg : @MeasurableSpace.CountablyGenerated Ω (pastSigma κ b jumps spec E' (j + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  set g : Ω → RecData := fun ω => pastMap κ b jumps spec E' (j + 1) ω (Fin.last j) with hgdef
  have hgm : Measurable g := (measurable_pi_apply _).comp hpmΩ
  have hθj : schedAngle l j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    schedAngle_mem_Icc hlθ (by rwa [← length_scheduleProgram 0 l])
  have hallSucc : ∀ ω ω', pastMap κ b jumps spec E' j ω = pastMap κ b jumps spec E' j ω' →
      AllSucc (schedDelta 0 l) (fun i => E' i ω') j → AllSucc (schedDelta 0 l) (fun i => E' i ω) j :=
    fun ω ω' he hs' => by
      rw [allSucc_iff_flags hgw hprog hΔ E' hlen_le ω, he]
      exact (allSucc_iff_flags hgw hprog hΔ E' hlen_le ω').1 hs'
  have hstop : ∀ ω i, i < j → AllSucc (schedDelta 0 l) (fun i => E' i ω) j →
      pieceStop spec (fun i => E' i ω) i = schedDelta 0 l i := fun ω i hi hs' => by
    simp only [pieceStop]
    rw [show instrTime spec i = schedDelta 0 l i from instrTime_sched (lt_of_lt_of_le hi hlen_le)]
    exact min_eq_left (hs' i hi).le
  filter_upwards [hS.2.2.2 j, hR.ae_pieceRegular,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hS.2.1 j) (hpm j),
    Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 j) hR.ae_pieceRegular,
    KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P) (pastSigma_mono spec E' (Nat.le_succ j))
      (hS.2.1 (j + 1)) hcg,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 j) (Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 (j + 1))
      (ae_isClosed_counterflowCompletedRange hT13 hκ hcf hζ'))]
    with ω₀ hst hreg0 hpmω hregν hkk hclν hint
  -- the first `j` pieces failed at `ω₀`: nothing to prove
  by_cases hs0 : AllSucc (schedDelta 0 l) (fun i => E' i ω₀) j
  swap
  · filter_upwards [hpmω] with ω hω hs1
    exact absurd (hallSucc ω₀ ω hω.symm (hs1.mono (Nat.le_succ j))) hs0
  have hr0 := pieceRegular_of_allSucc hreg0 hlen_le hs0
  -- a switching tip before `j` was on the boundary at `ω₀`: nothing to prove
  by_cases hti0 : SwitchTipsInterior spec (fun i => E' i ω₀) j
  swap
  · filter_upwards [hpmω, hregν] with ω hω hregω hs1 hti1
    exfalso
    apply hti0
    intro i hi
    have hsω : AllSucc (schedDelta 0 l) (fun i => E' i ω) j := hs1.mono (Nat.le_succ j)
    have hrω := pieceRegular_of_allSucc hregω hlen_le hsω
    have hrec : recOf (schedDelta 0 l i) (E' i ω) = recOf (schedDelta 0 l i) (E' i ω₀) := by
      have h1 := congrFun hω ⟨i, hi⟩
      rwa [pastMap_of_allSucc hgw hprog hΔ E' hlen_le hsω,
        pastMap_of_allSucc hgw hprog hΔ E' hlen_le hs0] at h1
    have h1 := hti1 i (Nat.lt_succ_of_lt hi)
    rw [hstop ω i hi hsω] at h1
    rw [hstop ω₀ i hi hs0]
    exact (isInteriorStop_congr (hΔ i) (hsω i hi) (hs0 i hi) (continuousOn_of_pieceRegular (hrω i hi) (hsω i hi))
      (continuousOn_of_pieceRegular (hr0 i hi) (hs0 i hi)) hrec).1 h1
  -- the pair at `j`
  have hpair : HasLaunchPair κ b jumps P h W' spec E' j ω₀ := hint hs0 hti0
  have hl0 := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E' i ω₀) hj).1 hs0
  obtain ⟨b', J', hj', hb', htrj, hfl⟩ := hst _ _ hl0
  obtain ⟨Wk, ζk, hWk, hζk, hidk⟩ := hpair _ _ hl0 hj' htrj
  have hext : GW1P.HasProperBdryExt (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j) :=
    hasProperBdryExt_of_launch hreg0 hl0
  have hconf := isConformal_succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j hr0
  have hhj := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  have hgν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' j) ω₀),
      g ω = recOf (schedDelta 0 l j) (E' j ω) := by
    filter_upwards [hpmω] with ω hω
    exact pastMap_succ_last E' hj (hallSucc ω ω₀ hω hs0)
  have hGν := hG κ hκ hκ4 (schedAngle l j) hθj b' J' hb' _ hj' hhj Wk ζk hWk hζk _ _ hfl
    (schedDelta 0 l j) (hΔ j) g hgm hgν
  have hfg : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' j) ω₀),
      pastMap κ b jumps spec E' (j + 1) ω =
        Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps spec E' j ω₀) (g ω) := by
    filter_upwards [hpmω] with ω hω
    rw [pastMap_succ_eq_snoc spec E' j ω, hω]
  have hker2 := KernelTower.ae_condExpKernel_comap_eq (P := condExpKernel P (pastSigma κ b jumps spec E' j) ω₀)
    hpmΩ hgm (measurable_snoc_const _) (ψ := fun u : PastData (j + 1) => u (Fin.last j))
    (measurable_pi_apply _) hfg (Eventually.of_forall fun ω => rfl)
  have hlift := KernelTower.ae_ae_condExpKernel_of_ae (P := condExpKernel P (pastSigma κ b jumps spec E' j) ω₀)
    (m := MeasurableSpace.comap g inferInstance) hgm.comap_le
    ((ae_counterflow_regular hT13 hκ hWk hζk).and hidk)
  filter_upwards [hpmω, hregν, hkk, hclν, hGν, hker2, hlift] with ω hω hregω hkkω hclω hGω hker2ω hliftω
  intro hs1 hti1 c θ' hl1 h'' htr''
  have hsω : AllSucc (schedDelta 0 l) (fun i => E' i ω) j := hs1.mono (Nat.le_succ j)
  have hjω : schedDelta 0 l j < (E' j ω).2 := hs1 j (Nat.lt_succ_self j)
  have hk1 : j + 1 < spec.2.2.length := by
    by_contra hk
    rw [launches_run_succ_of_length_le κ b jumps spec _ (not_lt.1 hk)] at hl1
    exact absurd hl1 (by simp)
  rw [(launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E' i ω) hk1).1 hs1] at hl1
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl1)
  have hrω := pieceRegular_of_allSucc hregω hk1.le hs1
  have hsucc : succChart spec.1 (schedDelta 0 l) (fun i => E' i ω) j =
      succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j := by
    refine succChart_eq_of_recOf_eq spec.1 hΔ j hsω hs0
      (fun i hi => continuousOn_of_pieceRegular (hrω i (Nat.lt_succ_of_lt hi)) (hsω i hi))
      (fun i hi => continuousOn_of_pieceRegular (hr0 i hi) (hs0 i hi)) fun i hi => ?_
    have h1 := congrFun hω ⟨i, hi⟩
    rwa [pastMap_of_allSucc hgw hprog hΔ E' hlen_le hsω, pastMap_of_allSucc hgw hprog hΔ E' hlen_le hs0] at h1
  obtain ⟨hU, hU0⟩ := continuous_stopDrv (hrω j (Nat.lt_succ_self j))
  have hT : 0 ≤ stopTime (schedDelta 0 l j) (E' j ω) := NNReal.coe_nonneg _
  have hc_eq : succChart spec.1 (schedDelta 0 l) (fun i => E' i ω) (j + 1) =
      (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j).loewner (stopDrv (schedDelta 0 l j) (E' j ω))
        (stopTime (schedDelta 0 l j) (E' j ω)) := by
    change (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω) j).loewner _ _ = _
    rw [hsucc]
  have hc₂ := Chart.isConformal_id.loewner hU hU0 hT
  have hℓ₂ := hc₂.continuousOn_lift_inv (Chart.continuousOn_lift_loewner hU hU0 hT)
  have htr₂ : ∀ ω', IsChartTransport (Chart.id.loewner (stopDrv (schedDelta 0 l j) (E' j ω))
      (stopTime (schedDelta 0 l j) (E' j ω))) 1 0 (QuantumZipper.chiC κ) (hj' ω') (h'' ω') := fun ω' =>
    IsChartTransport.of_trans hconf.1 hc₂ hconf.2 hℓ₂ (htrj ω') (by
      rw [← Chart.loewner_eq_trans, ← hc_eq]
      exact htr'' ω')
  have hint_stop : IsInteriorStop (fun t => (E' j ω).1 t) (schedDelta 0 l j) := by
    have h1 := hti1 j (Nat.lt_succ_self j)
    have e : pieceStop spec (fun i => E' i ω) j = schedDelta 0 l j := by
      simp only [pieceStop]
      rw [show instrTime spec j = schedDelta 0 l j from instrTime_sched hj]
      exact min_eq_left hjω.le
    rwa [e] at h1
  obtain ⟨W₂, ζ₂, hW₂, hζ₂, hid₂⟩ := hGω hjω hint_stop h'' htr₂
  have hμ : condExpKernel (condExpKernel P (pastSigma κ b jumps spec E' j) ω₀) (MeasurableSpace.comap g inferInstance)
      ω = condExpKernel P (pastSigma κ b jumps spec E' (j + 1)) ω := hker2ω.symm.trans hkkω
  rw [hμ] at hW₂ hζ₂ hid₂ hliftω
  refine ⟨W₂, ζ₂, hW₂, hζ₂, ?_⟩
  have hB : HasBdryLimits (fwdMapInv (stopDrv (schedDelta 0 l j) (E' j ω))
      (stopTime (schedDelta 0 l j) (E' j ω))) :=
    (hrω j (Nat.lt_succ_self j)).hasBdryLimits (ne_top_of_le_ne_top (hΔ j) (min_le_left _ _))
  filter_upwards [hid₂, ae_counterflow_regular hT13 hκ hW₂ hζ₂, hliftω, hclω] with ω' hid₂ω hreg₂ω hlω hclω'
  obtain ⟨γ₂, hγ₂, hW₂c, hW₂0, -⟩ := hreg₂ω
  obtain ⟨⟨γk, hγk, hWkc, hWk0, htrk⟩, hidkω⟩ := hlω
  intro r z hz
  rw [hc_eq] at hz
  exact mem_of_tipAt_loewner_trans hext hU hU0 hT hB hγk hWkc hWk0 htrk hclω' hidkω hγ₂ hW₂c hW₂0 hid₂ω r z hz

end GW2Later

end Theorem14

end InteractingSLE
