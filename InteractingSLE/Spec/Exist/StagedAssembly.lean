/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.Spec.Exist.StagedRun
import InteractingSLE.Spec.Theorem14Inputs
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Staged histories: `Theorem14.StagedHistoryConstructionStatement` from Theorem 1.2 (parametric), Theorem 1.3 and
the staged conditional law

Packet PROVE-STAGED. The frozen `exists_isStagedHistory` (Theorem 1.4's companion) follows from
`Theorem14.StagedHistoryConstructionStatement` (`Theorem14.exists_isStagedHistory_of_inputs`, PROVE-SEC7-D2). This file
proves that statement from three named inputs:

* `Theorem12ParamStatement` (`StagedDet.lean`): the frozen Theorem 1.2 with the determination map jointly Borel in the
  force word (obstruction (b) of PROVE-FLOWEXIST3);
* `Theorem13Statement` (PROVE-FLOWEXIST): exactly the frozen Theorem 1.3;
* **`StagedCondLawStatement`** (obstruction (a), GW1/GW2a): if the instructions before `k` are realized by measurable,
  everywhere regular drivers that are conditional flow lines (`StageOK`), then the retained past before `k` is a
  measurable map, and conditionally on it the field read in the chart of instruction `k` is a GFF whose boundary data
  `bdat` is read off the past, with a measurable flow-line word and a measurable chart field `Y`.

Obstruction (c) is proved (`StagedKernel.lean`), specialized here to flow lines (`exists_flowDrv_condKernel`). The history
is built one instruction at a time (`exists_partial`); the drivers of the earlier instructions are never changed, so the
limit history satisfies every clause of `IsStagedHistory` (`exists_regular_isStagedHistory_of_inputs`), with drivers
regular at **every** sample (`IsRegularDriver`: continuous before the lifetime, `0` at time `0`, constant from the
lifetime on, equal to the continuous left limit at a finite positive lifetime when there is one).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Staged

open LQGMetric

/-! ### The flow-line word, padded -/

/-- The flow-line word at the seed `0` of the angle-`θ` flow line of a field with data `b` (jumps `J`), padded by `0`. -/
def padFL (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) : PadWord :=
  ((fun i => if hi : i < flowLineNL b J 0 then flowLineXL b J 0 ⟨i, hi⟩ else 0,
    fun j => if hj : j < flowLineNR b J 0 then flowLineXR b J 0 ⟨j, hj⟩ else 0),
   (fun i => if hi : i < flowLineNL b J 0 then flowLineRhoL κ b J 0 θ ⟨i, hi⟩ else 0,
    fun j => if hj : j < flowLineNR b J 0 then flowLineRhoR κ b J 0 θ ⟨j, hj⟩ else 0))

theorem truncWord_padFL (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    truncWord (flowLineNL b J 0) (flowLineNR b J 0) (padFL κ θ b J) =
      ((flowLineXL b J 0, flowLineXR b J 0), (flowLineRhoL κ b J 0 θ, flowLineRhoR κ b J 0 θ)) := by
  simp only [truncWord, padFL, Fin.is_lt, ↓reduceDIte, Fin.eta]

/-- **A staged driver is regular at every sample**: continuous before its lifetime, `0` at time `0`, constant from its
lifetime on, and at a finite positive lifetime equal to its continuous left limit when it has one. -/
def IsRegularDriver (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2} ∧ e.1 0 = 0 ∧ (∀ t : ℝ≥0, e.2 ≤ t → e.1 t = e.1 e.2.toNNReal) ∧
    (e.2 ≠ ⊤ → 0 < e.2 → ∀ c : ℝ, Tendsto e.1 (𝓝[<] e.2.toNNReal) (𝓝 c) → e.1 e.2.toNNReal = c)

/-- **Step (c) for flow lines**: one measurable, everywhere regular driver is, for `P`-a.e. `ω₀`, the angle-`θ` flow-line
driver of every field `h'` that agrees almost surely with `Y` under the kernel and is there a GFF with the data
`bdat (r ω₀)`. -/
theorem exists_flowDrv_condKernel (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {R : Type*} [MeasurableSpace R] [StandardBorelSpace R] {r : Ω → R}
    (hr : Measurable r) (bdat : R → (ℝ → ℝ) × Finset ℝ) (θ : ℝ)
    (hnL : Measurable fun x => flowLineNL (bdat x).1 (bdat x).2 0)
    (hnR : Measurable fun x => flowLineNR (bdat x).1 (bdat x).2 0)
    (hpw : Measurable fun x => padFL κ θ (bdat x).1 (bdat x).2) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) :
    ∃ E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable E ∧ (∀ ω, IsRegularDriver (E ω)) ∧
      ∀ᵐ ω₀ ∂P, ∀ h' : Ω → DistOn upperHalfPlaneOpens,
        IsPiecewiseConstantBoundaryData (bdat (r ω₀)).1 (bdat (r ω₀)).2 →
        (∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀), Y ω = h' ω) →
        IsGFFWithBoundaryData (condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀) h'
          (bdat (r ω₀)).1 (bdat (r ω₀)).2 →
        IsFlowLineDriver κ (bdat (r ω₀)).1 (bdat (r ω₀)).2 θ
          (condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀) h' (fun t ω => (E ω).1 t)
          (fun ω => (E ω).2) := by
  set Y'' : Ω → DistOn upperHalfPlaneOpens := fun ω => flowField 0 (θ * QuantumZipper.chiC κ) (Y ω) with hY''
  have hY''m : Measurable Y'' := (measurable_flowField 0 _).comp hY
  obtain ⟨E, hEm, hEeq, hE⟩ := exists_drv_condKernel (P := P) h12p h13 hκ hr hnL hnR hpw hY''m
  refine ⟨E, hEm, fun ω => ?_, ?_⟩
  · rw [hEeq ω]; exact stagedDrv_regular h12p hκ _ _ _ _ _
  filter_upwards [hE] with ω₀ hω₀ h' hb hYh hh'
  set h'' : Ω → DistOn upperHalfPlaneOpens := fun ω => flowField 0 (θ * QuantumZipper.chiC κ) (h' ω)
  have htw := truncWord_padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2
  have hF : IsOrderedForceWord (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
      (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).1.1
      (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
      (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).1.2 := by
    rw [htw]; exact Theorem15.isOrderedForceWord_flowLine _ _ 0
  have hYh'' : ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀), Y'' ω = h'' ω :=
    hYh.mono fun ω hω => by simp only [hY'', h'', hω]
  have hgff := isGFFWithBoundaryData_flowField hκ hb 0 θ hh'
  have hgff' : IsGFFWithBoundaryData (condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀) h''
      (forceBoundaryData κ (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
        (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).2.1
        (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
        (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).2.2
        (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
        (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).1.1
        (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
        (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).1.2)
      (forceJumpSet (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
        (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).1.1
        (truncWord (flowLineNL (bdat (r ω₀)).1 (bdat (r ω₀)).2 0)
        (flowLineNR (bdat (r ω₀)).1 (bdat (r ω₀)).2 0) (padFL κ θ (bdat (r ω₀)).1 (bdat (r ω₀)).2)).1.2) := by
    rw [htw]; exact hgff
  obtain ⟨𝓕, VL, VR, B, hC⟩ := hω₀ h'' hF hYh'' hgff'
  rw [htw] at hC
  exact ⟨h'', 𝓕, VL, VR, B, fun ω => isTranslateAddConst_flowField 0 _ (h' ω), hC⟩

/-! ### The retained past -/

/-- The retained data before instruction `k`. -/
abbrev PastData (k : ℕ) : Type := Fin k → (ℚ → ℝ) × ℝ≥0∞ × Bool

/-- The retained past before instruction `k` (the map generating `pastSigma`). -/
def pastMap (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) : PastData k :=
  fun i =>
    let r := (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.1 i
    ((fun q : ℚ => r.1 (q : ℝ).toNNReal), r.2.1, r.2.2)

theorem pastSigma_eq_comap (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    pastSigma κ b jumps spec E k = MeasurableSpace.comap (pastMap κ b jumps spec E k) inferInstance := rfl

/-- Stage `k` of `E` is a conditional flow line: the last clause of `IsStagedHistory` at `k`. -/
def StageOK (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Prop :=
  ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
    ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
      IsPiecewiseConstantBoundaryData b' jumps' ∧
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
      IsFlowLineDriver κ b' jumps' θ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h'
        (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2)

/-- **Named input (GW1/GW2a with measurability): the staged conditional law.** For `0 < κ < 4`, a GFF `h` with
piecewise-constant data `b` on a standard Borel space and a boundary-continued program: whenever the instructions
`j < k` are realized by measurable, everywhere regular drivers that are conditional flow lines (`StageOK`), the retained
past before `k` is measurable, and there are boundary data `bdat` read off the past (with measurable flow-line word) and a
measurable field `Y` (the field read in the chart of the sample's own past) such that, for `P`-a.e. `ω₀` at which
instruction `k` launches a piece in the chart `c`, conditionally on the past the field read in `c` is `Y` almost surely
and is a GFF with the piecewise-constant data `bdat (past ω₀)` (Lemmas GW1, p. 618, and GW2a, p. 623: "the flow line of
`h` conditional on `η|[0, τ_{j−1}]` … in the current unbounded conditional domain"). -/
def StagedCondLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
    ∀ (k : ℕ) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      (∀ j < k, Measurable (E j)) → (∀ j < k, ∀ ω, IsRegularDriver (E j ω)) →
      (∀ j < k, StageOK κ b jumps P h spec E j) →
      Measurable (pastMap κ b jumps spec E k) ∧
      ∃ (bdat : PastData k → (ℝ → ℝ) × Finset ℝ) (Y : Ω → DistOn upperHalfPlaneOpens),
        Measurable (fun x => flowLineNL (bdat x).1 (bdat x).2 0) ∧
        Measurable (fun x => flowLineNR (bdat x).1 (bdat x).2 0) ∧
        (∀ θ : ℝ, Measurable fun x => padFL κ θ (bdat x).1 (bdat x).2) ∧ Measurable Y ∧
        ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
          (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
          IsPiecewiseConstantBoundaryData (bdat (pastMap κ b jumps spec E k ω₀)).1
            (bdat (pastMap κ b jumps spec E k ω₀)).2 ∧
          ∃ h' : Ω → DistOn upperHalfPlaneOpens,
            (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), Y ω = h' ω) ∧
            IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h'
              (bdat (pastMap κ b jumps spec E k ω₀)).1 (bdat (pastMap κ b jumps spec E k ω₀)).2

/-! ### The construction, one instruction at a time -/

section Construction

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}

/-- Stage `k` only sees the drivers of the instructions `j ≤ k`. -/
theorem StageOK.congr {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hE : StageOK κ b jumps P h spec E k)
    (hEE' : ∀ j ≤ k, E j = E' j) : StageOK κ b jumps P h spec E' k := by
  have hpast : pastSigma κ b jumps spec E k = pastSigma κ b jumps spec E' k :=
    pastSigma_congr spec fun j hj => hEE' j hj.le
  have hk : E k = E' k := hEE' k le_rfl
  unfold StageOK at hE ⊢
  rw [← hpast, ← hk]
  filter_upwards [hE] with ω₀ hω₀ c θ hl
  refine hω₀ c θ ?_
  rw [run_congr spec (k := k + 1) (D := fun j => E j ω₀) (D' := fun j => E' j ω₀)
    fun j hj => by rw [hEE' j (Nat.lt_succ_iff.1 hj)]]
  exact hl

/-- The partial-history invariant: the instructions `j < n` are realized. -/
def IsGoodPartial (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (n : ℕ) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  (∀ j < n, Measurable (E j)) ∧ (∀ j < n, ∀ ω, IsRegularDriver (E j ω)) ∧
    ∀ j < n, StageOK κ b jumps P h spec E j

/-- **One more instruction.** -/
theorem exists_good_succ (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hGW : StagedCondLawStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hspec : IsBoundaryContinuedProgram spec.2.2) {n : ℕ}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsGoodPartial κ b jumps P h spec n E) :
    ∃ E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, IsGoodPartial κ b jumps P h spec (n + 1) E' ∧ ∀ j < n, E' j = E j := by
  obtain ⟨hpm, bdat, Y, hnL, hnR, hpw, hY, hlaw⟩ :=
    hGW κ hκ hκ4 b jumps hb P h hh spec hspec n E hE.1 hE.2.1 hE.2.2
  obtain ⟨En, hEnm, hEnreg, hEn⟩ :=
    exists_flowDrv_condKernel (P := P) h12p h13 hκ hpm bdat (instrAngle spec n) hnL hnR (hpw _) hY
  set E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := Function.update E n En with hE'def
  have hlt : ∀ j < n, E' j = E j := fun j hj => Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hn : E' n = En := Function.update_self _ _ _
  refine ⟨E', ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩, hlt⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hlt j hj]; exact hE.1 j hj
    · rw [hn]; exact hEnm
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hlt j hj]; exact hE.2.1 j hj
    · rw [hn]; exact hEnreg
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (hE.2.2 j hj).congr fun i hi => (hlt i (lt_of_le_of_lt hi hj)).symm
    · -- the new stage
      have hpast : pastSigma κ b jumps spec E' j = pastSigma κ b jumps spec E j :=
        pastSigma_congr spec hlt
      unfold StageOK
      rw [hpast, hn]
      filter_upwards [hEn, hlaw] with ω₀ hEω₀ hlω₀ c θ hl
      have hl' : (ExplState.run κ b jumps spec (fun i => E i ω₀) (j + 1)).2.2.2.1 j = some (c, θ) := by
        rw [← hl]
        exact congrFun (launches_run_succ_congr spec fun i hi => by rw [hlt i hi]) j
      obtain ⟨hbd, h', hct, hYh', hgff⟩ := hlω₀ c θ hl'
      have hθ : θ = instrAngle spec j := angle_of_launch spec _ hl'
      subst hθ
      exact ⟨_, _, h', hbd, hct, hEω₀ h' hbd hYh' hgff⟩

/-- **Partial histories that extend each other.** -/
theorem exists_partial (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hGW : StagedCondLawStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hspec : IsBoundaryContinuedProgram spec.2.2) :
    ∃ H : ℕ → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, (∀ n, IsGoodPartial κ b jumps P h spec n (H n)) ∧
      ∀ n, ∀ j < n, H (n + 1) j = H n j := by
  classical
  have step := fun (n : ℕ) (E : {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ // IsGoodPartial κ b jumps P h spec n E}) =>
    exists_good_succ h12p h13 hGW hκ hκ4 hb hh hspec E.2
  let H : (n : ℕ) → {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ // IsGoodPartial κ b jumps P h spec n E} :=
    fun n => Nat.rec ⟨fun _ _ => (fun _ => 0, 0), fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
      (fun n E => ⟨(step n E).choose, (step n E).choose_spec.1⟩) n
  exact ⟨fun n => (H n).1, fun n => (H n).2, fun n j hj => (step n (H n)).choose_spec.2 j hj⟩

end Construction

/-- **The staged histories exist, with drivers regular at every sample** (from the three named inputs). -/
theorem exists_regular_isStagedHistory_of_inputs (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hGW : StagedCondLawStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    (hspec : IsBoundaryContinuedProgram spec.2.2) :
    ∃ D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, IsStagedHistory κ b jumps P h spec D ∧ ∀ k ω, IsRegularDriver (D k ω) := by
  obtain ⟨H, hH, hext⟩ := exists_partial h12p h13 hGW hκ hκ4 hb hh hspec
  -- the drivers of the earlier instructions are never changed
  have hstab : ∀ j n, j < n → H n j = H (j + 1) j := by
    intro j n hjn
    induction n with
    | zero => exact absurd hjn (Nat.not_lt_zero _)
    | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with hj | rfl
      · rw [hext n j hj, ih hj]
      · rfl
  set D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => H (j + 1) j with hD
  have hDH : ∀ n, ∀ j < n, D j = H n j := fun n j hj => (hstab j n hj).symm
  have hgood : ∀ k, ∀ j ≤ k, D j = H (k + 1) j := fun k j hj => hDH (k + 1) j (Nat.lt_succ_of_le hj)
  refine ⟨D, ⟨fun k => (hH (k + 1)).1 k (Nat.lt_succ_self k), fun k => ?_, fun k => ?_, fun k => ?_⟩,
    fun k ω => (hH (k + 1)).2.1 k (Nat.lt_succ_self k) ω⟩
  · -- the retained past is measurable
    have hpm := (hGW κ hκ hκ4 b jumps hb P h hh spec hspec k (H k) (hH k).1 (hH k).2.1 (hH k).2.2).1
    rw [pastSigma_congr spec (E' := H k) (hDH k), pastSigma_eq_comap]
    exact hpm.comap_le
  · exact Eventually.of_forall fun ω => ((hH (k + 1)).2.1 k (Nat.lt_succ_self k) ω).2.2.2
  · exact ((hH (k + 1)).2.2 k (Nat.lt_succ_self k)).congr fun j hj => (hgood k j hj).symm

/-- The staged-history construction with drivers regular at **every** sample (`IsRegularDriver`): the form needed by
consumers that read path properties of the drivers outside the conditional laws (PROVE-STRIPSYS3). -/
def RegularStagedHistoryConstructionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      ∃ D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, IsStagedHistory κ b jumps P h spec D ∧ ∀ k ω, IsRegularDriver (D k ω)

theorem regularStagedHistoryConstructionStatement_of_inputs (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hGW : StagedCondLawStatement.{u}) :
    RegularStagedHistoryConstructionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh spec hspec
  exact exists_regular_isStagedHistory_of_inputs h12p h13 hGW hκ hκ4 hb hh hspec

theorem RegularStagedHistoryConstructionStatement.stagedHistoryConstructionStatement
    (hR : RegularStagedHistoryConstructionStatement.{u}) : Theorem14.StagedHistoryConstructionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh spec hspec
  obtain ⟨D, hD, -⟩ := hR κ hκ hκ4 b jumps hb P h hh spec hspec
  exact ⟨D, hD⟩

/-- **`Theorem14.StagedHistoryConstructionStatement` from the three named inputs.** -/
theorem stagedHistoryConstructionStatement_of_inputs (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hGW : StagedCondLawStatement.{u}) :
    Theorem14.StagedHistoryConstructionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh spec hspec
  obtain ⟨D, hD, -⟩ := exists_regular_isStagedHistory_of_inputs h12p h13 hGW hκ hκ4 hb hh hspec
  exact ⟨D, hD⟩

end Staged

end Exist

end InteractingSLE
