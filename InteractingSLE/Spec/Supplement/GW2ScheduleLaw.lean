/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SchedulePast
import InteractingSLE.Spec.Exist.StagedLawMain
import InteractingSLE.Spec.Exist.StagedLaw2Run

/-!
# The canonical schedule is a staged history

Packet PROVE-T14-TIP3. For a GW2 schedule `spec` (root `x₀ = spec.1`, the GW2 convention, angles `θ`, finite own times
`Δ`), the canonical family `canonFam` (`GW2ScheduleCanon`: field-determined pieces, run from the field sample `h ω`)
realizes the staged history in the sense of the frozen `IsStagedHistory`. The proof is the induction of the landed
staged law (`Exist.StagedLaw.stageLaw`), with the canonical word and field as **explicit** witnesses:

* `IsStageWitness … k (canonWord k) (canonField k)`: at a launch the chart of instruction `k` is conformal, the
  canonical field is the field read in it, and conditionally on the retained past it is a GFF with the data of the
  canonical word (`canonWitness_zero`, `canonWitness_succ`, the latter by the single-stage law `post_stage`);
* `StageOK … k`: the canonical `k`-th piece is, conditionally on the retained past, the flow line of the field read
  in the current chart (`stageOK_canon`, by `Staged.isOptionalHullCoupling_drv`: the field-determined driver of a GFF
  with the right data is an optional hull coupling).

The witnesses being explicit, they are the same objects for every vector of own times; this is what makes the
canonical construction jointly measurable in the switching times (`GW2ScheduleCanon`).

## Main results

* `canon_stageLaw`: the witnesses and the conditional flow lines at every instruction;
* `isStagedHistory_canonFam`: **the canonical family is a staged history of `spec`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw Restart LQGMetric

section Law

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (c₀ : BoundaryWord) (θ : ℕ → ℝ) (Δ : ℕ → ℝ≥0∞)

/-- **The canonical family of drivers** of the field `h` for the root `x₀`. -/
def canonFam (x₀ : ℝ) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun k ω => canonDrive hκ h12p βA c₀ x₀ θ Δ (h ω) k

/-- The canonical field before instruction `k`. -/
def canonField (x₀ : ℝ) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (k : ℕ) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  (canonState hκ h12p βA c₀ x₀ θ Δ (h ω) k).2

/-- The canonical word before instruction `k`, read off the retained past. -/
def canonWord (κ' : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (k : ℕ) (ω : Ω) : BoundaryWord :=
  pastWord βA c₀ spec.1 θ k (pastMap κ' b jumps spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k ω)

/-- Composition of a jointly measurable two-argument map with a fixed first argument. -/
theorem measurable_comp_const_left {α A B C : Type*} [MeasurableSpace α] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {F : A → B → C} (hF : Measurable fun p : A × B => F p.1 p.2) (a : A) {g : α → B}
    (hg : Measurable g) : Measurable fun x => F a (g x) :=
  hF.comp (measurable_const.prodMk hg)

theorem measurable_canonFam (x₀ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hβA : Measurable βA) (hh : Measurable h) (k : ℕ) : Measurable (canonFam hκ h12p βA c₀ θ Δ x₀ h k) :=
  measurable_comp_const_left (F := fun Δ' f => canonDrive hκ h12p βA c₀ x₀ θ Δ' f k)
    (measurable_canonDrive hκ h12p βA c₀ x₀ θ hβA k) Δ hh

theorem isRegularDriver_canonFam (x₀ : ℝ) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (k : ℕ) (ω : Ω) :
    IsRegularDriver (canonFam hκ h12p βA c₀ θ Δ x₀ h k ω) :=
  isRegularDriver_canonDrive hκ h12p βA c₀ x₀ θ _ _ _

theorem measurable_canonField (x₀ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hβA : Measurable βA) (hh : Measurable h) (k : ℕ) : Measurable (canonField hκ h12p βA c₀ θ Δ x₀ h k) :=
  measurable_snd.comp (measurable_comp_const_left (F := fun Δ' f => canonState hκ h12p βA c₀ x₀ θ Δ' f k)
    (measurable_canonState hκ h12p βA c₀ x₀ θ hβA k) Δ hh)

variable {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}

/-- **On the success event the canonical word read off the past is the canonical state's word.** -/
theorem canonWord_eq (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {Ω : Type u}
    {h : Ω → DistOn upperHalfPlaneOpens} {k : ℕ} (hk : k ≤ spec.2.2.length) {ω : Ω}
    (hs : AllSucc Δ (fun j => canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω) k) :
    canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k ω = (canonState hκ h12p βA c₀ spec.1 θ Δ (h ω) k).1 := by
  rw [canonWord, pastMap_of_allSucc hgw hprog hΔ _ hk hs]
  exact pastWord_canonRec βA c₀ spec.1 θ hκ h12p Δ (h ω) k

omit h12p βA c₀ in
/-- A launch of instruction `k < length` is the success of the earlier pieces. -/
theorem launch_ne_none_iff (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k < spec.2.2.length) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k ≠ none ↔ AllSucc Δ D k := by
  constructor
  · intro hl
    by_contra hs
    exact hl ((launches_run_gw2 hgw hprog hΔ D hk).2 hs)
  · intro hs
    rw [(launches_run_gw2 hgw hprog hΔ D hk).1 hs]
    exact Option.some_ne_none _

omit h12p βA c₀ in
/-- No launch after the end of the program. -/
theorem launch_eq_none_of_le (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : spec.2.2.length ≤ k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none := by
  rw [run_succ]
  have hnone : spec.2.2[k]? = none := List.getElem?_eq_none hk
  rw [hnone]
  exact launches_run_of_le spec D le_rfl

omit h12p βA c₀ in
/-- The instruction time of a flow program. -/
theorem instrTime_eq (hprog : IsFlowProg spec.2.2 θ Δ) {k : ℕ} (hk : k < spec.2.2.length) :
    instrTime spec k = Δ k := by
  simp only [instrTime, hprog k hk]

omit h12p βA c₀ in
/-- The instruction angle of a flow program. -/
theorem instrAngle_eq (hprog : IsFlowProg spec.2.2 θ Δ) {k : ℕ} (hk : k < spec.2.2.length) :
    instrAngle spec k = θ k := by
  simp only [instrAngle, hprog k hk]

omit h12p βA c₀ in
/-- The chart of the run before instruction `k`, on the success event. -/
theorem chart_run_eq (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ spec.2.2.length) (hs : AllSucc Δ D k) :
    (ExplState.run κ b jumps spec D k).2.2.2.2.1 = succChart spec.1 Δ D k :=
  ((run_gw2 hgw hprog hΔ D k hk).1 hs).2

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-! ### Instruction `0` -/

/-- **The witness at instruction `0`**: the root chart, the root word and the field read in the root chart. -/
theorem canonWitness_zero (hβA : Measurable βA)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) (hh : IsGFFWithBoundaryData P h b jumps) :
    IsStageWitness κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) 0
      (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h 0) (canonField hκ h12p βA c₀ θ Δ spec.1 h 0) := by
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have hgff := isGFFWithBoundaryData_shiftW spec.1 hh₀
  refine ⟨measurable_const, measurable_canonField hκ h12p βA c₀ θ Δ spec.1 hβA hh.1 0,
    Eventually.of_forall fun ω _ => ?_, ?_⟩
  · exact ⟨Chart.isConformal_id.recenter _, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift,
      isChartTransport_shiftChart _ _ _⟩
  · rw [pastSigma_zero]
    filter_upwards [ae_isGFFWithBoundaryData_condExpKernel_bot hgff] with ω₀ h0 _
    exact h0

/-! ### The canonical piece is a conditional flow line -/

/-- **The canonical piece is a conditional flow line** (`StageOK`), from the witness at instruction `k`: under the
regular conditional law given the retained past, at a launch, the canonical field is the field read in the current
chart, a GFF with the data of the canonical word, and the canonical piece is its field-determined flow-line driver
(`Staged.isOptionalHullCoupling_drv`). -/
theorem stageOK_canon (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {k : ℕ}
    (hW : IsStageWitness κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k
      (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k) (canonField hκ h12p βA c₀ θ Δ spec.1 h k)) :
    StageOK κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k := by
  classical
  set C := canonFam hκ h12p βA c₀ θ Δ spec.1 h with hCdef
  have hCm : ∀ j, Measurable (C j) := fun j => measurable_canonFam hκ h12p βA c₀ θ Δ spec.1 hβA.1 hh.1 j
  have hCreg : ∀ j ω, IsRegularDriver (C j ω) := fun j ω => isRegularDriver_canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω
  have hpm : Measurable (pastMap κ b jumps spec C k) :=
    measurable_pastMap runMeasStatement hb spec (fun j _ => hCm j) (fun j _ => hCreg j) k le_rfl
  have h𝒢 : pastSigma κ b jumps spec C k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  rcases lt_or_ge k spec.2.2.length with hk | hk
  swap
  · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
    rw [launch_eq_none_of_le _ hk] at hl
    exact absurd hl (by simp)
  have hL := measurableSet_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ C hk.le
  have : StandardBorelSpace (PastData k) := inferInstance
  have : MeasurableSpace.CountablySeparated (PastData k) := inferInstance
  have hatom0 := ae_ae_eq_of_comap (P := P) hpm
  rw [← pastSigma_eq_comap] at hatom0
  unfold StageOK
  filter_upwards [hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL, hatom0,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1] with ω₀ hpath hgff hmem hatom hpathK c θ' hl
  have hne : (ExplState.run κ b jumps spec (fun j => C j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  have hs₀ : AllSucc Δ (fun j => C j ω₀) k := (launch_ne_none_iff θ Δ hgw hprog hΔ _ hk).1 hne
  have hl' := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun j => C j ω₀) hk).1 hs₀
  rw [hl'] at hl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
  obtain ⟨hconf, hlift, -⟩ := hpath hne
  rw [chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs₀] at hconf hlift
  set c := succChart spec.1 Δ (fun j => C j ω₀) k with hcdef
  set ν := condExpKernel P (pastSigma κ b jumps spec C k) ω₀ with hν
  set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)
    with hh'def
  have hT' : ∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hmem' := hmem hs₀
  have hYh' : ∀ᵐ ω ∂ν, canonField hκ h12p βA c₀ θ Δ spec.1 h k ω = h' ω := by
    filter_upwards [hmem', hatom, hpathK] with ω hω hpω hpathω
    have hrun : ExplState.run κ b jumps spec (fun j => C j ω) k = ExplState.run κ b jumps spec (fun j => C j ω₀) k :=
      run_eq_of_readRec_eq spec (fun j _ => hCreg j ω) (fun j _ => hCreg j ω₀) fun i hi => congrFun hpω ⟨i, hi⟩
    have hneω := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => C j ω) hk).2 hω
    obtain ⟨-, -, hTω⟩ := hpathω hneω
    rw [hrun, chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs₀] at hTω
    exact hTω.unique hconf (hT' ω)
  have hgff' := isGFFWithBoundaryData_congr_ae (hgff hne) hh'm hYh'
  set w := canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k ω₀ with hw
  have hPC : IsPiecewiseConstantBoundaryData w.fn w.jumps := w.isPiecewiseConstantBoundaryData
  have hgff'' := isGFFWithBoundaryData_flowField hκ hPC 0 (θ k) hgff'
  have hCeq : ∀ᵐ ω ∂ν, C k ω = drvOf (detCode (paramΦ h12p hκ (flowLineNL w.fn w.jumps 0) (flowLineNR w.fn w.jumps 0))
      (((flowLineXL w.fn w.jumps 0, flowLineXR w.fn w.jumps 0),
        (flowLineRhoL κ w.fn w.jumps 0 (θ k), flowLineRhoR κ w.fn w.jumps 0 (θ k))),
        flowField 0 (θ k * QuantumZipper.chiC κ) (h' ω))) := by
    filter_upwards [hmem', hatom, hYh'] with ω hω hpω hYω
    have hword : (canonState hκ h12p βA c₀ spec.1 θ Δ (h ω) k).1 = w := by
      rw [← canonWord_eq hκ h12p βA c₀ θ Δ hgw hprog hΔ hk.le hω, hw, canonWord, canonWord, hpω]
    change wordDrv hκ h12p (θ k) (canonState hκ h12p βA c₀ spec.1 θ Δ (h ω) k).1
      (canonField hκ h12p βA c₀ θ Δ spec.1 h k ω) = _
    rw [hword, hYω]
    simp only [wordDrv, stagedDrv, wNL, wNR, wPad, truncWord_padFL]
  obtain ⟨𝓕, VL, VR, B, hcoup⟩ := isOptionalHullCoupling_drv h12p h13 hκ
    (Theorem15.isOrderedForceWord_flowLine _ _ 0) hgff'' (hCm k) hCeq
  exact ⟨w.fn, w.jumps, h', hPC, hT', fun ω => flowField 0 (θ k * QuantumZipper.chiC κ) (h' ω), 𝓕, VL, VR, B,
    fun ω => isTranslateAddConst_flowField 0 _ (h' ω), hcoup⟩

/-! ### The next witness -/

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The canonical word before `k + 1` is the single-stage word of the canonical word before `k`. -/
theorem canonWord_succ (k : ℕ) (ω : Ω) :
    canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h (k + 1) ω =
      βA (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k ω, θ k,
        pastMap κ b jumps spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) (k + 1) ω (Fin.last k)) := by
  simp only [canonWord, pastWord]
  rw [pastMap_succ, Fin.init_snoc]

/-- **The next witness** (`post_stage`): from the witness and the conditional flow line at instruction `k`, the
canonical word and field before `k + 1` are a witness. -/
theorem canonWitness_succ (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {k : ℕ}
    (hW : IsStageWitness κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k
      (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k) (canonField hκ h12p βA c₀ θ Δ spec.1 h k))
    (hok : StageOK κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k) :
    IsStageWitness κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) (k + 1)
      (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h (k + 1)) (canonField hκ h12p βA c₀ θ Δ spec.1 h (k + 1)) := by
  classical
  set C := canonFam hκ h12p βA c₀ θ Δ spec.1 h with hCdef
  have hCm : ∀ j, Measurable (C j) := fun j => measurable_canonFam hκ h12p βA c₀ θ Δ spec.1 hβA.1 hh.1 j
  have hCreg : ∀ j ω, IsRegularDriver (C j ω) := fun j ω => isRegularDriver_canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω
  have hpm1 : Measurable (pastMap κ b jumps spec C (k + 1)) :=
    measurable_pastMap runMeasStatement hb spec (fun j _ => hCm j) (fun j _ => hCreg j) (k + 1) le_rfl
  have h𝒢1 : pastSigma κ b jumps spec C (k + 1) ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm1.comap_le
  have hYm := measurable_canonField hκ h12p βA c₀ θ Δ spec.1 hβA.1 hh.1
  have hpost := post_stage hβA runMeasStatement hκ hb hh (fun j _ => hCm j) (fun j _ => hCreg j) hok hW.1 hW.2.1
    hW.2.2.1 hW.2.2.2
  refine ⟨?_, hYm (k + 1), ?_, ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastWord βA c₀ spec.1 θ hβA.1 (k + 1)).comp (comap_measurable _)
  · -- the chart after piece `k`
    rcases lt_or_ge (k + 1) spec.2.2.length with hk1 | hk1
    swap
    · exact Eventually.of_forall fun ω hl => absurd (launch_eq_none_of_le _ hk1) hl
    have hk : k < spec.2.2.length := lt_trans (Nat.lt_succ_self k) hk1
    filter_upwards [hW.2.2.1, hpost.1] with ω hpath hgood hl1
    have hs1 := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => C j ω) hk1).1 hl1
    have hs : AllSucc Δ (fun j => C j ω) k := hs1.mono (Nat.le_succ k)
    have hne := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => C j ω) hk).2 hs
    obtain ⟨hconf, hlift, hT⟩ := hpath hne
    have hgd := hgood hne (by
      rw [instrTime_eq θ Δ hprog hk]; exact ne_top_of_le_ne_top (hΔ k) (min_le_left _ _))
    rw [instrTime_eq θ Δ hprog hk] at hgd
    rw [chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs] at hconf hlift hT
    rw [chart_run_eq θ Δ hgw hprog hΔ _ hk1.le hs1]
    have hWc : Continuous fun x : ℝ => (retOf (Δ k) (C k ω)).1 x.toNNReal :=
      (continuous_retOf (hCreg k ω) hgd).comp continuous_real_toNNReal
    have hW0 : (fun x : ℝ => (retOf (Δ k) (C k ω)).1 x.toNNReal) 0 = 0 := by
      change (C k ω).1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (Δ k) (C k ω).2)).toNNReal = 0
      rw [Real.toNNReal_zero, ENNReal.coe_zero, min_eq_left (zero_le (a := min (Δ k) (C k ω).2)),
        ENNReal.toNNReal_zero]
      exact (hCreg k ω).2.1
    change ((succChart spec.1 Δ (fun j => C j ω) k).loewner (fun x : ℝ => (retOf (Δ k) (C k ω)).1 x.toNNReal)
        ((min (Δ k) (C k ω).2).toNNReal : ℝ)).IsConformal ∧
      ContinuousOn (fun w => ((succChart spec.1 Δ (fun j => C j ω) k).loewner
        (fun x : ℝ => (retOf (Δ k) (C k ω)).1 x.toNNReal) ((min (Δ k) (C k ω).2).toNNReal : ℝ)).2.2
        (((succChart spec.1 Δ (fun j => C j ω) k).loewner (fun x : ℝ => (retOf (Δ k) (C k ω)).1 x.toNNReal)
          ((min (Δ k) (C k ω).2).toNNReal : ℝ)).2.1 w)) QuantumZipper.H ∧
      IsChartTransport ((succChart spec.1 Δ (fun j => C j ω) k).loewner
        (fun x : ℝ => (retOf (Δ k) (C k ω)).1 x.toNNReal) ((min (Δ k) (C k ω).2).toNNReal : ℝ)) 1 0
        (QuantumZipper.chiC κ) (h ω) (recField κ (recOf (Δ k) (C k ω)) (canonField hκ h12p βA c₀ θ Δ spec.1 h k ω))
    refine ⟨hconf.loewner hWc hW0 (NNReal.coe_nonneg _),
      hconf.continuousOn_loewner_lift hlift hWc hW0 (NNReal.coe_nonneg _), ?_⟩
    rw [InteractingSLE.Chart.loewner_eq_trans, ← recChart_eq_loewner (hCreg k ω) hgd]
    exact IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT
      (isChartTransport_recField κ _ _)
  · -- the conditional law after piece `k`
    rcases lt_or_ge (k + 1) spec.2.2.length with hk1 | hk1
    swap
    · exact Eventually.of_forall fun ω hl => absurd (launch_eq_none_of_le _ hk1) hl
    have hk : k < spec.2.2.length := lt_trans (Nat.lt_succ_self k) hk1
    set M : Set Ω := {ω | AllSucc Δ (fun j => C j ω) (k + 1)} with hMdef
    have hM : MeasurableSet[pastSigma κ b jumps spec C (k + 1)] M :=
      measurableSet_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ C hk1.le
    have hlastm : Measurable fun ω => pastMap κ b jumps spec C (k + 1) ω (Fin.last k) :=
      (measurable_pi_apply (X := fun _ : Fin (k + 1) => RecData) (Fin.last k)).comp hpm1
    have hCF : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (canonField hκ h12p βA c₀ θ Δ spec.1 h (k + 1) ω' φ : ℂ)) |
          pastSigma κ b jumps spec C (k + 1)] ω =
          gaussCF (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h (k + 1) ω) φ := by
      intro φ
      set X : Ω → ℂ := fun ω' => Complex.exp (Complex.I *
        (recField κ (pastMap κ b jumps spec C (k + 1) ω' (Fin.last k))
          (canonField hκ h12p βA c₀ θ Δ spec.1 h k ω') φ : ℂ)) with hXdef
      set X' : Ω → ℂ := fun ω' => Complex.exp (Complex.I *
        (canonField hκ h12p βA c₀ θ Δ spec.1 h (k + 1) ω' φ : ℂ)) with hX'def
      have hXX' : M.indicator X = M.indicator X' := by
        funext ω
        by_cases hω : ω ∈ M
        · rw [indicator_of_mem hω, indicator_of_mem hω, hXdef, hX'def]
          have hlast : pastMap κ b jumps spec C (k + 1) ω (Fin.last k) = recOf (Δ k) (C k ω) := by
            rw [pastMap_of_allSucc hgw hprog hΔ C hk1.le hω]
            rfl
          simp only [hlast]
          rfl
        · rw [indicator_of_notMem hω, indicator_of_notMem hω]
      have hXi : Integrable X P := GFF.integrable_exp_I_mul
        ((measurable_distOn_apply φ).comp (measurable_recField_comp κ hlastm (hYm k)))
      have hX'i : Integrable X' P := GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp (hYm (k + 1)))
      have h1 := condExp_indicator hXi hM
      have h2 := condExp_indicator hX'i hM
      filter_upwards [h1, h2, hpost.2 φ] with ω e1 e2 e3 hωM
      have hs : AllSucc Δ (fun j => C j ω) k := (show AllSucc Δ (fun j => C j ω) (k + 1) from hωM).mono
        (Nat.le_succ k)
      have hne := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => C j ω) hk).2 hs
      have hstop : min (instrTime spec k) (C k ω).2 ≠ ⊤ := by
        rw [instrTime_eq θ Δ hprog hk]; exact ne_top_of_le_ne_top (hΔ k) (min_le_left _ _)
      have e3' := e3 hne hstop
      rw [hXX'] at e1
      rw [e1, indicator_of_mem hωM, indicator_of_mem hωM] at e2
      change P[X' | pastSigma κ b jumps spec C (k + 1)] ω = _
      rw [← e2]
      change P[X | pastSigma κ b jumps spec C (k + 1)] ω = _ at e3'
      rw [e3', canonWord_succ, instrAngle_eq θ Δ hprog hk]
    have hK := ae_isGFFWithBoundaryData_condExpKernel h𝒢1 (M := M)
      (β := canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h (k + 1))
      (Eventually.of_forall fun ω _ => by rw [canonWord_succ]; exact hβA.2.1 _) (hYm (k + 1)) hCF
    filter_upwards [hK] with ω₀ hG hl1
    exact hG ((launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ _ hk1).1 hl1)

/-! ### The canonical family is a staged history -/

/-- **The staged law of the canonical family**: the explicit witnesses and the conditional flow lines at every
instruction. -/
theorem canon_stageLaw (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) :
    ∀ k, IsStageWitness κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k
        (canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h k) (canonField hκ h12p βA c₀ θ Δ spec.1 h k) ∧
      StageOK κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k
  | 0 =>
    have hW := canonWitness_zero hκ h12p βA c₀ θ Δ hβA.1 hc₀J hc₀ hh
    ⟨hW, stageOK_canon hκ h12p βA c₀ θ Δ h13 hβA hb hh hgw hprog hΔ hW⟩
  | k + 1 =>
    have ih := canon_stageLaw h13 hβA hb hc₀J hc₀ hh hgw hprog hΔ k
    have hW := canonWitness_succ hκ h12p βA c₀ θ Δ hβA hb hh hgw hprog hΔ ih.1 ih.2
    ⟨hW, stageOK_canon hκ h12p βA c₀ θ Δ h13 hβA hb hh hgw hprog hΔ hW⟩

/-- **The canonical family is a staged history** of the GW2 schedule `spec`: the canonical pieces, built from the field
sample alone (`canonDrive`), are, conditionally on the retained past, the flow lines of the field read in the current
chart (frozen `IsStagedHistory`). -/
theorem isStagedHistory_canonFam (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) :
    IsStagedHistory κ b jumps P h spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) := by
  have hCm : ∀ j, Measurable (canonFam hκ h12p βA c₀ θ Δ spec.1 h j) := fun j =>
    measurable_canonFam hκ h12p βA c₀ θ Δ spec.1 hβA.1 hh.1 j
  have hCreg : ∀ j ω, IsRegularDriver (canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω) := fun j ω =>
    isRegularDriver_canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω
  refine ⟨hCm, fun k => ?_, fun k => Eventually.of_forall fun ω => (hCreg k ω).2.2.2,
    fun k => (canon_stageLaw hκ h12p βA c₀ θ Δ h13 hβA hb hc₀J hc₀ hh hgw hprog hΔ k).2⟩
  rw [pastSigma_eq_comap]
  exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hCm j) (fun j _ => hCreg j) k le_rfl).comap_le

end Law

end GW2Schedule

end Theorem14

end InteractingSLE
