/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineClop
import InteractingSLE.Spec.Supplement.SB2DrvEraseKer
import InteractingSLE.Spec.Supplement.WalkSideAssembly
import InteractingSLE.Spec.Restart.RetAux79Word
import InteractingSLE.Spec.Restart.R1MeanChart
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Sec5.Aux61MeanIdUniq
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# SB2(1)'s (S) line mean, part 1: the early regime `t ≤ T_L`

Packet PROVE-T14-SB2DRV (round 6). `SB2LineSMeanStatement` splits at the first visit `T_L` of `L` by the upper flow
(**`sb2LineSMeanStatement_of_early_late`**). Before it (`a t = 0`, the relative hull is empty) the mean of the (S) line
set is the chart mean of the retained word, read in the launch chart:

* `D.earlyEv t`: on the entrance event, every late capped flow first hits `L` no earlier than `t`; an event of the
  entrance σ-algebra (`measurableSet_earlyEv`), almost surely `{t ≤ T_L}` there (`ae_mem_earlyEv_iff`);
* `ae_dom_clopen_early`: on `{t ≤ T_L}` the chart domain is clopen in `ℍ \ B t`;
* `bheProc_zero_eq_mean`: on a type cell the time-`0` coupling data are the word mean plus `ψχ`;
* **`sb2LineSMeanEarlyStatement`** (PROVED): the chart law given the entrance σ-algebra (round 3,
  `ae_condExp_chartField_marks`) and `Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw` on `D.earlyEv t`,
  upgraded to all test functions (`WangWu.ae_forall_apply_eq_of_forall_ae`), transported by the chart
  (`Restart.chartTransport_eq_integral_of_eq_integral`, `RetAux79.chartTransport_eq_integral_couplingMean_zero`).

Hence (S) needs only the late regime: **`SB2LineSMeanLateStatement`**, **`sb2LineSMeanStatement_of_late`**.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6

/-! ### The early event -/

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

/-- **The early event** at the absolute time `t`: on the entrance event, every late enough capped flow first hits
`L` no earlier than `t`. -/
def earlyEv (t : ℝ≥0∞) : Set Ω :=
  D.event ∩ ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {ω | t ≤ hitQ (D.point ω) (pathCoord (D.ηc n ω))}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem earlyEv_subset (t : ℝ≥0∞) : D.earlyEv t ⊆ D.event := inter_subset_left

/-- The early event is an event of the entrance σ-algebra. -/
theorem measurableSet_earlyEv (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0∞) :
    MeasurableSet[D.marks] (D.earlyEv t) := by
  refine (D.measurableSet_event HP).inter (MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => ?_)
  have e : {ω | t ≤ hitQ (D.point ω) (pathCoord (D.ηc n ω))} =
      ruleHist (D.ηc n) (capLife ζ n) D.point hitQ ⁻¹' {k : KHist | t ≤ k.1.1} := rfl
  rw [e]
  exact le_iSup (iterMarks _ D.ηc (capLife ζ) D.point hitQ) n _
    (comap_ruleHist_le_iterMarks n _ ⟨_, measurableSet_le measurable_const (measurable_fst.comp measurable_fst), rfl⟩)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **On the entrance event the early event is almost surely `{t ≤ T_L}`.** -/
theorem ae_mem_earlyEv_iff (t : ℝ≥0∞) : ∀ᵐ ω ∂P, ω ∈ D.event →
    (ω ∈ D.earlyEv t ↔ t ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))) := by
  filter_upwards [D.version, D.Lp_eq, D.ae_mem_event_iff] with ω hv hL hev hω
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hω
  have hT : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω := (hev hl).1 hω
  have hz' : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [EntranceUnion.point, hL hl]
  obtain ⟨N₀, hN₀⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hT)
  have hhit : ∀ n : ℕ, N₀ ≤ n → hitQ (D.point ω) (pathCoord (D.ηc n ω)) =
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) := by
    intro n hn
    have hTn : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (n : ℝ≥0∞) :=
      hN₀.trans_le (by exact_mod_cast hn)
    have h1 := (hitQ_capped_eq (γ := η ω) (ζ := ζ ω) (γc := fun n => D.ηc n ω) (n := n) (D.paths.cont n ω) (hv n)
      (z := D.point ω) (by rw [hz']; exact hT) (by rw [hz']; exact hTn)).1
    rw [h1, hz']
  constructor
  · rintro ⟨-, hU⟩
    obtain ⟨N, hN⟩ := mem_iUnion.1 hU
    have h1 := mem_iInter₂.1 hN (max N N₀) (le_max_left _ _)
    rwa [mem_ofPred_eq, hhit _ (le_max_right _ _)] at h1
  · intro ht
    refine ⟨hω, mem_iUnion.2 ⟨N₀, mem_iInter₂.2 fun n hn => ?_⟩⟩
    show t ≤ hitQ (D.point ω) (pathCoord (D.ηc n ω))
    rw [hhit n hn]
    exact ht

end EntranceUnion

/-! ### The chart domain before the entrance -/

section Early

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **Before the entrance the chart domain is clopen in the complement of the (S) line set.** -/
theorem ae_dom_clopen_early (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ D.event →
      (t : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) →
      ((I.chart ω).dom : Set ℂ) ⊆ H \ D.lineS A' (t : ℝ≥0∞) ω ∧
        IsOpen ((H \ D.lineS A' (t : ℝ≥0∞) ω) \ (I.chart ω).dom) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [I.chart_eq, ae_verChart_eq_runChart hR (HP.drivers_regular _) (k + 1), hR.ae_pieceRegular,
    sb2ErasedAvoidStatement κ b jumps P h E k u ψ η ζ HP, D.ae_mem_event_iff, hA'ae,
    EntranceUnion.ae_isBounded_stageSet HP, D.ae_absPart_subset_range t, D.ae_absPart_subset_image]
    with ω hce hver hpr hav hev hA hbA hbP hup hevω htT
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hevω
  have hT : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω := (hev hl).1 hevω
  have hreg' : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  have hDrun : ((I.chart ω).dom : Set ℂ) =
      (((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)).2.2.2.2.1).dom : Set ℂ) := by
    show ((((verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)).dom : Set ℂ)) = _
    rw [Chart.dom_recenter, hver]
    rfl
  have hchart : I.chart ω = (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω) :=
    hce hl
  have hDl : ((I.chart ω).dom : Set ℂ) = ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ) := by
    rw [hchart, Chart.dom_recenter]
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  set FA : Set ℂ := fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) with hFAdef
  have hdomA : ((I.chart ω).dom : Set ℂ) = H \ FA := by
    rw [hDrun]
    exact hD.1.coe_dom.trans hD.2.1
  have hpc := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  have hcf := isConformal_chart I ω
  have hdomO : IsOpen ((I.chart ω).dom : Set ℂ) := (I.chart ω).dom.isOpen
  have hbA' : Bornology.IsBounded (A' ω) := by rw [hA]; exact hbA hl
  have hFA : fillH (cptClosure A' ω) = FA := by
    rw [cptClosure, ite_eq_left hbA', Sec7.SideHeight.fillH_closure, hA, ← EntranceUnion.prefixPhysSet_inter_H,
      Sec7.SideHeight.fillH_inter_H]
  obtain ⟨N, hN⟩ := hbP hevω
  have hbP' : Bornology.IsBounded (D.absPart (t : ℝ≥0∞) ω) :=
    ((isCompact_Icc.image (D.paths.cont N ω)).isBounded).subset hN
  have hFP : fillH (cptClosure (D.absPart (t : ℝ≥0∞)) ω) = fillH (D.absPart (t : ℝ≥0∞) ω) := by
    rw [cptClosure, ite_eq_left hbP', Sec7.SideHeight.fillH_closure]
  have hS : D.lineS A' (t : ℝ≥0∞) ω = FA ∪ fillH (D.absPart (t : ℝ≥0∞) ω) := by
    rw [EntranceUnion.lineS, ite_eq_left hevω, hFA, hFP]
  rw [hS]
  refine ⟨fun z hz => ⟨hcf.dom_subset hz, ?_⟩, ?_⟩
  · rintro (hzA | hzP)
    · have hz' : z ∈ ((I.chart ω).dom : Set ℂ) := hz
      rw [hdomA] at hz'
      exact hz'.2 hzA
    · have hdisj : Disjoint ((I.chart ω).dom : Set ℂ) (D.absPart (t : ℝ≥0∞) ω) := by
        rw [Set.disjoint_left]
        intro y hy hyP
        obtain ⟨σ, hσ, rfl⟩ := hup hevω (t : ℝ≥0∞) hyP
        have hσ' : (σ : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) :=
          hσ.trans (max_le htT le_rfl)
        rw [hDl] at hy
        exact Set.disjoint_left.1 (hav hl) hy ⟨σ, le_min (hσ'.trans hT.le) hσ', rfl⟩
      have hdcl : ((I.chart ω).dom : Set ℂ) ⊆ H \ closure (D.absPart (t : ℝ≥0∞) ω) := fun y hy =>
        ⟨hcf.dom_subset hy, fun hyc => by
          obtain ⟨y', hy'⟩ := (_root_.mem_closure_iff.1 hyc) _ hdomO hy
          exact Set.disjoint_left.1 hdisj hy'.1 hy'.2⟩
      refine FinRel.notMem_fillH_of_isPreconnected hz ?_ hdcl ?_ hzP
      · rw [hdomA]
        exact HalfPlaneSep.isPreconnected_H_diff_fillH hpc.isClosed hpc.isBounded
      · rw [hdomA]
        exact HalfPlaneSep.not_isBounded_H_diff_fillH hpc.isClosed hpc.isBounded
  · have e : (H \ (FA ∪ fillH (D.absPart (t : ℝ≥0∞) ω))) \ ((I.chart ω).dom : Set ℂ) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.2 ?_
      rw [hdomA]
      exact ⟨hz.1.1, fun h' => hz.1.2 (Or.inl h')⟩
    rw [e]
    exact isOpen_empty

end Early

/-! ### The word at relative time `0` -/

/-- **On a type cell the time-`0` coupling data are the word mean plus `ψχ`.** -/
theorem bheProc_zero_eq_mean {Ω : Type*} {κ ψ : ℝ} (hκ : 0 < κ) {w : WordType} {c : BoundaryWord}
    (hc : c ∈ FCDet.typeSet κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w))
    (hcp : IsPiecewiseConstantBoundaryData c.fn c.jumps) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) {xL : Ω → Fin w.1 → ℝ} {xR : Ω → Fin w.2.1 → ℝ} {ω : Ω}
    (hxL : xL ω = FCDet.typeXL κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c)
    (hxR : xR ω = FCDet.typeXR κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c) :
    ∀ z ∈ H, bheProc κ (typedRhoL w) (typedRhoR w) W (geomLW W xL) (geomRW W xR) ω 0 z =
      (sortedRep c).mean z + ψ * chiC κ := by
  have hft := FCDet.isFlowType_of_mem_typeSet hc
  obtain ⟨hsL, hsR⟩ := Restart.RetAux79.isFlowType_signs hft
  have hL0 : ∀ i, geomLW W xL i 0 ω = xL ω i := fun i =>
    geomLW_zero hWc hW0 (by rw [hxL]; exact hsL i)
  have hR0 : ∀ j, geomRW W xR j 0 ω = xR ω j := fun j =>
    geomRW_zero hWc hW0 (by rw [hxR]; exact hsR j)
  have hu := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := typedRhoL w) (ρR := typedRhoR w) (W := W)
    (VL := geomLW W xL) (VR := geomRW W xR) ω 0
  simp only [hL0, hR0, hW0, sub_zero, hxL, hxR] at hu
  have hsort := (sortedRep_spec hcp).1
  have hS : ({0} ∪ (c.jumps : Set ℝ)).Finite := (finite_singleton 0).union c.jumps.finite_toSet
  refine Restart.RetAux79.eqOn_mean_add_of_forceBoundaryData hu hsort (ψ * chiC κ) hS fun y hy => ?_
  have h0 : y ≠ 0 := fun h' => hy (Or.inl h')
  have hJ : y ∉ c.jumps := fun h' => hy (Or.inr h')
  rw [Restart.RetAux79.forceBoundaryData_zero_of_isFlowType hft y,
    Exist.forceBoundaryData_flowLine_seed hκ hcp 0 ψ h0 (by simpa using hJ), add_zero,
    (sortedRep_spec hcp).2.2 y hJ]

/-! ### The two regimes -/

/-- **Named input (the early regime of the (S) line mean)**: as `SB2LineSMeanStatement`, on `{t ≤ T_L}`. -/
def SB2LineSMeanEarlyStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionR HP I D),
    ∀ w ∈ I.types, ∀ A' : Ω → Set ℂ, (∀ ω, A' ω ⊆ H) →
    (∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U}) →
    (∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) →
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (D.lineS A' (t : ℝ≥0∞)) (WholeField.centredField h u₀) P g → ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      (t : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z

/-- **Named input (the late regime of the (S) line mean)**: as `SB2LineSMeanStatement`, on `{T_L < t}`. -/
def SB2LineSMeanLateStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionR HP I D),
    ∀ w ∈ I.types, ∀ A' : Ω → Set ℂ, (∀ ω, A' ω ⊆ H) →
    (∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U}) →
    (∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) →
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (D.lineS A' (t : ℝ≥0∞)) (WholeField.centredField h u₀) P g → ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z

/-- **The (S) line mean from its two regimes.** -/
theorem sb2LineSMeanStatement_of_early_late (hE : SB2LineSMeanEarlyStatement.{u})
    (hL : SB2LineSMeanLateStatement.{u}) : SB2LineSMeanStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t g hg φ
  filter_upwards [hE κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t g hg φ,
    hL κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t g hg φ] with ω h1 h2 hc hlt hφ
  by_cases ht : (t : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
  · exact h1 hc hlt hφ ht
  · exact h2 hc hlt hφ (not_le.1 ht)

/-! ### The early regime -/

/-- **The early regime of the (S) line mean** (Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LineSMeanEarlyStatement (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB2LineSMeanEarlyStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t g hg φ
  classical
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hpast := D.past_le_marks
  have h𝒢' := D.marks_le HP
  obtain ⟨hc, hliftc, hliftH, hdom, hfwd, hCm, hliftm⟩ := I.chart_measurable
  set G : Set Ω := D.earlyEv (t : ℝ≥0∞) with hGdef
  have hG : MeasurableSet[D.marks] G := D.measurableSet_earlyEv HP (t : ℝ≥0∞)
  have hGev : G ⊆ D.event := D.earlyEv_subset (t : ℝ≥0∞)
  set B : Ω → Set ℂ := D.lineS A' (t : ℝ≥0∞) with hBdef
  have hBm : Measurable[_, hittingSigma] B := D.measurable_lineS HP hA'H hA'm (t : ℝ≥0∞)
  have hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω) := fun ω =>
    ⟨D.lineS_subset_H A' _ ω, D.isOpen_H_sdiff_lineS A' _ ω⟩
  have hlocAbs := D.isHistoryAvoidanceLocal_lineS h12p h13 HP hu₀ hA'H hA'm hA'ae t
  have hlocal : IsLocalSet B (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hBm (Eventually.of_forall hBc)).out 4 1).2 hlocAbs.isAvoidanceLocal
  have hmark : WholeField.IsHistoryAvoidanceLocal D.marks B (WholeField.centredField h u₀) P :=
    fun U G' hUH hG' hd F hF => hlocAbs U G' hUH hG' hd F (D.marks_le_absMarks (t : ℝ≥0∞) _ hF)
  have hAD : ∀ᵐ ω ∂P, ω ∈ G →
      ((I.chart ω).dom : Set ℂ) ⊆ H \ B ω ∧ IsOpen ((H \ B ω) \ (I.chart ω).dom) := by
    filter_upwards [ae_dom_clopen_early HP I D hA'ae t, D.ae_mem_earlyEv_iff (t : ℝ≥0∞)] with ω h1 h2 hωG
    exact h1 (hGev hωG) ((h2 (hGev hωG)).1 hωG)
  -- the chart mean, one test function at a time
  have hmean : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G → tsupport φ' ⊆ (I.chart ω).dom →
      g ω φ' = (∫ z, ((sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z) * φ' z) -
        ∫ z, u₀ z * φ' z := fun φ' =>
    Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw h𝒢' hc (fun z => hpast _ (hdom z))
      (fun z => (hfwd z).mono hpast le_rfl) (fun z ε => hpast _ (hCm z ε)) (fun z => (hliftm z).mono hpast le_rfl)
      hliftc HP.field hu₀ (measurable_chartField I HP.field.1 h𝒢) hG
      (Eventually.of_forall fun ω _ => isChartTransport_chartField I ω)
      (fun ψ' => (ae_condExp_chartField_marks sb2ErasedAvoidStatement h12p h13 HP I hu₀ D ψ').mono
        fun ω h' hωG => h' (D.event_subset (hGev hωG)))
      hBm hlocal hmark hAD hg φ'
  -- every test function at once
  set A₂ : Ω → Set ℂ := fun ω => if ω ∈ G then H \ (I.chart ω).dom else H with hA₂
  set m : Ω → ℂ → ℝ := fun ω z =>
    (sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z - u₀ z with hmdef
  have hA₂G : ∀ ω ∈ G, H \ A₂ ω = (I.chart ω).dom := fun ω hω => by
    simp only [hA₂, ite_eq_left hω]
    exact Set.sdiff_sdiff_cancel_left (hc ω).dom_subset
  have hA₂n : ∀ ω ∉ G, H \ A₂ ω = ∅ := fun ω hω => by
    simp only [hA₂, ite_eq_right hω, sdiff_self]
  have hcont : ∀ ω, IsPiecewiseConstantBoundaryData (I.word ω).fn (I.word ω).jumps →
      ContinuousOn (fun z => (sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z)
        (I.chart ω).dom := by
    intro ω hpc
    have hmc : ContinuousOn (sortedRep (I.word ω)).mean H := fun z hz =>
      ((Restart.BoundaryWord.isBoundedHarmonicExtension_mean _ (sortedRep_spec hpc).1).1 z
        hz).1.continuousAt.continuousWithinAt
    exact (hmc.comp (hc ω).differentiableOn_fwd.continuousOn fun z hz => (hc ω).fwd_mem hz).sub
      (continuousOn_const.mul (hliftc ω))
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A₂ ω) := by
    filter_upwards [hg.2.1, hAD] with ω h1 h2
    by_cases hω : ω ∈ G
    · rw [hA₂G ω hω]
      exact IsHarmonicDistOn.mono h1 (h2 hω).1
    · rw [hA₂n ω hω]
      exact Sec5.Aux61MeanId.isHarmonicDistOn_empty _
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A₂ ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · rw [hA₂G ω hω]
      exact (I.chart ω).dom.isOpen
    · rw [hA₂n ω hω]
      exact isOpen_empty
  have hm : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A₂ ω) := by
    filter_upwards [I.field] with ω hf
    by_cases hω : ω ∈ G
    · rw [hA₂G ω hω]
      obtain ⟨hpc, -⟩ := hf (D.event_subset (hGev hω))
      exact WalkSide.harmonicOnNhd_chartMean (hc ω) (hliftH ω) (sortedRep_spec hpc).1 hu₀.1 (chiC κ)
    · rw [hA₂n ω hω]
      intro z hz
      exact hz.elim
  have hφ : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ' ⊆ H \ A₂ ω →
      g ω φ' = ∫ z, m ω z * φ' z := by
    intro φ'
    filter_upwards [hmean φ', I.field] with ω h1 hf hsupp
    by_cases hω : ω ∈ G
    · rw [hA₂G ω hω] at hsupp
      obtain ⟨hpc, -⟩ := hf (D.event_subset (hGev hω))
      rw [h1 hω hsupp]
      have hi1 := WholeField.integrable_mul_testOn (hcont ω hpc) φ' hsupp
      have hi2 := WholeField.integrable_mul_testOn hu₀c φ' φ'.tsupport_subset
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hmdef]
      ring
    · rw [hA₂n ω hω] at hsupp
      have h0 : ∀ z, φ' z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => hsupp hz
      have hφ0 : φ' = 0 := by
        ext z
        exact h0 z
      rw [hφ0, map_zero]
      have e : (fun z => m ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
        funext z
        rw [← hφ0, h0 z, mul_zero]
      rw [e, integral_zero]
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hharm hopen hm hφ
  -- the transport at one sample
  filter_upwards [hall, Vd.chain w hw t, D.ae_mem_earlyEv_iff (t : ℝ≥0∞), I.field] with
    ω hallω hch hGiff hf hcell hlt _ ht
  have hev : ω ∈ D.event := hcell.1.1
  have hωG : ω ∈ G := (hGiff hev).2 ht
  obtain ⟨hpc, -⟩ := hf (D.event_subset hev)
  obtain ⟨p, g', β', γ, tL, S, Wr, ηr, w', ηw, _, _, _, ⟨_, _, _, _, hTL, _, _, _⟩, _, _, _, ⟨_, ha0, _⟩⟩ :=
    hch hcell hlt
  have htL : (t : ℝ) ≤ tL := by
    have : (t : ℝ≥0∞) ≤ (tL : ℝ≥0∞) := by rw [hTL]; exact ht
    exact_mod_cast this
  have hat : Vd.a t ω = 0 := ha0 t htL
  have hT : ∀ φ' : TestOn upperHalfPlaneOpens, tsupport φ' ⊆ (I.chart ω).dom →
      (g ω + (h ω - WholeField.centredField h u₀ ω)) φ' =
        ∫ z, ((sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z) * φ' z := by
    intro φ' hφ'
    have h1 := hallω φ' (by rw [hA₂G ω hωG]; exact hφ')
    show g ω φ' + (h ω φ' - WholeField.centredField h u₀ ω φ') = _
    rw [WholeField.centredField_apply h hu₀.1 ω φ', h1, sub_sub_cancel]
    have hi1 : Integrable (fun z => m ω z * φ' z) :=
      WholeField.integrable_mul_testOn (((hcont ω hpc).sub (hu₀c.mono (hc ω).dom_subset)).congr fun z _ => by
        simp only [hmdef, Pi.sub_apply]) φ' hφ'
    have hi2 := WholeField.integrable_mul_testOn hu₀c φ' φ'.tsupport_subset
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hmdef]
    ring
  have hmc : ContinuousOn (sortedRep (I.word ω)).mean H := fun z hz =>
    ((Restart.BoundaryWord.isBoundedHarmonicExtension_mean _ (sortedRep_spec hpc).1).1 z
      hz).1.continuousAt.continuousWithinAt
  have hid := fun φ'' : TestOn upperHalfPlaneOpens =>
    Restart.chartTransport_eq_integral_of_eq_integral (hc ω) (hliftc ω) (chiC κ) hmc hT φ''
  have hWc : Continuous fun s : ℝ => Vd.W s.toNNReal ω := (Vd.W_cont ω).comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => Vd.W s.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, Vd.W_zero]
  have hu : ∀ z ∈ H, bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
      (geomRW Vd.W (cellXR κ ψ I.word w)) ω 0 z = (sortedRep (I.word ω)).mean z + ψ * chiC κ :=
    bheProc_zero_eq_mean HP.kappa_pos (mem_typeSet_of_mem_wordTypeCell hcell.1) hpc Vd.W_zero Vd.W_cont rfl rfl
  rw [hat, ENNReal.toNNReal_zero, NNReal.coe_zero]
  exact Restart.RetAux79.chartTransport_eq_integral_couplingMean_zero κ (hc ω)
    (CondDriverBridge.continuousOn_lift_inv (hc ω) (hliftc ω)) hWc hW0 hmc (ψ * chiC κ) hid hu φ

/-- **(S)'s line mean from its late regime alone** (Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LineSMeanStatement_of_late (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hL : SB2LineSMeanLateStatement.{u}) : SB2LineSMeanStatement.{u} :=
  sb2LineSMeanStatement_of_early_late (sb2LineSMeanEarlyStatement h12p h13) hL

/-- **SB2(1)'s ambient driver link from the repaired version half and the late regime of the (S) line mean**
(Theorems 1.2–1.3 as hypotheses, R48). -/
theorem sb2DriverLinkAmbStatement_of_versionR_late (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionRStatement.{u}) (hL : SB2LineSMeanLateStatement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_versionR_sMean h12p h13 hV (sb2LineSMeanStatement_of_late h12p h13 hL)

end InteractingSLE.Theorem14.SB.Lv
