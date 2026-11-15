/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineKer
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# SB2(1)'s line kernels, part 2: the line sets

Packet PROVE-T14-SB2DRV (round 4). The line sets of `hasSafeLaw_hasSafeMembers_of_lineSets` are chosen so that the hull
identity holds by definition: on the live cell `{a t < V}` of the type `w`, `B t = ℍ \ c(ℍ \ K_{a t})` (the complement
of the chart image of the relative hull's complement), elsewhere `B t = ℍ`. Here:

* `isHistoryAvoidanceLocal_of_ae_enlargement` (generic): an almost-sure enlargement with mark-measurable avoidance
  events of a history-marked local set is history-marked local;
* `chartImage c K = c(ℍ \ K)`, `mem_chartImage_iff`, `isOpen_chartImage`;
* **`measurableSet_inter_subset_chartImage`** (generic): for a measurable random chart and relatively closed random
  sets whose rational-ball avoidance events on `S` are measurable, `S ∩ {U ⊆ c(ℍ \ K)}` is measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open LocalSets Coupling

/-! ### Almost-sure enlargements -/

section Enlarge

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **An almost-sure enlargement of a marked local set is marked local**, once its avoidance events are marks. -/
theorem isHistoryAvoidanceLocal_of_ae_enlargement {C B : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ C h P) (hCB : ∀ᵐ ω ∂P, C ω ∩ H ⊆ B ω)
    (hB : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (B ω) U}) :
    WholeField.IsHistoryAvoidanceLocal ℋ B h P := by
  intro U G hUH hG hd F hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd (F ∩ {ω | Disjoint (B ω) U}) (hF.inter (hB U hUH))
  refine ⟨g, hg, Filter.EventuallyEq.trans (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)) hge⟩
  filter_upwards [hCB] with ω hω
  show (ω ∈ {ω | Disjoint (B ω) U} ∩ F) = (ω ∈ {ω | Disjoint (C ω) U} ∩ (F ∩ {ω | Disjoint (B ω) U}))
  apply propext
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hBU, hFω⟩
    refine ⟨Set.disjoint_left.2 fun z hzC hzU => Set.disjoint_left.1 hBU (hω ⟨hzC, hUH hzU⟩) hzU, hFω, hBU⟩
  · rintro ⟨-, hFω, hBU⟩
    exact ⟨hBU, hFω⟩

end Enlarge

/-! ### Chart images of complements -/

/-- The chart image of the complement of `K` in `ℍ`. -/
def chartImage (c : Chart) (K : Set ℂ) : Set ℂ := c.2.1 '' (H \ K)

theorem mem_chartImage_iff {c : Chart} (hc : c.IsConformal) {K : Set ℂ} {z : ℂ} :
    z ∈ chartImage c K ↔ z ∈ c.dom ∧ c.1 z ∉ K := by
  constructor
  · rintro ⟨y, ⟨hyH, hyK⟩, rfl⟩
    have hd := hc.inv_mem_dom hyH
    have hfi : c.1 (c.2.1 y) = y := hc.injOn (hc.fwd_mem hd) hyH (hc.inv_fwd hd)
    exact ⟨hd, by rw [hfi]; exact hyK⟩
  · rintro ⟨hz, hzK⟩
    exact ⟨c.1 z, ⟨hc.fwd_mem hz, hzK⟩, hc.inv_fwd hz⟩

theorem chartImage_subset_H {c : Chart} (hc : c.IsConformal) (K : Set ℂ) : chartImage c K ⊆ H := fun _ hz =>
  hc.dom_subset ((mem_chartImage_iff hc).1 hz).1

theorem isOpen_chartImage {c : Chart} (hc : c.IsConformal) {K : Set ℂ} (hK : IsOpen (H \ K)) :
    IsOpen (chartImage c K) := by
  have e : chartImage c K = (c.dom : Set ℂ) ∩ c.1 ⁻¹' (H \ K) := by
    ext z
    rw [mem_chartImage_iff hc]
    exact ⟨fun h => ⟨h.1, hc.fwd_mem h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact hc.differentiableOn_fwd.continuousOn.isOpen_inter_preimage c.dom.isOpen hK

/-! ### Measurability of the chart-image containment -/

section Meas

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω}

/-- A rational closed ball of positive radius inside an open set. -/
def ratBallIn (U : Set ℂ) : Set (ℚ × ℚ × ℚ) := {i | 0 < i.2.2 ∧ closedBall (ratCentre i) (i.2.2 : ℝ) ⊆ U}

theorem eq_iUnion_ratBallIn {U : Set ℂ} (hU : IsOpen U) :
    U = ⋃ i ∈ ratBallIn U, closedBall (ratCentre i) (i.2.2 : ℝ) := by
  refine Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun i hi => hi.2)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 4 by linarith)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r < z.re by linarith)
  obtain ⟨b', hb1, hb2⟩ := exists_rat_btwn (show z.im - r < z.im by linarith)
  have hdist : dist z (ratCentre (a, b', 2 * r)) ≤ (((2 * r : ℚ)) : ℝ) := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [ratCentre, Complex.sub_re, Complex.sub_im]
    have h1 : |z.re - (a : ℝ)| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |z.im - (b' : ℝ)| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    push_cast
    linarith
  have hr0' : (0 : ℚ) < 2 * r := by have : (0 : ℚ) < r := by exact_mod_cast hr0
                                    linarith
  refine mem_iUnion₂.2 ⟨(a, b', 2 * r), ⟨hr0', fun y hy => hεU ?_⟩, hdist⟩
  have hy' : dist y (ratCentre (a, b', 2 * r)) ≤ (((2 * r : ℚ)) : ℝ) := hy
  rw [mem_ball]
  calc dist y z ≤ dist y (ratCentre (a, b', 2 * r)) + dist z (ratCentre (a, b', 2 * r)) := dist_triangle_right _ _ _
    _ ≤ 4 * r := by push_cast at hy' hdist ⊢; linarith
    _ < ε := by linarith

theorem countable_ratBallIn (U : Set ℂ) : (ratBallIn U).Countable := Set.to_countable _

/-- On a closed ball of positive radius, a continuous map lands in a closed set as soon as the points of a dense set
do. -/
theorem image_closedBall_subset_of_dense {f : ℂ → ℂ} {Dd : Set ℂ} (hDd : Dense Dd) {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall z₀ r)) {X : Set ℂ} (hX : IsClosed X)
    (hq : ∀ q ∈ Dd ∩ closedBall z₀ r, f q ∈ X) : f '' closedBall z₀ r ⊆ X := by
  rintro _ ⟨z, hz, rfl⟩
  have hcl : closedBall z₀ r ⊆ closure (ball z₀ r ∩ Dd) := by
    rw [← closure_ball z₀ hr.ne']
    exact (closure_mono (hDd.open_subset_closure_inter isOpen_ball)).trans (by rw [closure_closure])
  have hsub : ball z₀ r ∩ Dd ⊆ closedBall z₀ r := fun y hy => ball_subset_closedBall hy.1
  have hzc := hcl hz
  have hmem : f z ∈ closure (f '' (ball z₀ r ∩ Dd)) :=
    (hf z hz).mono hsub |>.mem_closure_image hzc
  refine closure_minimal ?_ hX hmem
  rintro _ ⟨y, hy, rfl⟩
  exact hq y ⟨hy.2, hsub hy⟩

/-- **Measurability of the chart-image containment.** For a random chart with the measurability of a measurable random
chart, random sets `K` relatively closed in `ℍ` on `S` whose rational-ball avoidance events on `S` are measurable, and
an open `U`, the event `S ∩ {U ⊆ c(ℍ \ K)}` is measurable. -/
theorem measurableSet_inter_subset_chartImage {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[𝒢] {ω | closedBall z ε ⊆ (c ω).dom})
    {K : Ω → Set ℂ} {S : Set Ω} (hKo : ∀ ω ∈ S, IsOpen (H \ K ω))
    (hS : ∀ Fb : Finset (ℚ × ℚ × ℚ), MeasurableSet[𝒢] (S ∩ {ω | Disjoint (ballsK Fb) (K ω)}))
    {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet[𝒢] (S ∩ {ω | U ⊆ chartImage (c ω) (K ω)}) := by
  classical
  obtain ⟨Dd, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  set Bi : ℚ × ℚ × ℚ → Set ℂ := fun i => closedBall (ratCentre i) (i.2.2 : ℝ) with hBi
  set Q : ℚ × ℚ × ℚ → Finset (ℚ × ℚ × ℚ) → Set Ω := fun i Fb =>
    ⋂ q ∈ Dd ∩ Bi i, {ω | q ∈ (c ω).dom ∧ (c ω).1 q ∈ ballsK Fb} with hQ
  have hQm : ∀ i Fb, MeasurableSet[𝒢] (Q i Fb) := by
    intro i Fb
    refine MeasurableSet.biInter (hDc.mono inter_subset_left) fun q _ => ?_
    have e : {ω | q ∈ (c ω).dom ∧ (c ω).1 q ∈ ballsK Fb} =
        {ω | q ∈ (c ω).dom} ∩ ({ω | q ∈ (c ω).dom}.indicator fun ω => (c ω).1 q) ⁻¹' ballsK Fb := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [indicator_of_mem (show ω ∈ {ω | q ∈ (c ω).dom} from h1)]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [indicator_of_mem (show ω ∈ {ω | q ∈ (c ω).dom} from h1)] at h2⟩
    rw [e]
    exact (hdom q).inter (hfwd q (isCompact_ballsK Fb).isClosed.measurableSet)
  have key : S ∩ {ω | U ⊆ chartImage (c ω) (K ω)} =
      S ∩ ⋂ i ∈ ratBallIn U, ({ω | Bi i ⊆ (c ω).dom} ∩
        ⋃ Fb : Finset (ℚ × ℚ × ℚ), (Q i Fb ∩ (S ∩ {ω | Disjoint (ballsK Fb) (K ω)}))) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hωS, hsub⟩
      refine ⟨hωS, fun i hi => ?_⟩
      have hBU : Bi i ⊆ U := hi.2
      have hBd : Bi i ⊆ (c ω).dom := fun z hz => ((mem_chartImage_iff (hc ω)).1 (hsub (hBU hz))).1
      have hcpt : IsCompact ((c ω).1 '' Bi i) :=
        (isCompact_closedBall _ _).image_of_continuousOn ((hc ω).differentiableOn_fwd.continuousOn.mono hBd)
      have hin : (c ω).1 '' Bi i ⊆ H \ K ω := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨(hc ω).fwd_mem (hBd hz), ((mem_chartImage_iff (hc ω)).1 (hsub (hBU hz))).2⟩
      obtain ⟨Fb, hFU, hFK⟩ := exists_rationalBalls hcpt (hKo ω hωS) hin
      refine ⟨hBd, Fb, ?_, hωS, Set.disjoint_left.2 fun z hz hzK => (hFK hz).2 hzK⟩
      simp only [hQ, mem_iInter, mem_ofPred_eq]
      intro q hq
      exact ⟨hBd hq.2, ballsU_subset_ballsK Fb (hFU ⟨q, hq.2, rfl⟩)⟩
    · rintro ⟨hωS, hall⟩
      refine ⟨hωS, fun z hz => ?_⟩
      rw [eq_iUnion_ratBallIn hU] at hz
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
      obtain ⟨hBd, Fb, hQi, -, hdis⟩ := hall i hi
      have hqF : ∀ q ∈ Dd ∩ Bi i, (c ω).1 q ∈ ballsK Fb := fun q hq => by
        simp only [hQ, mem_iInter, mem_ofPred_eq] at hQi
        exact (hQi q hq).2
      have himg := image_closedBall_subset_of_dense hDd (by exact_mod_cast hi.1)
        ((hc ω).differentiableOn_fwd.continuousOn.mono hBd) (isCompact_ballsK Fb).isClosed hqF
      refine (mem_chartImage_iff (hc ω)).2 ⟨hBd hzi, fun hK => Set.disjoint_left.1 hdis (himg ⟨z, hzi, rfl⟩) hK⟩
  rw [key]
  have hSm : MeasurableSet[𝒢] S := by
    have := hS ∅
    simpa [ballsK] using this
  refine hSm.inter (MeasurableSet.biInter (countable_ratBallIn U) fun i _ => ?_)
  refine (hCm _ _).inter (MeasurableSet.iUnion fun Fb => (hQm i Fb).inter (hS Fb))

end Meas

/-! ### SB2(1)'s line sets -/

section SB2

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ} {u₀ : ℂ → ℝ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀}

theorem isConformal_chart (I : K2LaunchInputs κ b jumps P h E k u ψ) (ω : Ω) : (I.chart ω).IsConformal :=
  I.chart_measurable.1 ω

/-- The relative hull at physical time `t` after `T_L`. -/
def relHull (Vd : SB2LineVersionR HP I D) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal

/-- The live part of the type cell `w` at physical time `t`: below the relative lifetime. -/
def lineLive (Vd : SB2LineVersionR HP I D) (w : WordType) (t : ℝ≥0) : Set Ω :=
  seedCell κ ψ I.word D.event w ∩
    {ω | Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω}

open Classical in
/-- **The line set** at physical time `t`: on the live cell the complement of the chart image of the relative hull's
complement, elsewhere all of `ℍ`. -/
def lineB (Vd : SB2LineVersionR HP I D) (w : WordType) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  if ω ∈ lineLive Vd w t then H \ chartImage (I.chart ω) (relHull Vd t ω) else H

theorem isOpen_H_sdiff_relHull (Vd : SB2LineVersionR HP I D) (t : ℝ≥0) (ω : Ω) :
    IsOpen (H \ relHull Vd t ω) :=
  QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((Vd.W_cont ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg _)

theorem lineB_subset_H (Vd : SB2LineVersionR HP I D) (w : WordType) (t : ℝ≥0) (ω : Ω) : lineB Vd w t ω ⊆ H := by
  unfold lineB
  split_ifs
  · exact sdiff_subset
  · exact subset_rfl

theorem isOpen_H_sdiff_lineB (Vd : SB2LineVersionR HP I D) (w : WordType) (t : ℝ≥0) (ω : Ω) :
    IsOpen (H \ lineB Vd w t ω) := by
  unfold lineB
  split_ifs
  · rw [Set.sdiff_sdiff_cancel_left (chartImage_subset_H (isConformal_chart I ω) _)]
    exact isOpen_chartImage (isConformal_chart I ω) (isOpen_H_sdiff_relHull Vd t ω)
  · simp

/-- **The hull identity holds by construction.** -/
theorem H_sdiff_lineB_of_live (Vd : SB2LineVersionR HP I D) (w : WordType) (t : ℝ≥0) {ω : Ω}
    (hω : ω ∈ lineLive Vd w t) : H \ lineB Vd w t ω = (I.chart ω).2.1 '' (H \ relHull Vd t ω) := by
  unfold lineB
  rw [ite_eq_left hω, Set.sdiff_sdiff_cancel_left (chartImage_subset_H (isConformal_chart I ω) _)]
  rfl

theorem measurableSet_lineLive (Vd : SB2LineVersionR HP I D) {w : WordType} (hw : w ∈ I.types) (t : ℝ≥0) :
    MeasurableSet[D.lineFiltC HP t] (lineLive Vd w t) := by
  have hF : MeasurableSet[D.lineFiltC HP t] (seedCell κ ψ I.word D.event w) :=
    (D.marks_le_lineFiltC HP t) _ (measurableSet_seedCell (I.word_measurable.mono D.past_le_marks le_rfl)
      (D.measurableSet_event HP) w)
  have h1 := Vd.safeL w hw ∅ t
  have e : {ω | Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
      Disjoint (ballsK ∅) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal)} =
      {ω | Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω} := by
    ext ω
    simp [ballsK]
  rw [e] at h1
  exact hF.inter h1

/-- The avoidance events of the line set are events of the line filtration. -/
theorem measurableSet_disjoint_lineB (Vd : SB2LineVersionR HP I D) {w : WordType} (hw : w ∈ I.types) (t : ℝ≥0)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[D.lineFiltC HP t] {ω | Disjoint (lineB Vd w t ω) U} := by
  classical
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.lineFiltC HP t :=
    D.past_le_marks.trans (D.marks_le_lineFiltC HP t)
  obtain ⟨hc, -, -, hdom, hfwd, hCm, -⟩ := I.chart_measurable
  have hlive := measurableSet_lineLive Vd hw t
  have hS : ∀ Fb : Finset (ℚ × ℚ × ℚ), MeasurableSet[D.lineFiltC HP t]
      (lineLive Vd w t ∩ {ω | Disjoint (ballsK Fb) (relHull Vd t ω)}) := by
    intro Fb
    have hF : MeasurableSet[D.lineFiltC HP t] (seedCell κ ψ I.word D.event w) :=
      (D.marks_le_lineFiltC HP t) _ (measurableSet_seedCell (I.word_measurable.mono D.past_le_marks le_rfl)
        (D.measurableSet_event HP) w)
    have e : lineLive Vd w t ∩ {ω | Disjoint (ballsK Fb) (relHull Vd t ω)} = seedCell κ ψ I.word D.event w ∩
        {ω | Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (ballsK Fb) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal)} := by
      ext ω
      simp only [lineLive, relHull, mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [e]
    exact hF.inter (Vd.safeL w hw Fb t)
  have hmain := measurableSet_inter_subset_chartImage (𝒢 := D.lineFiltC HP t) hc (fun z => hpast _ (hdom z))
    (fun z => (hfwd z).mono hpast le_rfl) (fun z ε => hpast _ (hCm z ε))
    (fun ω _ => isOpen_H_sdiff_relHull Vd t ω) hS U.isOpen
  have e : {ω | Disjoint (lineB Vd w t ω) U} =
      (lineLive Vd w t ∩ {ω | (U : Set ℂ) ⊆ chartImage (I.chart ω) (relHull Vd t ω)}) ∪
        ((lineLive Vd w t)ᶜ ∩ {_ω | Disjoint H (U : Set ℂ)}) := by
    ext ω
    by_cases hω : ω ∈ lineLive Vd w t
    · simp only [lineB, mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and, mem_compl_iff,
        not_true_eq_false, false_and, or_false]
      constructor
      · intro hd z hz
        by_contra hn
        exact Set.disjoint_left.1 hd ⟨hUH hz, hn⟩ hz
      · intro hs
        exact Set.disjoint_left.2 fun z hz hzU => hz.2 (hs hzU)
    · simp only [lineB, mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff,
        not_false_eq_true, true_and, false_or, ↓reduceIte]
  rw [e]
  exact hmain.union (hlive.compl.inter (MeasurableSet.const _))

end SB2

end InteractingSLE.Theorem14.SB.Lv
