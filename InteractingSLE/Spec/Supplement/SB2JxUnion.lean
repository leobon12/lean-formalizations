/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineEarly
import InteractingSLE.Spec.Supplement.SB2DrvLateCmp
import InteractingSLE.Spec.Supplement.GW2FbLocal
import InteractingSLE.Spec.Exist.Param12Kernel
import InteractingSLE.Spec.Sec4.Special3Thin
import InteractingSLE.Spec.Sec5.CrossRestartLawTopo

/-!
# SB2(1)'s late (S) line mean, part 1: FIN's union and its mean against the line set

Packet PROVE-T14-SB2DRV (round 8), the comparison half of the late regime (handoff §R7.2, steps 1–3). For the upper
flow's coupling (`HP.flow`: field `h' = h(· + u) + ψχ`, driver `W`) and a finite stopping time `τ ≤ t` of its driving
filtration with `τ < ζ`:

* `EntranceUnion.ae_mem_absPart_of_lt`: below the lifetime the flow part of the absolute union contains the flow
  points in `ℍ` up to the rule;
* `walkFill A'` (the fill of the walk version on the launch event, `ℍ` off it) with past-measurable avoidance events
  and history-marked locality for the retained past;
* **`exists_flowUnion`**: a version `K` of the coupling hull `K_τ` such that FIN's union
  `U = walkFill A' ∪ (K + u)` is a local set of the centred field, and every local-set mean of `U` agrees almost surely
  with every local-set mean of the (S) line set `D.lineS A' t` on the entrance event, after `T_L`, on `{t ≤ τ}`
  (field determination: `Exist.Param12.hasFieldDeterminedHistories`, `GW2Fb.exists_flowHull_marks`,
  `WalkLaw.isHistoryAvoidanceLocal_union_of_det`, `Cmp.ae_mean_eq_on_event_of_det`).

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

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Below the lifetime, every flow point in `ℍ` up to the rule lies in the flow part of the absolute union.** -/
theorem ae_mem_absPart_of_lt : ∀ᵐ ω ∂P, ∀ (T : ℝ≥0∞) (s : ℝ≥0), (s : ℝ≥0∞) ≤ T → (s : ℝ≥0∞) < ζ ω →
    η ω s ∈ H → η ω s ∈ D.absPart T ω := by
  filter_upwards [D.version] with ω hv T s hsT hsζ hsH
  obtain ⟨n, hn⟩ := exists_nat_gt (s : ℝ)
  have hsn' : (s : ℝ≥0∞) ≤ min (ζ ω) ((n : ℝ≥0) : ℝ≥0∞) := by
    refine le_min hsζ.le (ENNReal.coe_le_coe.2 ?_)
    rw [← NNReal.coe_le_coe]
    simpa using hn.le
  have hcap : capTime (n : ℝ≥0) (ζ ω) s = s := capTime_of_le hsn'
  rw [absPart, limSet_eq]
  refine Or.inr (mem_iUnion.2 ⟨n, ⟨s, ?_, ?_⟩, ?_⟩)
  · show (s : ℝ≥0∞) ≤ maxRule T (D.point ω) (pathCoord (D.ηc n ω))
    exact hsT.trans (le_max_left _ _)
  · rw [hv n s, hcap]
  · exact hsH

end EntranceUnion

/-! ### The walk fill -/

section WalkFill

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

open Classical in
/-- **The walk fill**: the fill of the walk version on the launch event, all of `ℍ` off it. -/
def walkFill (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (A' : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if ω ∈ launchSet κ b jumps E (k + 1) then fillH (cptClosure A' ω) else H

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem walkFill_subset_H (A' : Ω → Set ℂ) (ω : Ω) : walkFill κ b jumps E k A' ω ⊆ H := by
  unfold walkFill
  split_ifs
  · exact fun _ hz => hz.1
  · exact subset_rfl

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem isOpen_H_sdiff_walkFill (A' : Ω → Set ℂ) (ω : Ω) : IsOpen (H \ walkFill κ b jumps E k A' ω) := by
  unfold walkFill
  split_ifs
  · exact isOpen_H_diff_fillH (isCompact_cptClosure A' ω).isBounded
  · simp

/-- The avoidance events of the walk fill are events of the retained past. -/
theorem measurableSet_disjoint_walkFill (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {A' : Ω → Set ℂ}
    (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)]
      {ω | Disjoint (walkFill κ b jumps E k A' ω) U} := by
  classical
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have hL : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hS.1 (HP.drivers_regular _) (k + 1)
  have hF := measurable_fillH_cptClosure (ℋ := pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) hA'H hA'm
  have e : {ω | Disjoint (walkFill κ b jumps E k A' ω) U} =
      (launchSet κ b jumps E (k + 1) ∩ (fun ω => fillH (cptClosure A' ω)) ⁻¹' {S | Disjoint S U}) ∪
        ((launchSet κ b jumps E (k + 1))ᶜ ∩ {_ω | Disjoint H (U : Set ℂ)}) := by
    ext ω
    by_cases hω : ω ∈ launchSet κ b jumps E (k + 1)
    · simp [walkFill, hω]
    · simp [walkFill, hω]
  rw [e]
  exact (hL.inter (hF (measurableSet_avoid U.isOpen hUH))).union (hL.compl.inter (MeasurableSet.const _))

/-- **The walk fill is history-marked local for the retained past** (almost-sure enlargement of the walk prefix). -/
theorem isHistoryAvoidanceLocal_walkFill (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) :
    WholeField.IsHistoryAvoidanceLocal
      (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1))
      (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P := by
  obtain ⟨-, -, hloc0⟩ := walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)
  refine isHistoryAvoidanceLocal_of_ae_enlargement hloc0 ?_
    fun U hUH => measurableSet_disjoint_walkFill HP hA'H hA'm hUH
  filter_upwards [hA'ae, EntranceUnion.ae_isBounded_stageSet HP] with ω hA hbA z hz
  by_cases hl : ω ∈ launchSet κ b jumps E (k + 1)
  · rw [walkFill, ite_eq_left hl]
    have hb : Bornology.IsBounded (A' ω) := by rw [hA]; exact hbA hl
    have hzA' : z ∈ A' ω := by rw [hA]; exact hz.1
    refine ⟨hz.2, Or.inl ?_⟩
    rw [cptClosure, ite_eq_left hb]
    exact subset_closure (subset_closure hzA')
  · rw [walkFill, ite_eq_right hl]
    exact hz.2

end WalkFill

/-! ### FIN's union with the coupling hull -/

/-- Below the lifetime the translated coupling hull is the fill of the flow. -/
theorem image_add_fwdHull_eq_fillH {W : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (u : ℝ)
    (htr : IsGeneratingTrace W ζ' (fun s => γ s - u)) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ') :
    (fun z : ℂ => z + u) '' fwdHull (fun r : ℝ => W r.toNNReal) (s : ℝ) = fillH (γ '' Icc 0 s) := by
  have hc : ContinuousOn (fun r => γ r - (u : ℂ)) (Icc 0 s) :=
    htr.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hs.le
  have hcpt : IsCompact ((fun r => γ r - (u : ℂ)) '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hc
  rw [Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hcpt (htr.2.2 s hs)]
  have e : (fun r => γ r - (u : ℂ)) '' Icc 0 s = (fun z : ℂ => z - u) '' (γ '' Icc 0 s) := by
    rw [image_image]
  rw [e, Lw.fillH_image_sub_real, image_image]
  simp

theorem coe_untopD_of_le {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : τ ≤ (t : WithTop ℝ≥0)) :
    ((τ.untopD 0 : ℝ≥0) : WithTop ℝ≥0) = τ := by
  cases τ with
  | top => exact absurd h (not_le.2 (WithTop.coe_lt_top t))
  | coe r => rfl

section FlowUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **FIN's union with the coupling hull at `τ`, and its mean against the (S) line set.** For the upper flow's
coupling and a finite stopping time `τ ≤ t`, `τ < ζ`: a version `K` of the hull `K_τ` such that
`walkFill A' ∪ (K + u)` is a local set of the centred field, and every local-set mean of it agrees almost surely
with every local-set mean of `D.lineS A' t` on the entrance event, after `T_L`, on `{t ≤ τ}`. -/
theorem exists_flowUnion (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (t : ℝ≥0)
    {h' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b jumps u) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b jumps u) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (htrans : ∀ ω, IsTranslateAddConst u (ψ * chiC κ) (h ω) (h' ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL b jumps u) (flowLineXR b jumps u) (flowLineRhoL κ b jumps u ψ)
      (flowLineRhoR κ b jumps u ψ) P 𝓕 W VL VR B ζ h')
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun s => W s ω) (ζ ω) (fun s => η ω s - u))
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, τ ω < ζ ω)
    (hτt : ∀ ω, τ ω ≤ (t : WithTop ℝ≥0)) :
    ∃ K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      Measurable[mΩ, hittingSigma] (fun ω => walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω) ∧
      (∀ᵐ ω ∂P, walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω ⊆ H ∧
        IsOpen (H \ (walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω))) ∧
      IsLocalSet (fun ω => walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω)
        (WholeField.centredField h u₀) P ∧
      ∀ g gU : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (D.lineS A' (t : ℝ≥0∞)) (WholeField.centredField h u₀) P g →
        IsLocalSetMean (fun ω => walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω)
          (WholeField.centredField h u₀) P gU →
        ∀ᵐ ω ∂P, ω ∈ D.event →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
          (t : WithTop ℝ≥0) ≤ τ ω → gU ω = g ω := by
  classical
  have hκ := HP.kappa_pos
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have hpastle := hS.2.1 (k + 1)
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps u ψ)
    (flowLineRhoR κ b jumps u ψ) (flowLineXL b jumps u) (flowLineXR b jumps u)
  have hrel := Exist.eqOn_flowLine_harmonicExtension hκ HP.boundary u ψ hu₀ hu₀'
  have hh0' := WholeField.isZeroBoundaryGFF_centredField hC hu₀'
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hhm : Measurable (WholeField.centredField h u₀) := hh0.measurable
  have hdet := Exist.Param12.hasFieldDeterminedHistories (Exist.Staged.theorem12Statement_of_param h12p) h13 hκ
    (Theorem15.isOrderedForceWord_flowLine b jumps u) P 𝓕 W VL VR B ζ h' hC
  have hτne : ∀ ω, τ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top WithTop.coe_ne_top (hτt ω)
  obtain ⟨K, hKτ, hKe, hKc, hτd, -⟩ := GW2Fb.exists_flowHull_marks hκ hC hdet hu₀' hh0' hX hτ hτζ hτne
  have hτle : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  -- the stopped marks are determined by the centred field
  have hcomap : MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P := by
    have e : WholeField.centredField h' u₀' =
        fun ω => Exist.flowField (-(-u)) 0 (WholeField.centredField h u₀ ω) := funext fun ω => by
      rw [Sec7.SideHeight.centredField_eq_flowField htrans hu₀.1 hu₀'.1 hrel ω, Sec7.SideHeight.flowField_neg_neg]
    rw [e]
    refine le_trans ?_ (fun s hs => ⟨s, hs, EventuallyEq.rfl⟩)
    exact ((Exist.measurable_flowField (-(-u)) 0).comp (comap_measurable _)).comap_le
  have hdetK : hτ.measurableSpace ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P :=
    hτd.trans (Supp8.Q3Chain.aeSigma_le_of_le hcomap)
  -- the translated hull
  set Ku : Ω → Set ℂ := fun ω => (fun z : ℂ => z + u) '' K ω with hKudef
  have hKuτ : Measurable[hτ.measurableSpace, hittingSigma] Ku := (Sec7.SideHeight.measurable_image_add u).comp hKτ
  have hKum : Measurable[mΩ, hittingSigma] Ku := hKuτ.mono hτle le_rfl
  have hKue : ∀ᵐ ω ∂P, Ku ω = (fun z : ℂ => z + u) '' fwdHull (fun r : ℝ => W r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
    filter_upwards [hKe] with ω hω
    simp only [hKudef, hω]
  have hlocK := Sec7.SideHeight.isHistoryAvoidanceLocal_flowHull hC hκ htrans hh0 hu₀.1 hu₀' hrel hX hτ hτζ hKum hKue
  have hKev : ∀ V : TopologicalSpace.Opens ℂ, (V : Set ℂ) ⊆ H →
      MeasurableSet[hτ.measurableSpace] {ω | Disjoint (Ku ω) V} := fun V hV =>
    hKuτ (measurableSet_avoid V.isOpen hV)
  have hKuc : ∀ᵐ ω ∂P, Ku ω ⊆ H ∧ IsOpen (H \ Ku ω) := by
    filter_upwards [hKc] with ω hω
    exact Sec7.SideHeight.image_add_relClosed u hω
  -- the walk fill and the union
  have hpast := EntranceUnion.past_le_aeSigma h12p h13 HP u₀
  have hWev : ∀ V : TopologicalSpace.Opens ℂ, (V : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)]
        {ω | Disjoint (walkFill κ b jumps E k A' ω) V} := fun V hV =>
    measurableSet_disjoint_walkFill HP hA'H hA'm hV
  have hWloc := isHistoryAvoidanceLocal_walkFill h12p h13 HP hu₀ hA'H hA'm hA'ae
  have hUloc := WalkLaw.isHistoryAvoidanceLocal_union_of_det hhm hWev hKev hpast hdetK hWloc hlocK
  have hUev : ∀ V : TopologicalSpace.Opens ℂ, (V : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ⊔ hτ.measurableSpace]
        {ω | Disjoint (walkFill κ b jumps E k A' ω ∪ Ku ω) V} := fun V hV => by
    have e : {ω | Disjoint (walkFill κ b jumps E k A' ω ∪ Ku ω) V} =
        {ω | Disjoint (walkFill κ b jumps E k A' ω) V} ∩ {ω | Disjoint (Ku ω) V} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, disjoint_union_left]
    rw [e]
    exact (le_sup_left (b := hτ.measurableSpace) _ (hWev V hV)).inter
      (le_sup_right (a := pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) _ (hKev V hV))
  have hUm : Measurable[mΩ, hittingSigma] fun ω => walkFill κ b jumps E k A' ω ∪ Ku ω :=
    WalkMean.measurable_hitting_of_avoid (sup_le hpastle hτle) hUev
  have hUc : ∀ᵐ ω ∂P, walkFill κ b jumps E k A' ω ∪ Ku ω ⊆ H ∧
      IsOpen (H \ (walkFill κ b jumps E k A' ω ∪ Ku ω)) := by
    filter_upwards [hKuc] with ω hω
    refine ⟨union_subset (walkFill_subset_H _ _) hω.1, ?_⟩
    rw [← Set.sdiff_inter_sdiff]
    exact (isOpen_H_sdiff_walkFill _ _).inter hω.2
  have hUlocal : IsLocalSet (fun ω => walkFill κ b jumps E k A' ω ∪ Ku ω) (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hUm hUc).out 4 1).2 hUloc.isAvoidanceLocal
  refine ⟨K, hKτ.mono hτle le_rfl, hKe, hUm, hUc, hUlocal, fun g gU hg hgU => ?_⟩
  -- the (S) line set is marked local for the line marks and the stopped marks
  have hBev : ∀ V : TopologicalSpace.Opens ℂ, (V : Set ℂ) ⊆ H →
      MeasurableSet[D.lineFiltC HP t] {ω | Disjoint (D.lineS A' (t : ℝ≥0∞) ω) V} := fun V hV =>
    D.lineFilt_le_lineFiltC HP t _ (D.measurableSet_disjoint_lineS HP hA'H hA'm (t : ℝ≥0∞) hV)
  have hdetL : D.lineFiltC HP t ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P :=
    (show D.lineFiltC HP t ≤ LocalSets.aeSigma (D.absMarks (t : ℝ≥0∞)) P from inf_le_right).trans
      (Supp8.Q3Chain.aeSigma_le_of_le (D.absMarks_le_aeSigma h12p h13 HP (t : ℝ≥0∞)))
  have hlocL := D.isHistoryAvoidanceLocal_lineFiltC HP t
    (D.isHistoryAvoidanceLocal_lineS h12p h13 HP hu₀ hA'H hA'm hA'ae t)
  have hLK := WalkLaw.isHistoryAvoidanceLocal_union_of_det hhm hBev hKev hdetL hdetK hlocL hlocK
  have hsub : ∀ᵐ ω ∂P, (fun ω => D.lineS A' (t : ℝ≥0∞) ω ∪ Ku ω) ω = D.lineS A' (t : ℝ≥0∞) ω := by
    filter_upwards [hKue, htr, D.ae_mem_absPart_of_lt, D.ae_absPart_subset_range t, hτζ, hKuc] with
      ω hKω htrω hlow hbP hτω hKcω
    refine union_eq_left.2 fun z hz => ?_
    by_cases hev : ω ∈ D.event
    · obtain ⟨N, hN⟩ := hbP hev
      have hbP' : Bornology.IsBounded (D.absPart (t : ℝ≥0∞) ω) :=
        ((isCompact_Icc.image (D.paths.cont N ω)).isBounded).subset hN
      rw [EntranceUnion.lineS, ite_eq_left hev]
      right
      rw [cptClosure, ite_eq_left hbP', Sec7.SideHeight.fillH_closure]
      have hsτ := coe_untopD_of_le (hτt ω)
      have hsζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        have : ((((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hsτ]; exact hτω
        exact this
      have hst : ((τ ω).untopD 0 : ℝ≥0) ≤ t := by
        have : (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by rw [hsτ]; exact hτt ω
        exact_mod_cast this
      have hfill := image_add_fwdHull_eq_fillH u htrω hsζ
      rw [hKω, hfill] at hz
      rw [← Sec7.SideHeight.fillH_inter_H (η ω '' Icc 0 ((τ ω).untopD 0))] at hz
      refine fillH_mono ?_ hz
      rintro _ ⟨⟨r, hr, rfl⟩, hrH⟩
      exact hlow (t : ℝ≥0∞) r (ENNReal.coe_le_coe.2 (hr.2.trans hst))
        (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) hsζ) hrH
    · rw [EntranceUnion.lineS, ite_eq_right hev]
      exact hKcω.1 hz
  have hlocB : WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t ⊔ hτ.measurableSpace)
      (D.lineS A' (t : ℝ≥0∞)) (WholeField.centredField h u₀) P :=
    WalkLaw.isHistoryAvoidanceLocal_congr_ae hsub hLK
  -- the comparison event
  have hE' : MeasurableSet[D.lineFiltC HP t ⊔ hτ.measurableSpace]
      (D.event ∩ (D.earlyEv (t : ℝ≥0∞))ᶜ ∩ {ω | (t : WithTop ℝ≥0) ≤ τ ω}) := by
    have h1 : MeasurableSet[D.lineFiltC HP t] (D.event ∩ (D.earlyEv (t : ℝ≥0∞))ᶜ) :=
      D.marks_le_lineFiltC HP t _ ((D.measurableSet_event HP).inter (D.measurableSet_earlyEv HP _).compl)
    exact (le_sup_left (b := hτ.measurableSpace) _ h1).inter
      (le_sup_right (a := D.lineFiltC HP t) _ (hτ.measurableSet_ge' t))
  have hUB : ∀ᵐ ω ∂P, ω ∈ D.event ∩ (D.earlyEv (t : ℝ≥0∞))ᶜ ∩ {ω | (t : WithTop ℝ≥0) ≤ τ ω} →
      walkFill κ b jumps E k A' ω ∪ Ku ω = D.lineS A' (t : ℝ≥0∞) ω := by
    filter_upwards [hKue, htr, D.ae_mem_absPart_of_lt, D.ae_absPart_subset_range t, D.ae_absPart_subset_image,
      D.ae_mem_earlyEv_iff (t : ℝ≥0∞), hτζ] with ω hKω htrω hlow hbP hup hearly hτω
    rintro ⟨⟨hev, hne⟩, htτ⟩
    have hl := D.event_subset hev
    have hTL : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) :=
      not_le.1 fun h' => hne ((hearly hev).2 h')
    have hτeq : τ ω = (t : WithTop ℝ≥0) := le_antisymm (hτt ω) htτ
    have htζ : (t : ℝ≥0∞) < ζ ω := by
      have : ((t : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [← hτeq]; exact hτω
      exact this
    have hs : (τ ω).untopD 0 = t := by rw [hτeq]; rfl
    obtain ⟨N, hN⟩ := hbP hev
    have hbP' : Bornology.IsBounded (D.absPart (t : ℝ≥0∞) ω) :=
      ((isCompact_Icc.image (D.paths.cont N ω)).isBounded).subset hN
    rw [EntranceUnion.lineS, ite_eq_left hev, walkFill, ite_eq_left hl]
    congr 1
    have hfill := image_add_fwdHull_eq_fillH u htrω htζ
    rw [hKω, hs, hfill, cptClosure, ite_eq_left hbP', Sec7.SideHeight.fillH_closure]
    refine Subset.antisymm ?_ (fillH_mono ?_)
    · rw [← Sec7.SideHeight.fillH_inter_H (η ω '' Icc 0 t)]
      refine fillH_mono ?_
      rintro _ ⟨⟨r, hr, rfl⟩, hrH⟩
      exact hlow (t : ℝ≥0∞) r (ENNReal.coe_le_coe.2 hr.2) (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) htζ) hrH
    · intro y hy
      obtain ⟨σ, hσ, rfl⟩ := hup hev (t : ℝ≥0∞) hy
      rw [mem_ofPred_eq, max_eq_left hTL.le] at hσ
      exact ⟨σ, ⟨zero_le, ENNReal.coe_le_coe.1 hσ⟩, rfl⟩
  have hres := Cmp.ae_mean_eq_on_event_of_det hh0 (sup_le ((D.lineFiltC HP).le t) hτle)
    (sup_le_sup_right (D.past_le_marks.trans (D.marks_le_lineFiltC HP t)) _) hUm (D.measurable_lineS HP hA'H hA'm _)
    hUc (Eventually.of_forall fun ω => ⟨D.lineS_subset_H A' _ ω, D.isOpen_H_sdiff_lineS A' _ ω⟩) hUev
    (sup_le hpast hdetK) hUloc (fun V hV => le_sup_left (b := hτ.measurableSpace) _ (hBev V hV))
    (sup_le hdetL hdetK) hlocB hE' hUB hgU hg
  filter_upwards [hres, D.ae_mem_earlyEv_iff (t : ℝ≥0∞)] with ω h1 h2 hev hTL htτ
  exact h1 ⟨⟨hev, fun hmem => absurd ((h2 hev).1 hmem) (not_le.2 hTL)⟩, htτ⟩

end FlowUnion

end InteractingSLE.Theorem14.SB.Lv
