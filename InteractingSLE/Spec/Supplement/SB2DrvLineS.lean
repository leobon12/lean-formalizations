/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineFill
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# SB2(1)'s (S) line sets: the filled union at absolute physical times

Packet PROVE-T14-SB2DRV (round 6). The (S) line set at the absolute physical time `T` is, on the entrance event, the
union of the fill of the retained lower prefix (through a version `A'` with exact past-measurable avoidance events) with
the fill of the capped upper flow up to `max(T, T_L)` (`D.absPart T`), and all of `ℍ` off the entrance event. On
`{T_L < T}` it is FIN's union `fill(A) ∪ fwdHull w T` at the deterministic time `T`.

* `D.absPart T`, **`D.measurableSet_disjoint_absPart`** (exact avoidance events in `D.absMarks T`);
* `D.lineS A' T`, `lineS_subset_H`, `isOpen_H_sdiff_lineS` (relatively closed at every sample),
  **`measurableSet_disjoint_lineS`**, `measurable_lineS` (hitting-measurable);
* **`ae_absPart_subset_range`**: on the entrance event the flow part lies in one capped range (hence is bounded);
* **`isHistoryAvoidanceLocal_lineS`**: the (S) line set is history-marked local for `D.absMarks T` (almost-sure
  enlargement of `D.absSet T`).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

/-- The flow part of the absolute union: the capped upper flows up to `max(T, T_n)`. -/
def absPart (T : ℝ≥0∞) : Ω → Set ℂ := limSet (fun _ => (∅ : Set ℂ)) D.ηc D.point (maxRule T)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem absPart_subset_H (T : ℝ≥0∞) (ω : Ω) : D.absPart T ω ⊆ H := by
  rw [absPart, limSet_eq]
  exact union_subset (empty_subset _) (iUnion_subset fun _ => inter_subset_right)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem absSet_eq (T : ℝ≥0∞) (ω : Ω) :
    D.absSet T ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω ∪ D.absPart T ω := by
  rw [absSet, absPart, limSet_eq, limSet_eq, empty_union]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_ruleHist_abs (T : ℝ≥0∞) (n : ℕ) :
    Measurable[D.absMarks T] (ruleHist (D.ηc n) (capLife ζ n) D.point (maxRule T)) :=
  Measurable.of_comap_le ((comap_ruleHist_le_iterMarks n).trans
    (le_iSup (iterMarks _ D.ηc (capLife ζ) D.point (maxRule T)) n))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The flow part's avoidance events are exact events of the absolute line.** -/
theorem measurableSet_disjoint_absPart (T : ℝ≥0∞) {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[D.absMarks T] {ω | Disjoint (D.absPart T ω) U} := by
  have e : {ω | Disjoint (D.absPart T ω) U} =
      ⋂ n, {ω | Disjoint (iterSet (fun _ => (∅ : Set ℂ)) D.ηc D.point (maxRule T) n ω) U} := by
    ext ω
    simp only [absPart, limSet, mem_ofPred_eq, disjoint_iUnion_left, mem_iInter]
  rw [e]
  refine @MeasurableSet.iInter _ _ (D.absMarks T) _ _ fun n => ?_
  exact @measurableSet_disjoint_iterSet Ω ℂ (fun _ => (∅ : Set ℂ)) D.ηc D.point (maxRule T) (D.absMarks T)
    (capLife ζ) D.paths.cont D.paths.start (fun U' _ => by simp) (fun n => D.measurable_ruleHist_abs T n) n U
    hUH

open Classical in
/-- **The (S) line set** at the absolute time `T`, built on a walk version `A'`. -/
def lineS (A' : Ω → Set ℂ) (T : ℝ≥0∞) (ω : Ω) : Set ℂ :=
  if ω ∈ D.event then fillH (cptClosure A' ω) ∪ fillH (cptClosure (D.absPart T) ω) else H

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem lineS_subset_H (A' : Ω → Set ℂ) (T : ℝ≥0∞) (ω : Ω) : D.lineS A' T ω ⊆ H := by
  unfold lineS
  split_ifs
  · exact union_subset (fun _ hz => hz.1) (fun _ hz => hz.1)
  · exact subset_rfl

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem isOpen_H_sdiff_lineS (A' : Ω → Set ℂ) (T : ℝ≥0∞) (ω : Ω) : IsOpen (H \ D.lineS A' T ω) := by
  unfold lineS
  split_ifs
  · have e : ∀ X Y : Set ℂ, H \ (X ∪ Y) = (H \ X) ∩ (H \ Y) := fun X Y => by
      ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
    rw [e]
    exact (isOpen_H_diff_fillH (isCompact_cptClosure A' ω).isBounded).inter
      (isOpen_H_diff_fillH (isCompact_cptClosure (D.absPart T) ω).isBounded)
  · simp

/-- **The (S) line set's avoidance events are exact events of the absolute line.** -/
theorem measurableSet_disjoint_lineS (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {A' : Ω → Set ℂ}
    (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (T : ℝ≥0∞) {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[D.absMarks T] {ω | Disjoint (D.lineS A' T ω) U} := by
  classical
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.absMarks T := le_limMarks
  have hF1 := measurable_fillH_cptClosure (ℋ := D.absMarks T) hA'H fun U' hU' => hpast _ (hA'm U' hU')
  have hF2 := measurable_fillH_cptClosure (ℋ := D.absMarks T) (D.absPart_subset_H T)
    fun U' hU' => D.measurableSet_disjoint_absPart T hU'
  have hE : MeasurableSet[D.absMarks T] D.event := (D.marks_le_absMarks T) _ (D.measurableSet_event HP)
  have e : {ω | Disjoint (D.lineS A' T ω) U} =
      (D.event ∩ ((fun ω => fillH (cptClosure A' ω)) ⁻¹' {S | Disjoint S U} ∩
        (fun ω => fillH (cptClosure (D.absPart T) ω)) ⁻¹' {S | Disjoint S U})) ∪
      (D.eventᶜ ∩ {_ω | Disjoint H (U : Set ℂ)}) := by
    ext ω
    by_cases hω : ω ∈ D.event
    · simp [lineS, hω, disjoint_union_left]
    · simp [lineS, hω]
  rw [e]
  exact (hE.inter ((hF1 (measurableSet_avoid U.isOpen hUH)).inter (hF2 (measurableSet_avoid U.isOpen hUH)))).union
    (hE.compl.inter (MeasurableSet.const _))

theorem measurable_lineS (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {A' : Ω → Set ℂ}
    (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (T : ℝ≥0∞) : Measurable[mΩ, hittingSigma] (D.lineS A' T) :=
  WalkMean.measurable_hitting_of_avoid (D.absMarks_le HP T) fun _ hUH =>
    D.measurableSet_disjoint_lineS HP hA'H hA'm T hUH

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **On the entrance event the flow part lies in one capped range.** -/
theorem ae_absPart_subset_range (T : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ D.event → ∃ N : ℕ,
    D.absPart T ω ⊆ D.ηc N ω '' Icc 0 (N : ℝ≥0) := by
  filter_upwards [D.version, D.Lp_eq, D.ae_mem_event_iff] with ω hv hL hev hω
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hω
  have hT : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω := (hev hl).1 hω
  have hz' : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [EntranceUnion.point, hL hl]
  set TL := firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) with hTLdef
  have hmax : max (T : ℝ≥0∞) TL ≠ ⊤ := max_ne_top ENNReal.coe_ne_top (ne_top_of_lt hT)
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hmax
  refine ⟨N, ?_⟩
  rw [absPart, limSet_eq, empty_union]
  rintro z hz
  obtain ⟨n, ⟨s', hs', rfl⟩, -⟩ := mem_iUnion.1 hz
  set σ : ℝ≥0 := capTime (n : ℝ≥0) (ζ ω) s' with hσdef
  have hσζn := coe_capTime_le (ζ := ζ ω) (n : ℝ≥0) s'
  have hσs' : (σ : ℝ≥0∞) ≤ s' := ENNReal.coe_le_coe.2 (capTime_le_self _ _)
  have hσmax : (σ : ℝ≥0∞) ≤ max (T : ℝ≥0∞) TL := by
    by_cases hTn : TL < (n : ℝ≥0∞)
    · have hhit := (hitQ_capped_eq (γ := η ω) (ζ := ζ ω) (γc := fun n => D.ηc n ω) (n := n) (D.paths.cont n ω)
        (hv n) (z := D.point ω) (by rw [hz']; exact hT) (by rw [hz']; exact hTn)).1
      have h1 := hs'
      simp only [mem_ofPred_eq, maxRule] at h1
      rw [hhit, hz'] at h1
      exact hσs'.trans h1
    · exact (hσζn.trans (min_le_right _ _)).trans ((not_lt.1 hTn).trans (le_max_right _ _))
  have hσN : (σ : ℝ≥0∞) ≤ min (ζ ω) (N : ℝ≥0) :=
    le_min (hσζn.trans (min_le_left _ _)) (hσmax.trans hN.le |>.trans (by exact_mod_cast le_rfl))
  refine ⟨σ, ⟨zero_le, ?_⟩, ?_⟩
  · have := hσN.trans (min_le_right _ _)
    exact_mod_cast this
  · rw [hv N σ, capTime_of_le hσN, ← hv n s']

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem stageSet_subset_prefixPhysSet (ω : Ω) :
    WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω ⊆
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1) :=
  fun _ hz => Or.inl (Or.inr hz.1)

/-- **On the launch event the retained lower prefix is almost surely bounded.** -/
theorem ae_isBounded_stageSet (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      Bornology.IsBounded (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hR := HP.pieces_regular _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  filter_upwards [hR.ae_pieceRegular] with ω hpr hl
  have hreg' : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  exact (Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd).isBounded.subset
    (stageSet_subset_prefixPhysSet ω)

/-- **The (S) line set is history-marked local** for the absolute line (almost-sure enlargement of `D.absSet T`). -/
theorem isHistoryAvoidanceLocal_lineS (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (T : ℝ≥0) :
    WholeField.IsHistoryAvoidanceLocal (D.absMarks (T : ℝ≥0∞)) (D.lineS A' (T : ℝ≥0∞))
      (WholeField.centredField h u₀) P := by
  refine isHistoryAvoidanceLocal_of_ae_enlargement (D.isHistoryAvoidanceLocal_abs h12p h13 HP hu₀ (T : ℝ≥0∞)) ?_
    fun U hUH => D.measurableSet_disjoint_lineS HP hA'H hA'm (T : ℝ≥0∞) hUH
  filter_upwards [hA'ae, ae_isBounded_stageSet HP, D.ae_absPart_subset_range T] with ω hA hbA hbP
  intro z hz
  by_cases hω : ω ∈ D.event
  · rw [lineS, ite_eq_left hω]
    rw [D.absSet_eq] at hz
    rcases hz.1 with hzA | hzP
    · left
      have hb : Bornology.IsBounded (A' ω) := by rw [hA]; exact hbA (D.event_subset hω)
      have hzA' : z ∈ A' ω := by rw [hA]; exact hzA
      refine ⟨hz.2, Or.inl ?_⟩
      rw [cptClosure, ite_eq_left hb]
      exact subset_closure (subset_closure hzA')
    · right
      obtain ⟨N, hN⟩ := hbP hω
      have hb : Bornology.IsBounded (D.absPart (T : ℝ≥0∞) ω) :=
        ((isCompact_Icc.image (D.paths.cont N ω)).isBounded).subset hN
      refine ⟨hz.2, Or.inl ?_⟩
      rw [cptClosure, ite_eq_left hb]
      exact subset_closure (subset_closure hzP)
  · rw [lineS, ite_eq_right hω]
    exact hz.2

end EntranceUnion

end InteractingSLE.Theorem14.SB.Lv
