/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2ReadoutSchedule
import InteractingSLE.Spec.Supplement.SBTail2CanonLaunch

/-!
# SB4's launch parametrization from a measurable version of its forbidden side

The physical schedule path is now constructed from R51 regularity. Exact
rational-incidence events are obtained from a measurable version of the side:
on a measurable conull agreement set use the physical path; elsewhere use zero,
which is outside either forbidden side. No raw-side measurability is assumed.
The measurable side version and the actual conditional-tail construction remain
explicit mathematical hypotheses; neither is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Readout

open Leaf

/-- R51 alone gives openness of both physical sides of any completed staged
history: its finitely many regular ordinary pieces are relatively closed and
the remaining root and connectors are real. -/
theorem ae_isOpen_physSet_sides {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    ∀ᵐ ω ∂P,
      IsOpen (rightSideOf (ExplState.physSet κ b jumps spec (fun j => E j ω))) ∧
      IsOpen (leftSideOf (ExplState.physSet κ b jumps spec (fun j => E j ω))) := by
  filter_upwards [hR.ae_pieceRegular] with ω hω
  have hc := closure_physSet_inter_H_subset
    (GW1P.closure_tipSet_inter_H_subset_run spec (fun j => E j ω) hω)
  exact ⟨isOpen_rightSideOf hc, isOpen_leftSideOf hc⟩

/-- The rational-incidence parametrization used by the launch-tail assembly.
`hside` is the exact remaining measurability input; it asks for a version of
the whole side, rather than measurability of an arbitrarily selected path. -/
theorem exists_schedule_launch_param_of_side_version
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) {S : Ω → Set ℂ}
    (hzero : ∀ ω, (0 : ℂ) ∉ S ω) (hopen : ∀ᵐ ω ∂P, IsOpen (S ω))
    (hside : ∃ S' : Ω → Set ℂ, MeasurableSet {p : Ω × ℂ | p.2 ∈ S' p.1} ∧
      ∀ᵐ ω ∂P, S ω = S' ω) :
    ∃ a : Ω → ℝ≥0 → ℂ,
      (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
        Continuous (a ω) ∧ IsOpen (S ω) ∧
          schedulePiece κ b jumps x l (fun j => E j ω) k = range (a ω) := by
  classical
  obtain ⟨a, ham, ha⟩ := exists_measurable_schedulePiece_param hb hEm hR hk
  obtain ⟨S', hSm, hSS'⟩ := hside
  obtain ⟨G, hGae, hGm, hG⟩ := hSS'.exists_measurable_mem
  let a' : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ G then a ω t else 0
  have he : ∀ ω ∈ G, a' ω = a ω := by
    intro ω hω
    funext t
    exact ite_eq_left hω
  refine ⟨a', ?_, ?_⟩
  · intro q
    have hm : MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S' ω} :=
      hSm.preimage (measurable_id.prodMk (ham _))
    have hset : {ω | a' ω (q : ℝ).toNNReal ∈ S ω} =
        G ∩ {ω | a ω (q : ℝ).toNNReal ∈ S' ω} := by
      ext ω
      by_cases hω : ω ∈ G
      · simp only [Set.mem_ofPred_eq, mem_inter_iff, hω, true_and, he ω hω, hG ω hω]
      · simp only [Set.mem_ofPred_eq, mem_inter_iff, hω, false_and]
        change (if ω ∈ G then a ω (q : ℝ).toNNReal else 0) ∈ S ω ↔ False
        rw [ite_eq_right hω]
        exact iff_false_intro (hzero ω)
    rw [hset]
    exact hGm.inter hm
  · filter_upwards [ha, hopen, hGae] with ω hω hopenω hωG hl
    rw [he ω hωG]
    obtain ⟨hac, har⟩ := hω hl
    exact ⟨hac, hopenω, har.symm⟩

/-- For SB4's actual forbidden right side, openness and exclusion of zero
are consequences of R51 and the side definition. Only the measurable side
version remains as a new input to the incidence construction. -/
theorem exists_rightSide_launch_param_of_version
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {specL : ExplSpec} (hRL : StagedPiecesRegular κ b jumps P specL EL)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length)
    (hside : ∃ S' : Ω → Set ℂ, MeasurableSet {p : Ω × ℂ | p.2 ∈ S' p.1} ∧
      ∀ᵐ ω ∂P, rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)) = S' ω) :
    ∃ a : Ω → ℝ≥0 → ℂ,
      (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈
        rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
        Continuous (a ω) ∧
          IsOpen (rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))) ∧
          schedulePiece κ b jumps x l (fun j => E j ω) k = range (a ω) := by
  apply exists_schedule_launch_param_of_side_version hb hEm hR hk
  · intro ω hz
    exact (lt_irrefl (0 : ℝ)) (show (0 : ℝ) < 0 from hz.1.1)
  · exact (ae_isOpen_physSet_sides hRL).mono fun _ hω => hω.1
  · exact hside

/-- The canonical actual-tail construction now needs only the side's measurable
version in addition to the original staged/R51 hypotheses. Its physical path
and rational-incidence parametrization are supplied by the preceding theorem. -/
theorem hasScheduleLaunchTail_of_canonical_side_version
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) {original : Set ℝ} {S : Ω → Set ℂ}
    (hzero : ∀ ω, (0 : ℂ) ∉ S ω) (hopen : ∀ᵐ ω ∂P, IsOpen (S ω))
    (hside : ∃ S' : Ω → Set ℂ, MeasurableSet {p : Ω × ℂ | p.2 ∈ S' p.1} ∧
      ∀ᵐ ω ∂P, S ω = S' ω)
    (hcanon : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (schedulePiece κ b jumps x l (fun j => E j ω) k) (S ω)) ∨
      Canon.CanonicalLaunchData κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l original
        (fun ω => schedulePiece κ b jumps x l (fun j => E j ω) k) S ω₀ c) :
    HasScheduleLaunchTail κ b jumps P h x l E k original
      (fun ω => schedulePiece κ b jumps x l (fun j => E j ω) k) S := by
  exact Canon.hasScheduleLaunchTail_of_canonical hκ
    (exists_schedule_launch_param_of_side_version hb hE.1 hR hk hzero hopen hside) hcanon

end InteractingSLE.Theorem14.SB.Readout
