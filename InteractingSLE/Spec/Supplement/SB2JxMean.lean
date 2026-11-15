/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JxLate

/-!
# SB2(1)'s late (S) line mean, part 3: means of almost surely equal local sets; the walk fill's chart mean

Packet PROVE-T14-SB2DRV (round 8), inputs of FIN's union mean in the late regime (`SB2JxFinStatement`):

* `isHistoryAvoidanceLocal_bot` (an avoidance-local set is history-marked local for the trivial marks) and
  **`IsLocalSetMean.ae_eq_of_ae_eq_set`** (generic): local-set means of two local sets that agree almost surely
  agree almost surely (`GW2Sf.ae_mean_eq_on_marked_event` for the null-completed trivial marks);
* **`ae_walkFill_mean`**: every local-set mean of the walk fill, on the launch event, is the chart mean of the launch
  word minus `u₀` against every test function supported in the chart domain (the chart law of the retained past,
  `Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`, with the walk fill's complement equal to the chart
  domain, upgraded to all test functions by `WangWu.ae_forall_apply_eq_of_forall_ae`). This is FIN's `hind₁` before
  the translation into the coupling's coordinates.

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

/-! ### Almost surely equal local sets -/

section Congr

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- **An avoidance-local set is history-marked local for the trivial marks.** -/
theorem isHistoryAvoidanceLocal_bot {A : Ω → Set ℂ} (hA : IsAvoidanceLocal A h P) :
    WholeField.IsHistoryAvoidanceLocal ⊥ A h P := by
  intro U G hUH hG hd F hF
  rcases MeasurableSpace.measurableSet_bot_iff.1 hF with rfl | rfl
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    simp only [inter_empty, indicator_empty]
    rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]
  · simpa only [inter_univ] using hA U G hUH hG hd

/-- **Local-set means of almost surely equal local sets agree almost surely.** -/
theorem IsLocalSetMean.ae_eq_of_ae_eq_set (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A B : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hBm : Measurable[mΩ, hittingSigma] B)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hlA : IsLocalSet A h P) (hlB : IsLocalSet B h P) (hAB : ∀ᵐ ω ∂P, A ω = B ω)
    {gA gB : Ω → DistOn upperHalfPlaneOpens} (hgA : IsLocalSetMean A h P gA) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, gA ω = gB ω := by
  have hA' := Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma
    (isHistoryAvoidanceLocal_bot (((isLocalSet_tfae hh hAm hAc).out 4 1).1 hlA))
  have hB' := Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma
    (isHistoryAvoidanceLocal_bot (((isLocalSet_tfae hh hBm hBc).out 4 1).1 hlB))
  have := GW2Sf.ae_mean_eq_on_marked_event hh inf_le_left (Cmp.nullSets_le_inf_aeSigma ⊥) hAm hBm hAc hBc hA' hB'
    (E := univ) MeasurableSet.univ (hAB.mono fun ω hω _ => hω) hgA hgB
  filter_upwards [this] with ω hω
  exact hω (mem_univ ω)

end Congr

/-! ### The walk fill's chart mean -/

section WalkMean

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **On the launch event the chart domain is the complement of the walk fill.** -/
theorem ae_dom_eq_H_sdiff_walkFill (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      ((I.chart ω).dom : Set ℂ) = H \ walkFill κ b jumps E k A' ω := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [ae_verChart_eq_runChart hR (HP.drivers_regular _) (k + 1), hR.ae_pieceRegular, hA'ae,
    EntranceUnion.ae_isBounded_stageSet HP] with ω hver hpr hA hbA hl
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
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  have hbA' : Bornology.IsBounded (A' ω) := by rw [hA]; exact hbA hl
  rw [hDrun, hD.1.coe_dom.trans hD.2.1, walkFill, ite_eq_left hl, cptClosure, ite_eq_left hbA',
    Sec7.SideHeight.fillH_closure, hA, ← EntranceUnion.prefixPhysSet_inter_H, Sec7.SideHeight.fillH_inter_H]

/-- **The walk fill's chart mean**: every local-set mean of the walk fill, on the launch event, is the chart mean of
the launch word minus `u₀`, against every test function supported in the chart domain. -/
theorem ae_walkFill_mean (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω)
    {gW : Ω → DistOn upperHalfPlaneOpens}
    (hgW : IsLocalSetMean (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P gW) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ (I.chart ω).dom →
      gW ω φ = ∫ z, ((sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z - u₀ z) * φ z := by
  classical
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  obtain ⟨hc, hliftc, hliftH, hdom, hfwd, hCm, hliftm⟩ := I.chart_measurable
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hS.1 (HP.drivers_regular _) (k + 1)
  have hWm : Measurable[mΩ, hittingSigma] (walkFill κ b jumps E k A') :=
    WalkMean.measurable_hitting_of_avoid h𝒢 fun _ hUH => measurableSet_disjoint_walkFill HP hA'H hA'm hUH
  have hWc : ∀ ω, walkFill κ b jumps E k A' ω ⊆ H ∧ IsOpen (H \ walkFill κ b jumps E k A' ω) := fun ω =>
    ⟨walkFill_subset_H A' ω, isOpen_H_sdiff_walkFill A' ω⟩
  have hWloc := isHistoryAvoidanceLocal_walkFill h12p h13 HP hu₀ hA'H hA'm hA'ae
  have hWlocal : IsLocalSet (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hWm (Eventually.of_forall hWc)).out 4 1).2 hWloc.isAvoidanceLocal
  have hdomW := ae_dom_eq_H_sdiff_walkFill HP I hA'ae
  have hAD : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      ((I.chart ω).dom : Set ℂ) ⊆ H \ walkFill κ b jumps E k A' ω ∧
        IsOpen ((H \ walkFill κ b jumps E k A' ω) \ (I.chart ω).dom) := by
    filter_upwards [hdomW] with ω hω hl
    rw [hω hl, sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩
  have hmean : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      tsupport φ' ⊆ (I.chart ω).dom →
      gW ω φ' = (∫ z, ((sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z) * φ' z) -
        ∫ z, u₀ z * φ' z := fun φ' =>
    Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw h𝒢 hc hdom hfwd hCm hliftm hliftc HP.field hu₀
      (measurable_chartField I HP.field.1 h𝒢) hL𝒢 (Eventually.of_forall fun ω _ => isChartTransport_chartField I ω)
      (fun ψ' => ae_condExp_chartField_eq_gaussCF HP I ψ') hWm hWlocal hWloc hAD hgW φ'
  -- every test function at once
  set A₂ : Ω → Set ℂ := fun ω => if ω ∈ launchSet κ b jumps E (k + 1) then H \ (I.chart ω).dom else H with hA₂
  set m : Ω → ℂ → ℝ := fun ω z =>
    (sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z - u₀ z with hmdef
  have hA₂G : ∀ ω ∈ launchSet κ b jumps E (k + 1), H \ A₂ ω = (I.chart ω).dom := fun ω hω => by
    simp only [hA₂, ite_eq_left hω]
    exact Set.sdiff_sdiff_cancel_left (hc ω).dom_subset
  have hA₂n : ∀ ω ∉ launchSet κ b jumps E (k + 1), H \ A₂ ω = ∅ := fun ω hω => by
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
  have hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (gW ω) (H \ A₂ ω) := by
    filter_upwards [hgW.2.1, hAD] with ω h1 h2
    by_cases hω : ω ∈ launchSet κ b jumps E (k + 1)
    · rw [hA₂G ω hω]
      exact IsHarmonicDistOn.mono h1 (h2 hω).1
    · rw [hA₂n ω hω]
      exact Sec5.Aux61MeanId.isHarmonicDistOn_empty _
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A₂ ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ launchSet κ b jumps E (k + 1)
    · rw [hA₂G ω hω]
      exact (I.chart ω).dom.isOpen
    · rw [hA₂n ω hω]
      exact isOpen_empty
  have hm : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A₂ ω) := by
    filter_upwards [I.field] with ω hf
    by_cases hω : ω ∈ launchSet κ b jumps E (k + 1)
    · rw [hA₂G ω hω]
      obtain ⟨hpc, -⟩ := hf hω
      exact WalkSide.harmonicOnNhd_chartMean (hc ω) (hliftH ω) (sortedRep_spec hpc).1 hu₀.1 (chiC κ)
    · rw [hA₂n ω hω]
      intro z hz
      exact hz.elim
  have hφ : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ' ⊆ H \ A₂ ω →
      gW ω φ' = ∫ z, m ω z * φ' z := by
    intro φ'
    filter_upwards [hmean φ', I.field] with ω h1 hf hsupp
    by_cases hω : ω ∈ launchSet κ b jumps E (k + 1)
    · rw [hA₂G ω hω] at hsupp
      obtain ⟨hpc, -⟩ := hf hω
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
  filter_upwards [hall] with ω hω hl φ hsupp
  exact hω φ (by rw [hA₂G ω hl]; exact hsupp)

end WalkMean

end InteractingSLE.Theorem14.SB.Lv
