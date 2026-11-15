/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideMean
import InteractingSLE.Spec.Supplement.WalkSideGeom

/-!
# Theorem 1.4's walk leaves: the two prefix inputs and the prefix inside the walk

Packet PROVE-T14-WALKSIDE. `WalkBdry.WalkPrefixSideStatement` is reduced (`WalkSideAssembly`) to two statements about
the **capped program** of a boundary walk (`capSpec`: the walk truncated before instruction `ℓ`, followed by the
angle-`θ` flow for own time `τ`, run with the walk's own drivers):

* **`PrefixMarkedLocalStatement θ right`** — the explored set of the capped program after `ℓ + 1` instructions is a
  history-marked local set for its own retained past, its avoidance events lying in that past up to null sets: the
  exact analogue of `WalkLaw.WalkMarkedLocalRegAEStatement` (Part D.2 and ruling R58) for the capped program, whose last
  stage is the piece stopped at the deterministic own time `τ` (Lemma GW3, proof: "Fix proper prefixes of the two
  selected arcs";
  `WalkLeaf.launchLocal_of_thm12_thm13` proves the uncapped stage, through capped entrance histories);
* **`PrefixChartVersionStatement θ right`** — the chart of the capped run after `ℓ + 1` instructions has a version
  measurable in that retained past (domain events, masked forward maps and lifts, closed-disc events), conformal with
  harmonic lift at every sample: the measurability hypotheses of the landed chart-mean lemma
  (`Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`) for the run's chart.

Also here (proved): `pastSigma_capSpec_le` (the capped retained past is part of the walk's, for rational `τ`),
`mem_pieces_run_mono`, `stageSet_capSpec_subset_walkSet` (the prefix lies in the walk) and the transfer of piece
regularity to the capped program (`pieceRegular_capSpec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged Restart LocalSets

/-! ### The two named inputs -/

/-- **Named input: the capped prefix of a boundary walk is a history-marked local set** (Lemma GW3, proof, p. 636:
"Fix proper prefixes of the two selected arcs … The two finite-stage marked local sets have their complete kernels by
GW1"; Part D.2; R58 form). For the walk `w = boundaryWalkSpec b jumps θ right`, every instruction `ℓ` and own time
`τ`: the explored set of the capped program `capSpec w ℓ θ τ` (run with the walk's drivers) after `ℓ + 1`
instructions has its avoidance events in the retained past of the capped program up to null sets, an open complement
almost surely, and is history-avoidance local for that past. -/
def PrefixMarkedLocalStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ → ∀ (ℓ : ℕ) (τ : ℝ≥0),
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
        MeasurableSet[aeSigma (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
            (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) P]
          {ω | Disjoint (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
            (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω) U}) ∧
      (∀ᵐ ω ∂P, IsOpen (H \ WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω)) ∧
      WholeField.IsHistoryAvoidanceLocal
        (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1))
        (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1))
        (WholeField.centredField h u₀) P

/-- **Named input: the prefix chart has a version measurable in the capped retained past** (the measurability
hypotheses of `Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`, for the chart of the capped run). For the walk
`w`, every instruction `ℓ` and own time `τ` there is a random chart `c'`, conformal with a continuous harmonic lift on
its domain at every sample, whose domain events, masked forward maps and lifts and closed-disc events are measurable in the
retained past of the capped program, and which is almost surely, on the capped launch event, the chart of the capped run
after `ℓ + 1` instructions. -/
def PrefixChartVersionStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω)) →
    ∀ (ℓ : ℕ) (τ : ℝ≥0), ∃ c' : Ω → Chart,
      (∀ ω, (c' ω).IsConformal) ∧ (∀ ω, ContinuousOn (c' ω).2.2 (c' ω).dom) ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (c' ω).2.2 (c' ω).dom) ∧
      (∀ z, MeasurableSet[pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)] {ω | z ∈ (c' ω).dom}) ∧
      (∀ z, Measurable[pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)] ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).1 z)) ∧
      (∀ (z : ℂ) (ε : ℝ), MeasurableSet[pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)] {ω | Metric.closedBall z ε ⊆ (c' ω).dom}) ∧
      (∀ z, Measurable[pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)] ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).2.2 z)) ∧
      ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        c' ω = (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1

/-! ### The capped retained past is part of the walk's (rational `τ`) -/

section Past

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ}

/-- The record of the piece stopped at a rational `τ`, read from the record of the unstopped piece (the zero record of
a non-launch is kept). -/
def capRec (τ : ℚ≥0) (r : RecData) : RecData :=
  if r.2.2 then (fun q : ℚ => r.1 (min q (τ : ℚ)), min ((τ : ℝ≥0) : ℝ≥0∞) r.2.1, decide (r.2.1 ≤ ((τ : ℝ≥0) : ℝ≥0∞)))
  else (fun _ => 0, 0, false)

theorem measurable_capRec (τ : ℚ≥0) : Measurable (capRec τ) := by
  have hdec : (fun r : RecData => decide (r.2.1 ≤ ((τ : ℝ≥0) : ℝ≥0∞))) =
      fun r => if r.2.1 ≤ ((τ : ℝ≥0) : ℝ≥0∞) then true else false := by
    funext r
    by_cases hr : r.2.1 ≤ ((τ : ℝ≥0) : ℝ≥0∞) <;> simp [hr]
  refine Measurable.ite (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const) ?_
    measurable_const
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_fst)
    (Measurable.prodMk (measurable_const.min (measurable_fst.comp measurable_snd)) ?_)
  rw [hdec]
  exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const) measurable_const
    measurable_const

/-- **The record of the piece stopped at `τ` is read from the record of the piece** (unstopped instruction). -/
theorem readRec_retOf_cap (τ : ℚ≥0) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    readRec (retOf ((τ : ℝ≥0) : ℝ≥0∞) e) = capRec τ (readRec (retOf ⊤ e)) := by
  have hflag : (readRec (retOf ⊤ e)).2.2 = true := by simp [readRec, retOf]
  rw [capRec, ite_eq_left_of_eq_true _ _ (eq_true hflag)]
  simp only [readRec, retOf, le_top, min_eq_right, decide_true]
  refine Prod.ext (funext fun q => ?_) rfl
  have e1 : (((min q (τ : ℚ) : ℚ) : ℝ).toNNReal : ℝ≥0∞) = min ((q : ℝ).toNNReal : ℝ≥0∞) ((τ : ℝ≥0) : ℝ≥0∞) := by
    rw [Rat.cast_min, Monotone.map_min (fun _ _ h => Real.toNNReal_le_toNNReal h), ENNReal.coe_min]
    rw [show ((τ : ℚ) : ℝ) = ((τ : ℝ≥0) : ℝ) by norm_cast, Real.toNNReal_coe]
  simp only [e1, min_assoc]

/-- **The retained past of the capped program is part of the program's** (rational `τ`, instruction `ℓ` an unstopped
angle-`θ` flow). -/
theorem pastSigma_capSpec_le {Ω : Type u} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hℓ : ℓ ≤ w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℚ≥0) :
    pastSigma κ b jumps (capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ≤ pastSigma κ b jumps w E (ℓ + 1) := by
  rw [pastSigma_eq_comap (spec := capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))]
  let _ : MeasurableSpace Ω := pastSigma κ b jumps w E (ℓ + 1)
  have hpm : Measurable (pastMap κ b jumps w E (ℓ + 1)) := comap_measurable (pastMap κ b jumps w E (ℓ + 1))
  refine Measurable.comap_le (measurable_pi_iff.2 fun i => ?_)
  have hp : Measurable fun ω => pastMap κ b jumps w E (ℓ + 1) ω i := (measurable_pi_apply i).comp hpm
  by_cases hi : (i : ℕ) < ℓ
  · have e : (fun ω => pastMap κ b jumps (capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ω i) =
        fun ω => pastMap κ b jumps w E (ℓ + 1) ω i := by
      funext ω
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞)) (fun j => E j ω) (ℓ + 1)).2.2.1 i) =
        readRec ((ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.1 i)
      rw [retained_run_succ_of_lt _ _ hi, retained_run_succ_of_lt _ _ hi, run_capSpec_of_le hℓ _ le_rfl]
    rw [e]
    exact hp
  · have hiℓ : (i : ℕ) = ℓ := le_antisymm (Nat.lt_succ_iff.1 i.2) (not_lt.1 hi)
    have e : (fun ω => pastMap κ b jumps (capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ω i) =
        capRec τ ∘ fun ω => pastMap κ b jumps w E (ℓ + 1) ω i := by
      funext ω
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞)) (fun j => E j ω) (ℓ + 1)).2.2.1 i) =
        capRec τ (readRec ((ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.1 i))
      rw [hiℓ, retained_run_succ_self, retained_run_succ_self, launches_run_capSpec_succ hℓ hwℓ]
      have hT : instrTime w ℓ = ⊤ := by simp only [instrTime, hwℓ]
      rw [instrTime_capSpec hℓ, hT]
      split_ifs
      · simp [capRec, readRec]
      · exact readRec_retOf_cap τ _
    rw [e]
    exact (measurable_capRec τ).comp hp

end Past

/-! ### The prefix lies in the walk -/

section Inside

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ}

/-- Recorded pieces stay recorded. -/
theorem mem_pieces_run_mono (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ} {p : WalkBdry.Piece}
    (hp : p ∈ (ExplState.run κ b jumps spec D n).1) : ∀ m, n ≤ m → p ∈ (ExplState.run κ b jumps spec D m).1 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hp
  | succ m _ ih =>
    rcases hl : (ExplState.run κ b jumps spec D (m + 1)).2.2.2.1 m with _ | ⟨c, θ'⟩
    · rw [GW1P.pieces_run_succ_of_noLaunch spec D hl]; exact ih
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hl
      rw [he, CounterflowRange.pieces_launch]
      exact List.mem_append_left _ ih

/-- **The prefix lies in the walk**: the explored set of the capped program after `ℓ + 1` instructions is contained
in the program's range in `ℍ` (instruction `ℓ` an unstopped angle-`θ` flow, regular driver). -/
theorem stageSet_capSpec_subset_walkSet {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (hℓ : ℓ < w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (hreg : IsRegularDriver (E ℓ ω)) (τ : ℝ≥0) :
    WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1) ω ⊆ WalkLaw.walkSet κ b jumps w E ω := by
  rw [WalkLaw.walkSet_eq_stageSet]
  rintro z ⟨hz, hzH⟩
  refine ⟨?_, hzH⟩
  simp only [mem_iUnion, exists_prop] at hz ⊢
  obtain ⟨p, hp, hzp⟩ := hz
  have hmono : ∀ q ∈ (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).1,
      q ∈ (ExplState.run κ b jumps w (fun j => E j ω) w.2.2.length).1 := fun q hq =>
    mem_pieces_run_mono w _ hq _ hℓ
  rcases hl : (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ with _ | ⟨c, θ'⟩
  · have hl' : (ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = none := by
      rw [launches_run_capSpec_succ hℓ.le hwℓ]; exact hl
    rw [GW1P.pieces_run_succ_of_noLaunch _ _ hl', run_capSpec_of_le hℓ.le _ le_rfl] at hp
    exact ⟨p, mem_pieces_run_mono w _ hp _ hℓ.le, hzp⟩
  · rw [pieces_run_capSpec_succ hℓ.le hwℓ _ hl] at hp
    rcases List.mem_append.1 hp with hp | hp
    · exact ⟨p, mem_pieces_run_mono w _ hp _ hℓ.le, hzp⟩
    · rw [List.mem_singleton] at hp
      subst hp
      -- the full piece is recorded
      obtain ⟨-, he, -⟩ := eq_launch_of_launches w (fun j => E j ω) hl
      have hT : instrTime w ℓ = ⊤ := by simp only [instrTime, hwℓ]
      have hfull : recPiece (ExplState.run κ b jumps w (fun j => E j ω) ℓ) (E ℓ ω) ⊤ ∈
          (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).1 := by
        rw [he, CounterflowRange.pieces_launch, hT]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      refine ⟨_, hmono _ hfull, ?_⟩
      by_cases hτ : (τ : ℝ≥0∞) < min ⊤ (E ℓ ω).2
      · have e := tipSet_recPiece (ExplState.run κ b jumps w (fun j => E j ω) ℓ) hreg hτ
        rw [← e] at hzp
        obtain ⟨t, ht, hlim⟩ := hzp
        exact ⟨t, ht.trans (le_of_lt hτ), hlim⟩
      · have heq : recPiece (ExplState.run κ b jumps w (fun j => E j ω) ℓ) (E ℓ ω) τ =
            recPiece (ExplState.run κ b jumps w (fun j => E j ω) ℓ) (E ℓ ω) ⊤ := by
          have h1 : min (τ : ℝ≥0∞) (E ℓ ω).2 = (E ℓ ω).2 := min_eq_right (by simpa using not_lt.1 hτ)
          simp only [recPiece, h1, le_top, min_eq_right]
        rw [heq] at hzp
        exact hzp

/-- **Piece regularity passes to the capped program.** -/
theorem pieceRegular_capSpec (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hℓ : ℓ ≤ w.2.2.length)
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤)))
    (hreg : ∀ (k : ℕ) (c : Chart) (θ' : ℝ), (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime w k) (D k).2)) (τ : ℝ≥0) :
    ∀ (k : ℕ) (c : Chart) (θ' : ℝ), (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (capSpec w ℓ θ τ) k) (D k).2) := by
  intro k c θ' hl
  rcases lt_trichotomy k ℓ with hk | rfl | hk
  · rw [run_capSpec_of_le hℓ _ (Nat.succ_le_of_lt hk)] at hl
    rw [instrTime_capSpec_of_lt hk hℓ]
    exact hreg k c θ' hl
  · rw [launches_run_capSpec_succ hℓ hwℓ] at hl
    have h := hreg k c θ' hl
    have hT : instrTime w k = ⊤ := by simp only [instrTime, hwℓ]
    rw [hT] at h
    rw [instrTime_capSpec hℓ]
    obtain ⟨h0, hc, α, hα, -⟩ := h
    have hle : min (τ : ℝ≥0∞) (D k).2 ≤ min ⊤ (D k).2 := min_le_min le_top le_rfl
    refine ⟨h0, hc.mono fun s hs => le_trans hs hle, α, ⟨hα.1, hα.2.1.mono fun s hs => le_trans hs hle,
      fun s hs => hα.2.2 s (lt_of_lt_of_le hs hle)⟩, fun htop => ?_⟩
    exact absurd htop (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
  · rw [run_capSpec_of_ge hℓ _ (by omega : ℓ + 1 ≤ k + 1), launches_run_of_le _ _ (Nat.succ_le_of_lt hk)] at hl
    exact absurd hl (by simp)

end Inside

end InteractingSLE.Theorem14.WalkSide
