/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas

/-!
# Theorem 1.4: the past of a boundary walk is a marked local set, with clause (i) up to null sets (R58)

Packet PROVE-T14-WALKLAW3. Ruling R58: clause (i) of `WalkLaw.WalkMarkedLocalRegStatement` (the avoidance events of the
walk are events of its retained past) is stated and used up to null sets. Here:

* **`WalkMarkedLocalRegAEStatement θ right`**: `WalkMarkedLocalRegStatement` with clause (i) in the null completion
  `aeSigma (pastSigma …) P`;
* **`exists_version_of_aeSigma`**: a random relatively closed subset of `ℍ` whose avoidance events are events of `𝒢`
  up to null sets has an almost surely equal version whose avoidance events are events of `𝒢` (a countable basis and
  compactness of closed balls);
* `IsHistoryAvoidanceLocal.congr_ae`, `IsHistoryAvoidanceLocalOff.congr_ae`: the marked criteria do not see null
  modifications of the random set;
* **`walkMarkedLocalRegAEStatement_of_kernel`**: `PastDetRegStatement` and the per-stage kernel input
  `WalkStageKernelLocalStatement θ right` give `WalkMarkedLocalRegAEStatement θ right` (the measurability stage input
  is proved, `walkStageAvoidMeasAEStatement`); the stage iteration `isHistoryAvoidanceLocal_of_stages` runs on the
  measurable versions of the explored sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets Exist.Staged Exist.StagedLaw

/-! ### Null modifications -/

section Congr

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The marked criterion does not see null modifications of the set.** -/
theorem isHistoryAvoidanceLocal_congr_ae {A A' : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hAA : ∀ᵐ ω ∂P, A ω = A' ω) (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A h P) :
    WholeField.IsHistoryAvoidanceLocal ℋ A' h P := by
  intro U G hUH hG hd F hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F hF
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hAA] with ω hω
  simp only [mem_inter_iff, mem_ofPred_eq, hω]

/-- **The marked criterion off a set does not see null modifications of the new set.** -/
theorem isHistoryAvoidanceLocalOff_congr_ae {K : Set ℂ} {B B' : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    {Q : Measure Ω} (hBB : ∀ᵐ ω ∂Q, B ω = B' ω) (hloc : IsHistoryAvoidanceLocalOff ℋ K B h Q) :
    IsHistoryAvoidanceLocalOff ℋ K B' h Q := by
  intro U G hUH hKU hG hd F hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hKU hG hd F hF
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hBB] with ω hω
  simp only [mem_inter_iff, mem_ofPred_eq, hω]

end Congr

/-! ### A measurable version of a random relatively closed set -/

section Version

/-- Every point of an open set lies in a closed ball inside it with centre in a fixed dense set and rational
radius. -/
theorem exists_closedBall_subset_of_mem {D : Set ℂ} (hD : Dense D) {U : Set ℂ} (hU : IsOpen U) {z : ℂ}
    (hz : z ∈ U) : ∃ c ∈ D, ∃ r : ℚ, z ∈ closedBall c (r : ℝ) ∧ closedBall c (r : ℝ) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨c, hcD, hcz⟩ := hD.exists_dist_lt z (by positivity : 0 < ε / 3)
  have hlt : dist z c < ε - dist z c := by linarith
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
  refine ⟨c, hcD, r, mem_closedBall.2 hr1.le, fun w hw => hball ?_⟩
  rw [mem_ball]
  calc dist w z ≤ dist w c + dist c z := dist_triangle _ _ _
    _ < ε := by rw [dist_comm c z]; linarith [mem_closedBall.1 hw]

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A measurable version of a random relatively closed subset of `ℍ`.** If the avoidance events of `A` (a random
subset of `ℍ`, almost surely relatively closed) are events of `𝒢` up to `P`-null sets, then an almost surely equal
random subset of `ℍ` has avoidance events in `𝒢`. -/
theorem exists_version_of_aeSigma {A : Ω → Set ℂ} (hAH : ∀ ω, A ω ⊆ H) (hAo : ∀ᵐ ω ∂P, IsOpen (H \ A ω))
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[aeSigma 𝒢 P] {ω | Disjoint (A ω) U}) :
    ∃ A' : Ω → Set ℂ, (∀ ω, A' ω ⊆ H) ∧ (∀ᵐ ω ∂P, A' ω = A ω) ∧
      ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (A' ω) U} := by
  classical
  obtain ⟨𝔅, h𝔅c, -, h𝔅⟩ := TopologicalSpace.exists_countable_basis ℂ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  set 𝔅H : Set (Set ℂ) := {B | B ∈ 𝔅 ∧ B ⊆ H} with h𝔅H
  have h𝔅Hc : 𝔅H.Countable := h𝔅c.mono fun _ hB => hB.1
  have : Countable 𝔅H := h𝔅Hc.to_subtype
  have : Countable D := hDc.to_subtype
  have hBo : ∀ B : 𝔅H, IsOpen (B : Set ℂ) := fun B => h𝔅.isOpen B.2.1
  choose G hGm hGe using fun B : 𝔅H => hA ⟨B, hBo B⟩ B.2.2
  set V : Ω → Set ℂ := fun ω => ⋃ (B : 𝔅H) (_ : ω ∈ G B), (B : Set ℂ) with hVdef
  refine ⟨fun ω => H \ V ω, fun ω => sdiff_subset, ?_, fun U hUH => ?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ B : 𝔅H, (ω ∈ {ω | Disjoint (A ω) (B : Set ℂ)}) = (ω ∈ G B) :=
      ae_all_iff.2 fun B => hGe B
    filter_upwards [hall, hAo] with ω hω hωo
    have hV : V ω = H \ A ω := by
      ext z
      simp only [hVdef, mem_iUnion, exists_prop, Set.mem_sdiff]
      constructor
      · rintro ⟨B, hB, hzB⟩
        rw [← hω B] at hB
        exact ⟨B.2.2 hzB, fun hzA => Set.disjoint_left.1 hB hzA hzB⟩
      · rintro ⟨hzH, hzA⟩
        obtain ⟨B, hB𝔅, hzB, hBsub⟩ := h𝔅.exists_subset_of_mem_open
          (show z ∈ H \ A ω from ⟨hzH, hzA⟩) hωo
        refine ⟨⟨B, hB𝔅, fun w hw => (hBsub hw).1⟩, ?_, hzB⟩
        rw [← hω]
        exact Set.disjoint_left.2 fun w hwA hwB => (hBsub hwB).2 hwA
    rw [hV]
    ext z
    simp only [Set.mem_sdiff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun hz => ⟨hAH ω hz, fun _ => hz⟩⟩
  · -- the avoidance event is a countable intersection of finite covering events
    have e : {ω | Disjoint (H \ V ω) U} =
        ⋂ (p : {p : D × ℚ // closedBall (p.1 : ℂ) (p.2 : ℝ) ⊆ U}),
          ⋃ (F : {F : Finset 𝔅H // closedBall (p.1.1 : ℂ) (p.1.2 : ℝ) ⊆ ⋃ B ∈ F, (B : Set ℂ)}),
            ⋂ B ∈ F.1, G B := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
      constructor
      · intro hd p
        have hKV : closedBall (p.1.1 : ℂ) (p.1.2 : ℝ) ⊆ ⋃ (B : {B : 𝔅H // ω ∈ G B}), (B.1 : Set ℂ) := by
          intro z hz
          have hzU := p.2 hz
          have hzV : z ∈ V ω := by
            by_contra hzV
            exact Set.disjoint_left.1 hd ⟨hUH hzU, hzV⟩ hzU
          simp only [hVdef, mem_iUnion, exists_prop] at hzV
          obtain ⟨B, hB, hzB⟩ := hzV
          exact mem_iUnion.2 ⟨⟨B, hB⟩, hzB⟩
        obtain ⟨F, hF⟩ := (isCompact_closedBall _ _).elim_finite_subcover
          (fun B : {B : 𝔅H // ω ∈ G B} => (B.1 : Set ℂ)) (fun B => hBo B.1) hKV
        refine ⟨⟨F.map ⟨Subtype.val, Subtype.val_injective⟩, fun z hz => ?_⟩, ?_⟩
        · obtain ⟨B, hBF, hzB⟩ := mem_iUnion₂.1 (hF hz)
          exact mem_iUnion₂.2 ⟨B.1, Finset.mem_map_of_mem _ hBF, hzB⟩
        · intro B hB
          obtain ⟨B', -, rfl⟩ := Finset.mem_map.1 hB
          exact B'.2
      · intro h
        refine Set.disjoint_left.2 fun z hz hzU => hz.2 ?_
        obtain ⟨c, hcD, r, hzc, hcU⟩ := exists_closedBall_subset_of_mem hDd U.isOpen hzU
        obtain ⟨F, hF⟩ := h ⟨(⟨c, hcD⟩, r), hcU⟩
        obtain ⟨B, hBF, hzB⟩ := mem_iUnion₂.1 (F.2 hzc)
        simp only [hVdef, mem_iUnion, exists_prop]
        exact ⟨B, hF B hBF, hzB⟩
    rw [e]
    exact MeasurableSet.iInter fun p => MeasurableSet.iUnion fun F =>
      Finset.measurableSet_biInter _ fun B _ => hGm B

end Version

/-! ### The explored sets stage by stage -/

section Stages

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
theorem stageSet_mono (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) {j k : ℕ} (hjk : j ≤ k) :
    stageSet κ b jumps spec E j ω ⊆ stageSet κ b jumps spec E k ω := by
  induction k, hjk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih => exact ih.trans (stageSet_subset_succ κ b jumps spec E k ω)

/-- **The complement in `ℍ` of the explored set after `k` instructions is almost surely open.** -/
theorem ae_isOpen_H_diff_stageSet {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω ∂P, IsOpen (H \ stageSet κ b jumps spec E k ω) := by
  filter_upwards [hR.ae_pieceRegular] with ω hω
  have hcl := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hω k).2
  set l := (ExplState.run κ b jumps spec (fun j => E j ω) k).1 with hl
  have hS : IsClosed (⋃ p ∈ l, p.1.tipSet p.2.1 p.2.2) :=
    (List.finite_toSet l).isClosed_biUnion fun p hp => hcl p hp
  have e : H \ stageSet κ b jumps spec E k ω = H \ ⋃ p ∈ l, p.1.tipSet p.2.1 p.2.2 := by
    rw [stageSet]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff hS

end Stages

/-! ### The walk statement with clause (i) up to null sets -/

/-- **`WalkMarkedLocalRegStatement` with clause (i) up to null sets (ruling R58).** As `WalkMarkedLocalRegStatement`,
except that every avoidance event `{walk ∩ U = ∅}` of an open `U ⊆ ℍ` is an event of the retained past `𝒢` only up to
`P`-null sets (it lies in `aeSigma 𝒢 P`). -/
def WalkMarkedLocalRegAEStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
        MeasurableSet[aeSigma (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right)
            (E (boundaryWalkSpec b jumps θ right)) (boundaryWalkSpec b jumps θ right).2.2.length) P]
          {ω | Disjoint (walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
            (E (boundaryWalkSpec b jumps θ right)) ω) U}) ∧
      (∀ᵐ ω ∂P, IsOpen (H \ walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
        (E (boundaryWalkSpec b jumps θ right)) ω)) ∧
      WholeField.IsHistoryAvoidanceLocal
        (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right))
          (boundaryWalkSpec b jumps θ right).2.2.length)
        (walkSet κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)))
        (WholeField.centredField h u₀) P

/-- The exact statement implies the R58 statement. -/
theorem walkMarkedLocalRegAEStatement_of_exact {θ : ℝ} {right : Bool}
    (hex : WalkMarkedLocalRegStatement.{u} θ right) : WalkMarkedLocalRegAEStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ hu₀
  obtain ⟨h1, h2, h3⟩ := hex κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀
  exact ⟨fun U hU => le_aeSigma _ P _ (h1 U hU), h2, h3⟩

/-- **The past of a boundary walk is a marked local set, clause (i) up to null sets (Part D.2, ruling R58), from the
per-stage kernel input.** For an angle in `[−π/2, π/2]`, the determination of the retained past
(`PastDetRegStatement`, proved in `WalkPastDet` from Theorems 1.2–1.3) and the conditional locality of each new piece
(`WalkStageKernelLocalStatement θ right`) give `WalkMarkedLocalRegAEStatement θ right`. The measurability stage input
is `walkStageAvoidMeasAEStatement`; the stages are glued (`isHistoryAvoidanceLocal_of_stages`) on measurable versions
of the explored sets (`exists_version_of_aeSigma`). -/
theorem walkMarkedLocalRegAEStatement_of_kernel {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {right : Bool} (hdet : PastDetRegStatement.{u}) (hker : WalkStageKernelLocalStatement.{u} θ right) :
    WalkMarkedLocalRegAEStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ hu₀
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps θ right).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hEw := hE w hw
  have hRw := hR w hw
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hmeas := walkStageAvoidMeasAEStatement hθ right κ hκ hκ4 b jumps hb P h hh E hE hR hreg
  -- measurable versions of the explored sets
  choose A' hA'H hA'ae hA'm using fun k => exists_version_of_aeSigma (P := P)
    (𝒢 := pastSigma κ b jumps w (E w) k) (A := stageSet κ b jumps w (E w) k)
    (fun ω => stageSet_subset_H κ b jumps w (E w) k ω) (ae_isOpen_H_diff_stageSet hRw k) (hmeas k)
  set A'' : ℕ → Ω → Set ℂ := fun k ω => ⋃ j ∈ Finset.range (k + 1), A' j ω with hA''def
  have hA''m : ∀ k (U : Opens ℂ), (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps w (E w) k] {ω | Disjoint (A'' k ω) U} := by
    intro k U hU
    have e : {ω | Disjoint (A'' k ω) U} = ⋂ j ∈ Finset.range (k + 1), {ω | Disjoint (A' j ω) U} := by
      ext ω
      simp only [hA''def, mem_ofPred_eq, mem_iInter, Set.disjoint_iUnion_left]
    rw [e]
    exact Finset.measurableSet_biInter _ fun j hj =>
      pastSigma_mono (κ := κ) (b := b) (jumps := jumps) w (E w)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) _ (hA'm j U hU)
  have hA'all : ∀ᵐ ω ∂P, ∀ j, A' j ω = stageSet κ b jumps w (E w) j ω := ae_all_iff.2 hA'ae
  have hA''ae : ∀ k, ∀ᵐ ω ∂P, A'' k ω = stageSet κ b jumps w (E w) k ω := fun k => by
    filter_upwards [hA'all] with ω hω
    simp only [hA''def, hω]
    refine subset_antisymm (iUnion₂_subset fun j hj =>
      stageSet_mono w (E w) ω (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) ?_
    exact subset_iUnion₂_of_subset k (Finset.mem_range.2 (Nat.lt_succ_self k)) subset_rfl
  have hsub : ∀ k ω, A'' k ω ⊆ A'' (k + 1) ω := fun k ω =>
    iUnion₂_subset fun j hj => subset_iUnion₂_of_subset j
      (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hj))) subset_rfl
  have hall := isHistoryAvoidanceLocal_of_stages (P := P) (𝒢 := fun k => pastSigma κ b jumps w (E w) k)
    (A := A'') hh0 (fun k => hEw.2.1 k)
    (fun k => pastSigma_mono (κ := κ) (b := b) (jumps := jumps) w (E w) (Nat.le_succ k)) hsub hA''m
    (fun k => by
      obtain ⟨f, hf, hp⟩ := hdet κ hκ hκ4 b jumps hb P h hh w (E w) hEw hRw k
      exact pastSigma_le_aeSigma_centred hf hp u₀)
    (by
      refine isHistoryAvoidanceLocal_congr_ae (A := fun _ => (∅ : Set ℂ)) ?_
        (isHistoryAvoidanceLocal_empty_of_trivial (WholeField.measurable_centredField hh.1 u₀)
          (pastSigma_zero_trivial κ b jumps w (E w)))
      filter_upwards [hA''ae 0] with ω hω
      rw [hω, stageSet_zero])
    (fun k => by
      filter_upwards [hker κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀ k,
        CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) w
          (fun j _ ω => hreg w j ω) (hEw.2.1 k) le_rfl, hA''ae k,
        KernelTower.ae_ae_condExpKernel_of_ae (P := P) (hEw.2.1 k) (hA''ae (k + 1))] with ω₀ hω₀ hfr h0 h1
      have hfr' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀),
          stageSet κ b jumps w (E w) k ω = stageSet κ b jumps w (E w) k ω₀ := by
        filter_upwards [hfr] with ω hω
        simp only [stageSet, hω]
      have := hω₀.union_frozen hfr'
      have e : (fun ω => stageSet κ b jumps w (E w) k ω ∪ pieceSet κ b jumps w (E w) k ω) =
          stageSet κ b jumps w (E w) (k + 1) :=
        funext fun ω => (stageSet_succ κ b jumps w (E w) k ω).symm
      rw [e] at this
      rw [h0]
      refine isHistoryAvoidanceLocalOff_congr_ae ?_ this
      filter_upwards [h1] with ω hω
      exact hω.symm)
  have e : walkSet κ b jumps w (E w) = stageSet κ b jumps w (E w) w.2.2.length :=
    funext fun ω => walkSet_eq_stageSet κ b jumps w (E w) ω
  refine ⟨fun U hU => ?_, ae_isOpen_H_diff_walkSet hRw, ?_⟩
  · rw [e]
    exact hmeas _ U hU
  · rw [e]
    exact isHistoryAvoidanceLocal_congr_ae (hA''ae _) (hall _)

/-- The right walk (`θ = −π/2`). -/
theorem walkMarkedLocalRegAEStatement_right (hdet : PastDetRegStatement.{u})
    (hker : WalkStageKernelLocalStatement.{u} (-(Real.pi / 2)) true) :
    WalkMarkedLocalRegAEStatement.{u} (-(Real.pi / 2)) true :=
  walkMarkedLocalRegAEStatement_of_kernel ⟨le_rfl, by linarith [Real.pi_pos]⟩ hdet hker

/-- The left walk (`θ = π/2`). -/
theorem walkMarkedLocalRegAEStatement_left (hdet : PastDetRegStatement.{u})
    (hker : WalkStageKernelLocalStatement.{u} (Real.pi / 2) false) :
    WalkMarkedLocalRegAEStatement.{u} (Real.pi / 2) false :=
  walkMarkedLocalRegAEStatement_of_kernel ⟨by linarith [Real.pi_pos], le_rfl⟩ hdet hker

end WalkLaw

end Theorem14

end InteractingSLE
