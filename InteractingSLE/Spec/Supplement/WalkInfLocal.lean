/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfLaunch

/-!
# Theorem 1.4's walk leaves: the capped prefix's marked locality (input (A) of `walkPrefixSideStatement_of_prefix`)

Packet PROVE-T14-WALKINF.

* `kernelLocal_of_launchLocal`: the per-stage kernel step of `WalkLaw.walkStageKernelLocalStatement_of_launch`, for any
  staged program;
* `markedLocalAE_of_kernel`: the stage gluing of `WalkLaw.walkMarkedLocalRegAEStatement_of_kernel`, for any staged
  program, at every number of instructions (R58 form);
* **`PrefixMarkedLocalOnStatement θ right`**: `WalkSide.PrefixMarkedLocalStatement θ right` for the instructions that
  are unstopped angle-`θ` flows of the walk;
* **`prefixMarkedLocalOnStatement_of_thm12_thm13`**: its proof from Theorems 1.2 (parametric) and 1.3 (R48: Theorem
  1.4 only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkInf

open LocalSets Exist.Staged Exist.StagedLaw Sec6 WalkSide

/-! ### The per-stage step and the gluing, for any staged program -/

section Generic

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The per-stage kernel input from the launched piece**, for any staged program: if the piece of instruction `k` is,
under the stage kernel, marked local off the explored set for the marks of its record, it is so for the retained past
after `k`. -/
theorem kernelLocal_of_launchLocal (hhm : Measurable h) (u₀ : ℂ → ℝ) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    (hL : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      WalkLaw.IsHistoryAvoidanceLocalOff
        (MeasurableSpace.comap (fun ω => recOf (instrTime spec k) (E k ω)) inferInstance)
        (WalkLaw.stageSet κ b jumps spec E k ω₀) (WalkLaw.pieceSet κ b jumps spec E k)
        (WholeField.centredField h u₀) (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)) :
    ∀ᵐ ω₀ ∂P, WalkLaw.IsHistoryAvoidanceLocalOff (pastSigma κ b jumps spec E (k + 1))
      (WalkLaw.stageSet κ b jumps spec E k ω₀) (WalkLaw.pieceSet κ b jumps spec E k)
      (WholeField.centredField h u₀) (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) := by
  filter_upwards [hL, CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec
    (fun j _ ω => hreg j ω) (hE.2.1 k) le_rfl] with ω₀ hLω hfr
  have hlaunch : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k =
        (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k := by
    filter_upwards [hfr] with ω hω
    rw [launches_run_succ_of_run_eq spec hω]
  have hpast : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E k ω₀ := by
    filter_upwards [hfr] with ω hω
    unfold pastMap
    rw [hω]
  by_cases hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = none
  · refine WalkLaw.isHistoryAvoidanceLocalOff_of_trivial (WholeField.measurable_centredField hhm u₀) ?_ ?_
    · filter_upwards [hlaunch] with ω hω
      simp only [WalkLaw.pieceSet, hω, hl, ↓reduceIte]
    · rintro _ ⟨T, -, rfl⟩
      have hconst : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
          pastMap κ b jumps spec E (k + 1) ω = pastMap κ b jumps spec E (k + 1) ω₀ := by
        filter_upwards [hlaunch, hpast] with ω h1 h2
        rw [WalkLaw.pastMap_succ_eq, WalkLaw.pastMap_succ_eq, h1, h2]
        simp only [hl, ↓reduceIte]
      by_cases hT : pastMap κ b jumps spec E (k + 1) ω₀ ∈ T
      · left
        filter_upwards [hconst] with ω hω
        show pastMap κ b jumps spec E (k + 1) ω ∈ T
        rw [hω]
        exact hT
      · right
        filter_upwards [hconst] with ω hω
        show pastMap κ b jumps spec E (k + 1) ω ∉ T
        rw [hω]
        exact hT
  · refine WalkLaw.isHistoryAvoidanceLocalOff_of_le_aeSigma ?_ (hLω hl)
    rintro _ ⟨T, hT, rfl⟩
    refine ⟨(fun ω => recOf (instrTime spec k) (E k ω)) ⁻¹'
      (WalkLaw.pastSucc (pastMap κ b jumps spec E k ω₀) ⁻¹' T), ⟨_, WalkLaw.measurable_pastSucc _ hT, rfl⟩, ?_⟩
    filter_upwards [hlaunch, hpast] with ω h1 h2
    have e : pastMap κ b jumps spec E (k + 1) ω =
        WalkLaw.pastSucc (pastMap κ b jumps spec E k ω₀) (recOf (instrTime spec k) (E k ω)) := by
      rw [WalkLaw.pastMap_succ_eq, h1, h2]
      simp only [hl, ↓reduceIte]
    change (pastMap κ b jumps spec E (k + 1) ω ∈ T) =
      (WalkLaw.pastSucc (pastMap κ b jumps spec E k ω₀) (recOf (instrTime spec k) (E k ω)) ∈ T)
    rw [e]

/-- **The explored sets of a staged program are marked local sets, clause (i) up to null sets** (the gluing of
`WalkLaw.walkMarkedLocalRegAEStatement_of_kernel`, for any staged program and every number of instructions), from the
determination of the retained pasts by the field and the per-stage kernel locality. -/
theorem markedLocalAE_of_kernel (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hdet : ∀ k, ∃ f : DistOn upperHalfPlaneOpens → PastData k, Measurable f ∧
      pastMap κ b jumps spec E k =ᵐ[P] f ∘ h)
    (hker : ∀ k, ∀ᵐ ω₀ ∂P, WalkLaw.IsHistoryAvoidanceLocalOff (pastSigma κ b jumps spec E (k + 1))
      (WalkLaw.stageSet κ b jumps spec E k ω₀) (WalkLaw.pieceSet κ b jumps spec E k)
      (WholeField.centredField h u₀) (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)) (n : ℕ) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (pastSigma κ b jumps spec E n) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps spec E n ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ WalkLaw.stageSet κ b jumps spec E n ω)) ∧
    WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E n) (WalkLaw.stageSet κ b jumps spec E n)
      (WholeField.centredField h u₀) P := by
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hmeas : ∀ k (U : Opens ℂ), (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (pastSigma κ b jumps spec E k) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps spec E k ω) U} :=
    fun k U hU => WalkLaw.measurableSet_aeSigma_stageSet_avoid hb hE.1 hreg hR hE.2.1 k U.isOpen hU
  -- measurable versions of the explored sets
  choose A' hA'H hA'ae hA'm using fun k => WalkLaw.exists_version_of_aeSigma (P := P)
    (𝒢 := pastSigma κ b jumps spec E k) (A := WalkLaw.stageSet κ b jumps spec E k)
    (fun ω => WalkLaw.stageSet_subset_H κ b jumps spec E k ω) (WalkLaw.ae_isOpen_H_diff_stageSet hR k) (hmeas k)
  set A'' : ℕ → Ω → Set ℂ := fun k ω => ⋃ j ∈ Finset.range (k + 1), A' j ω with hA''def
  have hA''m : ∀ k (U : Opens ℂ), (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps spec E k] {ω | Disjoint (A'' k ω) U} := by
    intro k U hU
    have e : {ω | Disjoint (A'' k ω) U} = ⋂ j ∈ Finset.range (k + 1), {ω | Disjoint (A' j ω) U} := by
      ext ω
      simp only [hA''def, mem_ofPred_eq, mem_iInter, Set.disjoint_iUnion_left]
    rw [e]
    exact Finset.measurableSet_biInter _ fun j hj =>
      pastSigma_mono (κ := κ) (b := b) (jumps := jumps) spec E
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) _ (hA'm j U hU)
  have hA'all : ∀ᵐ ω ∂P, ∀ j, A' j ω = WalkLaw.stageSet κ b jumps spec E j ω := ae_all_iff.2 hA'ae
  have hA''ae : ∀ k, ∀ᵐ ω ∂P, A'' k ω = WalkLaw.stageSet κ b jumps spec E k ω := fun k => by
    filter_upwards [hA'all] with ω hω
    simp only [hA''def, hω]
    refine subset_antisymm (iUnion₂_subset fun j hj =>
      WalkLaw.stageSet_mono spec E ω (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) ?_
    exact subset_iUnion₂_of_subset k (Finset.mem_range.2 (Nat.lt_succ_self k)) subset_rfl
  have hsub : ∀ k ω, A'' k ω ⊆ A'' (k + 1) ω := fun k ω =>
    iUnion₂_subset fun j hj => subset_iUnion₂_of_subset j
      (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hj))) subset_rfl
  have hall := WalkLaw.isHistoryAvoidanceLocal_of_stages (P := P) (𝒢 := fun k => pastSigma κ b jumps spec E k)
    (A := A'') hh0 (fun k => hE.2.1 k)
    (fun k => pastSigma_mono (κ := κ) (b := b) (jumps := jumps) spec E (Nat.le_succ k)) hsub hA''m
    (fun k => by
      obtain ⟨f, hf, hp⟩ := hdet k
      exact WalkLaw.pastSigma_le_aeSigma_centred hf hp u₀)
    (by
      refine WalkLaw.isHistoryAvoidanceLocal_congr_ae (A := fun _ => (∅ : Set ℂ)) ?_
        (WalkLaw.isHistoryAvoidanceLocal_empty_of_trivial (WholeField.measurable_centredField hh.1 u₀)
          (WalkLaw.pastSigma_zero_trivial κ b jumps spec E))
      filter_upwards [hA''ae 0] with ω hω
      rw [hω, WalkLaw.stageSet_zero])
    (fun k => by
      filter_upwards [hker k,
        CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec
          (fun j _ ω => hreg j ω) (hE.2.1 k) le_rfl, hA''ae k,
        KernelTower.ae_ae_condExpKernel_of_ae (P := P) (hE.2.1 k) (hA''ae (k + 1))] with ω₀ hω₀ hfr h0 h1
      have hfr' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
          WalkLaw.stageSet κ b jumps spec E k ω = WalkLaw.stageSet κ b jumps spec E k ω₀ := by
        filter_upwards [hfr] with ω hω
        simp only [WalkLaw.stageSet, hω]
      have := hω₀.union_frozen hfr'
      have e : (fun ω => WalkLaw.stageSet κ b jumps spec E k ω ∪ WalkLaw.pieceSet κ b jumps spec E k ω) =
          WalkLaw.stageSet κ b jumps spec E (k + 1) :=
        funext fun ω => (WalkLaw.stageSet_succ κ b jumps spec E k ω).symm
      rw [e] at this
      rw [h0]
      refine WalkLaw.isHistoryAvoidanceLocalOff_congr_ae ?_ this
      filter_upwards [h1] with ω hω
      exact hω.symm)
  exact ⟨hmeas n, WalkLaw.ae_isOpen_H_diff_stageSet hR n,
    WalkLaw.isHistoryAvoidanceLocal_congr_ae (hA''ae n) (hall n)⟩

end Generic

/-! ### The capped prefix -/

/-- **`WalkSide.PrefixMarkedLocalStatement θ right` at the unstopped angle-`θ` flow instructions of the walk.** For the
setting of `WalkSide.PrefixMarkedLocalStatement`, every instruction `ℓ` of the walk
`w = boundaryWalkSpec b jumps θ right`
that is an unstopped angle-`θ` flow and every own time `τ`: the explored set of the capped program after `ℓ + 1`
instructions has its avoidance events in the capped retained past up to null sets, an open complement almost surely,
and is history-avoidance local for that past (Lemma GW3, proof, p. 636: "Fix proper prefixes of the two selected
arcs"; Part D.2; R58 form). -/
def PrefixMarkedLocalOnStatement (θ : ℝ) (right : Bool) : Prop :=
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
      ℓ < (boundaryWalkSpec b jumps θ right).2.2.length →
      (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) →
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

/-- **The capped prefix of a boundary walk is a history-marked local set** (input (A) of
`WalkSide.walkPrefixSideStatement_of_prefix`, at the instructions its consumer uses), from Theorems 1.2 (parametric)
and 1.3 (R48: Theorem 1.4 only). The stages before `ℓ` are the walk's (`WalkLeaf.launchLocal_of_thm12_thm13`), the
stage `ℓ` is the capped piece (`launchLocalCap_of_thm12_thm13`), no piece follows; the stages are glued
(`markedLocalAE_of_kernel`). -/
theorem prefixMarkedLocalOnStatement_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    PrefixMarkedLocalOnStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ hu₀ ℓ τ hℓ hwℓ
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  set cs := capSpec w ℓ θ (τ : ℝ≥0∞) with hcs
  have hEw := hE w hw
  have hRw := hR w hw
  have hEc : IsStagedHistory κ b jumps P h cs (E w) := isStagedHistory_capSpec hb hEw (hreg w) hℓ hwℓ
  have hRc : StagedPiecesRegular κ b jumps P cs (E w) := stagedPiecesRegular_of_regular h13 hκ hb hEc (hreg w)
  have hdet := fun k => WalkLaw.pastDetRegStatement_of_thm12_thm13 h12p h13 κ hκ hκ4 b jumps hb P h hh cs (E w)
    hEc hRc k
  refine markedLocalAE_of_kernel hb hh hu₀ hEc hRc (hreg w) hdet (fun k => ?_) (ℓ + 1)
  refine kernelLocal_of_launchLocal hh.1 u₀ hEc (hreg w) k ?_
  rcases lt_trichotomy k ℓ with hk | rfl | hk
  · -- a stage of the walk
    refine WalkLeaf.launchLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hEc hRc (hreg w) u₀ k (θ := θ)
      fun θ' t ht => ?_
    rw [capSpec_getElem?_of_lt hk hℓ.le] at ht
    exact WalkLeaf.boundaryWalkSpec_inl ht
  · -- the capped piece
    exact launchLocalCap_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hEw hRw (hreg w) u₀ hℓ hwℓ τ
  · -- no piece after the cap
    refine Eventually.of_forall fun ω₀ hl => absurd ?_ hl
    rw [run_capSpec_of_ge hℓ.le _ (by omega : ℓ + 1 ≤ k + 1), launches_run_of_le _ _ (Nat.succ_le_of_lt hk)]

end InteractingSLE.Theorem14.WalkInf
