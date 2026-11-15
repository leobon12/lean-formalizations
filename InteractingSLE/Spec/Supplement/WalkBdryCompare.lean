/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkBdryDefs
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk
import InteractingSLE.Spec.Sec7.PocketStopSideFinalComparison
import InteractingSLE.Spec.Sec7.Lemma78MeanReal
import InteractingSLE.WangWu.ReverseContactGood
import InteractingSLE.WangWu.PrefixLocalSides

/-!
# Theorem 1.4's walk leaves: one walk against the union, and the two walks against each other

Packet PROVE-T14-WALKBDRY. Lemma GW3, proof (p. 636): "The nested marked collar comparison … preserve[s] that germ";
Theorem GW4, proof (p. 637): "Apply the marked collar comparison on a compact proper ordinary subarc." The comparison is
Proposition 3.8 for two marked local sets (`Sec7.PocketStopSide.ae_tendsto_sub_of_marked_union`): the difference of
the two local-set means tends to `0` at every point near which the two sets agree. Here its hypotheses are supplied for
the boundary walks:

* **`exists_walkVersion`**: a measurable version of one walk, a local set of the centred field whose hitting events are
  events of the walk's retained past (Theorems 1.2–1.3, through PROVE-T14-WALK's marked locality);
* **`ae_unbounded_lowerUnion_walk`**, **`ae_unbounded_lowerUnion_union`**: the lower unions of a walk and of the union
  of the two walks have only unbounded components (each walk is the range of a proper curve from `0`);
* **`hitting_comap_le_aeSigma_jointPast`**: the hitting σ-algebra of any version of the union is in the joined past up
  to null sets;
* **`ae_tendsto_sub_of_walkUnion`**: the marked-union comparison for two random sets whose union is almost surely the
  union of the walks and whose hitting events are in the joined past up to null sets.

R48: Theorems 1.2–1.3 are used as hypotheses; these results serve Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkBdry

open WalkLaw GW3Between LocalSets WalkMean

/-! ### A measurable version of one walk -/

section Version

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u₀ : ℂ → ℝ}

/-- **A measurable version of one boundary walk**: a random set in `ℍ`, almost surely the walk's range, whose hitting
events are events of the walk's retained past, and which is a local set of the centred field. -/
theorem exists_walkVersion (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg' : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω))
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A : Ω → Set ℂ, (∀ ω, A ω ⊆ H) ∧
      (∀ᵐ ω ∂P, A ω = walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
        (E (boundaryWalkSpec b jumps θ right)) ω) ∧
      Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right))
        (boundaryWalkSpec b jumps θ right).2.2.length, hittingSigma] A ∧
      Measurable[mΩ, hittingSigma] A ∧ IsLocalSet A (WholeField.centredField h u₀) P := by
  have hpr : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps θ right).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  obtain ⟨hAev, hAo, hloc⟩ := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 hθ right
    κ hκ hκ4 b jumps hb P h hh E hE hreg hreg' u₀ hu₀
  obtain ⟨A, hAH, hAae, hAm⟩ := exists_version_of_aeSigma (fun ω => walkSet_subset_H _ _ _ _ _ ω) hAo hAev
  have hle : pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right))
      (boundaryWalkSpec b jumps θ right).2.2.length ≤ mΩ := (hE _ hpr).2.1 _
  have hAmp : Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps θ right)
      (E (boundaryWalkSpec b jumps θ right)) (boundaryWalkSpec b jumps θ right).2.2.length, hittingSigma] A :=
    WalkMean.measurable_hitting_of_avoid (mΩ := pastSigma κ b jumps (boundaryWalkSpec b jumps θ right)
      (E (boundaryWalkSpec b jumps θ right)) (boundaryWalkSpec b jumps θ right).2.2.length) le_rfl hAm
  have hAm' : Measurable[mΩ, hittingSigma] A := hAmp.mono hle le_rfl
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hloc' := isHistoryAvoidanceLocal_congr_ae (hAae.mono fun ω h => h.symm) hloc
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hAae, hAo] with ω h1 h2
    exact ⟨hAH ω, h1 ▸ h2⟩
  exact ⟨A, hAH, hAae, hAmp, hAm', ((isLocalSet_tfae hh0 hAm' hAc).out 1 4).1 hloc'.isAvoidanceLocal⟩

end Version

/-! ### Unbounded lower unions -/

section Unbounded

/-- The lower union of `S ∩ ℍ` for the range `S` of a proper curve has only unbounded components. -/
theorem unbounded_lowerUnion_of_range {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {S : Set ℂ}
    (hS : S = range γ) :
    ∀ z ∈ lowerUnion (S ∩ H), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (S ∩ H)) z) := by
  rw [WangWu.lowerUnion_inter_H]
  refine WangWu.not_isBounded_lowerUnion_of_isPreconnected ?_ ?_
  · rw [hS]; exact isPreconnected_range hγ.1
  · rw [hS]
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    obtain ⟨t, ht⟩ := (hγ.2.2.2.eventually (eventually_gt_atTop R)).exists
    have := hR (mem_range_self t)
    rw [mem_closedBall, dist_zero_right] at this
    linarith

/-- The lower union of the union in `ℍ` of the ranges of two proper curves from `0` has only unbounded components. -/
theorem unbounded_lowerUnion_of_range₂ {γ₁ γ₂ : ℝ≥0 → ℂ} (hγ₁ : Supp9B.IsProperCurve γ₁)
    (hγ₂ : Supp9B.IsProperCurve γ₂) (h₁₀ : γ₁ 0 = 0) (h₂₀ : γ₂ 0 = 0) {S₁ S₂ : Set ℂ}
    (hS₁ : S₁ = range γ₁) (hS₂ : S₂ = range γ₂) :
    ∀ z ∈ lowerUnion (S₁ ∩ H ∪ S₂ ∩ H),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (S₁ ∩ H ∪ S₂ ∩ H)) z) := by
  rw [← union_inter_distrib_right, WangWu.lowerUnion_inter_H]
  refine WangWu.not_isBounded_lowerUnion_of_isPreconnected ?_ ?_
  · rw [hS₁, hS₂]
    refine (isPreconnected_range hγ₁.1).union 0 ⟨0, h₁₀⟩ ⟨0, h₂₀⟩ (isPreconnected_range hγ₂.1)
  · intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    obtain ⟨t, ht⟩ := (hγ₁.2.2.2.eventually (eventually_gt_atTop R)).exists
    have := hR (Or.inl (hS₁ ▸ mem_range_self t))
    rw [mem_closedBall, dist_zero_right] at this
    linarith

end Unbounded

/-! ### The hitting σ-algebra of a version of the union -/

section Hitting

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- If every avoidance event of `A` is an event of `𝒢` up to null sets, so is every hitting event. -/
theorem hitting_comap_le_aeSigma {𝒢 : MeasurableSpace Ω} {A : Ω → Set ℂ}
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[aeSigma 𝒢 P] {ω | Disjoint (A ω) U}) :
    MeasurableSpace.comap A hittingSigma ≤ aeSigma 𝒢 P := by
  rw [hittingSigma, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨_, ⟨V, hVo, hVH, rfl⟩, rfl⟩
  have e : A ⁻¹' {B | (B ∩ V).Nonempty} = {ω | Disjoint (A ω) ((⟨V, hVo⟩ : Opens ℂ) : Set ℂ)}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
    rfl
  rw [e]
  exact (hA ⟨V, hVo⟩ hVH).compl

/-- Avoidance events in `aeSigma 𝒢 P` pass to an almost surely equal random set. -/
theorem avoid_aeSigma_congr {𝒢 : MeasurableSpace Ω} {A A' : Ω → Set ℂ} (he : ∀ᵐ ω ∂P, A' ω = A ω)
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[aeSigma 𝒢 P] {ω | Disjoint (A ω) U}) :
    ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[aeSigma 𝒢 P] {ω | Disjoint (A' ω) U} := by
  intro U hU
  obtain ⟨G, hG, hGe⟩ := hA U hU
  refine ⟨G, hG, EventuallyEq.trans ?_ hGe⟩
  filter_upwards [he] with ω hω
  simp only [hω]

end Hitting

/-! ### The comparison for the walks -/

section Compare

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u₀ : ℂ → ℝ}

/-- **Proposition 3.8 for two random sets whose union is the union of the walks**: if `A`, `B` are measurable local
sets of the centred field whose hitting events are events of the joined past up to null sets, whose union is almost
surely the union of the two walks, and whose lower unions have only unbounded components, then almost surely, for
harmonic representatives `vA`, `vB` of their means, `vA − vB → 0` at every point near which `A` and `B` agree. -/
theorem ae_tendsto_sub_of_walkUnion (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg' : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω))
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A B : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hBm : Measurable[mΩ, hittingSigma] B)
    (hAloc : IsLocalSet A (WholeField.centredField h u₀) P) (hBloc : IsLocalSet B (WholeField.centredField h u₀) P)
    (hAJ : MeasurableSpace.comap A hittingSigma ≤ aeSigma (jointPast κ b jumps E) P)
    (hBJ : MeasurableSpace.comap B hittingSigma ≤ aeSigma (jointPast κ b jumps E) P)
    (hU : ∀ᵐ ω ∂P, A ω ∪ B ω = walkUnionSet κ b jumps E ω)
    (hAunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hBunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z))
    {gA gB : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean A (WholeField.centredField h u₀) P gA)
    (hgB : IsLocalSetMean B (WholeField.centredField h u₀) P gB) :
    ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = ∫ z, vB z * φ z) →
      ∀ p : ℂ, p ∈ A ω ∪ {z : ℂ | z.im = 0} → p ∈ B ω ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, B ω ∩ ball p r ⊆ A ω) → (∃ r > 0, A ω ∩ ball p r ⊆ B ω) →
      Tendsto (fun z => vA z - vB z) (𝓝[H \ (A ω ∪ B ω)] p) (𝓝 0) := by
  have hpi := Real.pi_pos
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  have hRl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith⟩ true
  have hLl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := Real.pi / 2)
    ⟨by linarith, le_rfl⟩ false
  obtain ⟨-, -, -, hlocU⟩ := walkUnion_markedAE hdet hRl hLl hκ hκ4 hb hh hE hreg hreg' hu₀
  have hloc' : WholeField.IsHistoryAvoidanceLocal (jointPast κ b jumps E) (fun ω => A ω ∪ B ω)
      (WholeField.centredField h u₀) P :=
    isHistoryAvoidanceLocal_congr_ae (hU.mono fun ω h => h.symm) hlocU
  have hmarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap A hittingSigma ⊔ MeasurableSpace.comap B hittingSigma)
      (fun ω => A ω ∪ B ω) (WholeField.centredField h u₀) P :=
    isHistoryAvoidanceLocal_of_le_aeSigma (sup_le hAJ hBJ) hloc'
  exact Sec7.PocketStopSide.ae_tendsto_sub_of_marked_union hh0 hAm hBm hAloc hBloc hmarked hAunb hBunb hgA hgB

end Compare

end InteractingSLE.Theorem14.WalkBdry
