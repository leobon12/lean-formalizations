/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3UnionLawProof
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Coupling.WholeFieldMarked
import InteractingSLE.GFF.LocalSets.GermApprox

/-!
# Theorem 1.4: the past of a boundary walk as a marked local set (Part D.2)

Packet PROVE-T14-WALKLAW. Lemma GW1 (specification p. 618–620) and the follow-up note's Part D.2
(`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L771–L832): "in the current hydrodynamic chart, the full
conditional harmonic mean is the canonical finite-piece mean […] and every frozen component keeps its previously
recorded kernel"; "Iterating the conditional Gaussian identities proves the asserted full joined-history law." In the
local-set calculus of the project (Lemma 3.6, Aux. lemma 18) the joined-history law of a walk is the statement that
the walk's range in `ℍ` is a local set of the centred field **marked by its retained history** (`pastSigma` of the
complete program), i.e. satisfies the history-marked avoidance criterion `WholeField.IsHistoryAvoidanceLocal`.

This file records that statement and the field determination of the retained past in the forms the union law of the
two walks consumes (`WalkUnionLaw.lean`):

* `walkSet`: the range of a walk in `ℍ` (its ordinary pieces; the real connectors are not in `ℍ`);
* **`WalkMarkedLocalRegStatement θ right`** (named input, D.2's locality): for the boundary walk at angle `θ`, the
  avoidance events of the walk are events of its retained past, its complement in `ℍ` is open, and the walk is a local
  set of the centred field marked by its retained past;
* **`PastDetRegStatement`** (named input; PROVE-T14-SB7's (a1), `StagedDet.exists_pastMap_eq_comp_field`, in flight):
  the retained past of a staged history is almost surely a Borel function of the field;
* `comap_le_aeSigma_of_ae_eq_comp`, `aeSigma_comap_field_le_centred`, **`pastSigma_le_aeSigma_centred`**: the retained
  past is, up to null sets, an event family of the centred field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

/-! ### The range of a walk in `ℍ` -/

/-- The range in `ℍ` of the staged program `w` run with the drivers `E`: the physical set of the run without its real
points (the original-real connectors). -/
def walkSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (w : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Set ℂ :=
  ExplState.physSet κ b jumps w (fun k => E k ω) ∩ H

theorem walkSet_subset_H (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (w : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : walkSet κ b jumps w E ω ⊆ H :=
  inter_subset_right

/-- The complement in `ℍ` of the union of two walk ranges is the complement of the union of the physical sets. -/
theorem H_diff_walkSet_union (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (w₁ w₂ : ExplSpec)
    (E₁ E₂ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    H \ (walkSet κ b jumps w₁ E₁ ω ∪ walkSet κ b jumps w₂ E₂ ω) =
      H \ (ExplState.physSet κ b jumps w₁ (fun k => E₁ k ω) ∪ ExplState.physSet κ b jumps w₂ (fun k => E₂ k ω)) := by
  ext z
  simp only [walkSet, Set.mem_sdiff, mem_union, mem_inter_iff]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h' => hn (h'.elim (fun h1 => Or.inl ⟨h1, hz⟩) fun h2 => Or.inr ⟨h2, hz⟩)⟩
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h' => hn (h'.elim (fun h1 => Or.inl h1.1) fun h2 => Or.inr h2.1)⟩

/-! ### The named inputs -/

/-- **Named input: the past of a boundary walk is a local set of the centred field marked by its retained history,
R51 form** (Lemma GW1, pp. 618–620: "The iterated optional Gaussian law is the full joined-history kernel"; follow-up
note D.2, L771–L832: "Iterating the conditional Gaussian identities proves the asserted full joined-history law. No old
range or component is forgotten"). For a GFF `h` on `ℍ` with piecewise-constant data `b`, `0 < κ < 4`, and staged
histories `E` of every boundary-continued program which are `StagedPiecesRegular` (ruling R51) and regular at every
sample (`IsRegularDriver`, as the regularized family `StagedReg.regFam` is; then the runs are functions of the retained
past at every sample, which the first clause needs), the boundary walk
`w = boundaryWalkSpec b jumps θ right` with its retained past `𝒢 = pastSigma … w (E w) |w|` satisfies, for the centred
field `h⁰ = h − 𝔥₀` (`𝔥₀` the bounded harmonic extension of `b`):

* every avoidance event `{walk ∩ U = ∅}` of an open `U ⊆ ℍ` is an event of `𝒢` (the walk is recorded in its past);
* almost surely the complement in `ℍ` of the walk is open;
* the walk is a local set of `h⁰` satisfying the history-marked avoidance criterion for the marks `𝒢`
  (`WholeField.IsHistoryAvoidanceLocal`, Lemma 3.6 (i) with marks; Aux. lemma 18). -/
def WalkMarkedLocalRegStatement (θ : ℝ) (right : Bool) : Prop :=
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
        MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right))
            (boundaryWalkSpec b jumps θ right).2.2.length]
          {ω | Disjoint (walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
            (E (boundaryWalkSpec b jumps θ right)) ω) U}) ∧
      (∀ᵐ ω ∂P, IsOpen (H \ walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
        (E (boundaryWalkSpec b jumps θ right)) ω)) ∧
      WholeField.IsHistoryAvoidanceLocal
        (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right))
          (boundaryWalkSpec b jumps θ right).2.2.length)
        (walkSet κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)))
        (WholeField.centredField h u₀) P

/-- **Named input: the retained past of a staged history is determined by the field, R51 form** (Lemma GW1: each
piece is the flow line of the conditional field, hence by Theorem 1.2 a function of it; PROVE-T14-SB7's (a1),
`StagedDet.exists_pastMap_eq_comp_field`, from `Theorem12ParamStatement` and Theorem 1.3). For a staged history `E`
of a GFF with piecewise-constant data, `0 < κ < 4`, which is `StagedPiecesRegular`, the retained past before every
instruction `k` is almost surely a Borel function of the field. -/
def PastDetRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), IsStagedHistory κ b jumps P h spec E →
      StagedPiecesRegular κ b jumps P spec E → ∀ k : ℕ,
        ∃ f : DistOn upperHalfPlaneOpens → Exist.Staged.PastData k, Measurable f ∧
          Exist.Staged.pastMap κ b jumps spec E k =ᵐ[P] f ∘ h

/-! ### The retained past is an event family of the centred field, up to null sets -/

section AeSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A σ-algebra generated by a map that is almost surely a Borel function of `h` is, up to null sets, inside `σ(h)`. -/
theorem comap_le_aeSigma_of_ae_eq_comp {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] {p : Ω → S}
    {g : Ω → T} {f : T → S} (hf : Measurable f) (hp : p =ᵐ[P] f ∘ g) :
    MeasurableSpace.comap p inferInstance ≤ LocalSets.aeSigma (MeasurableSpace.comap g inferInstance) P := by
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨g ⁻¹' (f ⁻¹' B), ⟨f ⁻¹' B, hf hB, rfl⟩, ?_⟩
  filter_upwards [hp] with ω hω
  simp only [mem_preimage, hω, Function.comp_apply]

omit mΩ in
/-- The σ-algebra of the field is that of the centred field (a deterministic translation). -/
theorem comap_field_le_comap_centred (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) :
    MeasurableSpace.comap h inferInstance ≤
      MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance := by
  rintro _ ⟨B, hB, rfl⟩
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens =>
      g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ :=
    LQGMetric.measurable_distOn_iff.2 fun φ => (LQGMetric.measurable_distOn_apply φ).add_const _
  refine ⟨(fun g => g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ⁻¹' B, hadd hB, ?_⟩
  ext ω
  simp only [mem_preimage, WholeField.centredField, sub_add_cancel]

/-- `aeSigma` is monotone in the σ-algebra. -/
theorem aeSigma_mono {m m' : MeasurableSpace Ω} (hmm' : m ≤ m') :
    LocalSets.aeSigma m P ≤ LocalSets.aeSigma m' P := by
  rintro G ⟨G', hG', hGG'⟩
  exact ⟨G', hmm' G' hG', hGG'⟩

/-- **The retained past is, up to null sets, an event family of the centred field** (from its determination by the
field). -/
theorem pastSigma_le_aeSigma_centred {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {h : Ω → DistOn upperHalfPlaneOpens}
    {f : DistOn upperHalfPlaneOpens → Exist.Staged.PastData k} (hf : Measurable f)
    (hp : Exist.Staged.pastMap κ b jumps spec E k =ᵐ[P] f ∘ h) (u₀ : ℂ → ℝ) :
    pastSigma κ b jumps spec E k ≤
      LocalSets.aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P := by
  rw [Exist.Staged.pastSigma_eq_comap]
  exact (comap_le_aeSigma_of_ae_eq_comp hf hp).trans (aeSigma_mono (comap_field_le_comap_centred h u₀))

end AeSigma

end WalkLaw

end Theorem14

end InteractingSLE
