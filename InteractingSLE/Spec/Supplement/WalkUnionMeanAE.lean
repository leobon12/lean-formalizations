/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkStageLocalAE
import InteractingSLE.Spec.Supplement.WalkUnionLawMain
import InteractingSLE.Spec.Supplement.WalkPastDet

/-!
# Theorem 1.4: the union law of the two walks with the walks' avoidance events up to null sets (R58)

Packet PROVE-T14-WALKLAW3. PROVE-T14-WALKLAW's wiring (`WalkLaw.gw3UnionLawBetweenRegStatement_of_walkLaws`) takes the
exact clause (i) of `WalkMarkedLocalRegStatement` and the union mean `WalkUnionMeanRegStatement`, which conditions on
the germs of the union of the walks. Under ruling R58 the walks' avoidance events are events of the retained pasts only
up to null sets; the union of the walks is then only almost surely a random closed set, and for a non-measurable union
`germSigma` is not a sub-σ-algebra of the events (Mathlib's conditional expectation is then the junk value `0`). So:

* **`WalkUnionMeanRegAEStatement`** (named input, the D.5–D.6 union mean in R58 form): `WalkUnionMeanRegStatement`
  with the germs of a measurable version `A'` of the union (a random closed set almost surely equal to the union);
* **`walkUnion_markedAE`**: the union of the walks is a marked local set for the joined pasts, its avoidance events
  being events of the joined past up to null sets (from `WalkMarkedLocalRegAEStatement` for both walks, through
  measurable versions, `exists_version_of_aeSigma`);
* **`gw3UnionLawBetweenRegStatement_of_walkLawsAE`**: `GW3Between.GW3UnionLawBetweenRegStatement` from the R58 walk
  statements, the determination of the pasts and the R58 union mean (WALKLAW's proof, run on the measurable version);
* **`gw3UnionLawBetweenRegStatement_of_kernel`**: the same from Theorems 1.2–1.3, the per-stage kernel input
  `WalkStageKernelLocalStatement` for both walks and `WalkUnionMeanRegAEStatement` (the measurability stage input is
  proved, `walkStageAvoidMeasAEStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets GW3Between

/-! ### The union of the two walks -/

/-- **The union of the two walks is a local set of the centred field marked by both retained pasts** (R58 form: its
avoidance events are events of the joined past up to null sets). -/
theorem walkUnion_markedAE (hdet : PastDetRegStatement.{u})
    (hR : WalkMarkedLocalRegAEStatement.{u} (-(Real.pi / 2)) true)
    (hL : WalkMarkedLocalRegAEStatement.{u} (Real.pi / 2) false) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg' : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (jointPast κ b jumps E) P] {ω | Disjoint (walkUnionSet κ b jumps E ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ walkUnionSet κ b jumps E ω)) ∧
    jointPast κ b jumps E ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    WholeField.IsHistoryAvoidanceLocal (jointPast κ b jumps E) (walkUnionSet κ b jumps E)
      (WholeField.centredField h u₀) P := by
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  obtain ⟨hAR, hoR, hlocR⟩ := hR κ hκ hκ4 b jumps hb P h hh E hE hreg hreg' u₀ hu₀
  obtain ⟨hAL, hoL, hlocL⟩ := hL κ hκ hκ4 b jumps hb P h hh E hE hreg hreg' u₀ hu₀
  obtain ⟨fR, hfR, hpR⟩ := hdet κ hκ hκ4 b jumps hb P h hh _ _ (hE _ hprR) (hreg _ hprR)
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length
  obtain ⟨fL, hfL, hpL⟩ := hdet κ hκ hκ4 b jumps hb P h hh _ _ (hE _ hprL) (hreg _ hprL)
    (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length
  have hdR := pastSigma_le_aeSigma_centred hfR hpR u₀
  have hdL := pastSigma_le_aeSigma_centred hfL hpL u₀
  -- measurable versions of the two walks
  obtain ⟨AR, -, hARae, hARm⟩ := exists_version_of_aeSigma (fun ω => walkSet_subset_H _ _ _ _ _ ω) hoR hAR
  obtain ⟨AL, -, hALae, hALm⟩ := exists_version_of_aeSigma (fun ω => walkSet_subset_H _ _ _ _ _ ω) hoL hAL
  have hlocR' := isHistoryAvoidanceLocal_congr_ae (hARae.mono fun ω h => h.symm) hlocR
  have hlocL' := isHistoryAvoidanceLocal_congr_ae (hALae.mono fun ω h => h.symm) hlocL
  have hU := isHistoryAvoidanceLocal_union_of_det (WholeField.measurable_centredField hh.1 u₀) hARm hALm hdR hdL
    hlocR' hlocL'
  refine ⟨fun U hU => ?_, ?_, sup_le hdR hdL, isHistoryAvoidanceLocal_congr_ae ?_ hU⟩
  · have e : {ω | Disjoint (walkUnionSet κ b jumps E ω) (U : Set ℂ)} =
        {ω | Disjoint (walkSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω) (U : Set ℂ)} ∩
        {ω | Disjoint (walkSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false)) ω) (U : Set ℂ)} := by
      ext ω
      simp only [walkUnionSet, mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
    rw [e]
    exact (aeSigma_mono (le_sup_left : _ ≤ jointPast κ b jumps E) _ (hAR U hU)).inter
      (aeSigma_mono (le_sup_right : _ ≤ jointPast κ b jumps E) _ (hAL U hU))
  · filter_upwards [hoR, hoL] with ω h1 h2
    have e : ∀ s t v : Set ℂ, s \ (t ∪ v) = (s \ t) ∩ (s \ v) := fun s t v => Set.ext fun z => by
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
      tauto
    rw [walkUnionSet, e]
    exact h1.inter h2
  · filter_upwards [hARae, hALae] with ω h1 h2
    simp only [walkUnionSet, h1, h2]

/-! ### The named input: the union mean on the between components, R58 form -/

/-- **Named input: the union mean on the between components (follow-up note D.5–D.6), R58 form.** As
`WalkUnionMeanRegStatement`, with the conditional mean taken given the germs of a measurable version `A'` of the union
of the two walks (`A'` is a random closed set, `Measurable` for the hitting σ-algebra, almost surely equal to the
union; the conditional mean does not depend on the version, the germ σ-algebras of two versions differing by null sets
at every level `δ`). Needed because the union is only almost surely a random closed set (ruling R58), and for a
non-measurable union `germSigma` is not a sub-σ-algebra of the events. -/
def WalkUnionMeanRegAEStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧ (∀ᵐ ω ∂P, A' ω = walkUnionSet κ b jumps E ω) ∧
      ∃ μ : Ω → ℂ → ℝ,
        (∀ φ : TestOn upperHalfPlaneOpens,
          Measurable[jointPast κ b jumps E] fun ω => ∫ z, μ ω z * φ z) ∧
        (∀ᵐ ω ∂P, ContinuousOn (μ ω) (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω)))) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) →
          P[fun ω' => WholeField.centredField h u₀ ω' φ |
              germSigma A' (WholeField.centredField h u₀) ⊔ jointPast κ b jumps E] ω =
            (∫ z, μ ω z * φ z) - ∫ z, u₀ z * φ z) ∧
        ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω)),
          ∃ c : Chart, IsComponentChart (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
              (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) C c ∧
            ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω)) c.2.1 bC jumpsC ∧
              ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀' →
                ∀ w ∈ H, u₀' w = μ ω (c.2.1 w) + QuantumZipper.chiC κ * c.2.2 (c.2.1 w)


/-! ### The union law on the between components -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The kernel form of the union law, R58 form** (WALKLAW's `ae_betweenLawAt_of_walkLaws_reg` run on the measurable
version of the union given by the union-mean input). -/
theorem ae_betweenLawAt_of_walkLawsAE_reg (hdet : PastDetRegStatement.{u})
    (hR : WalkMarkedLocalRegAEStatement.{u} (-(Real.pi / 2)) true)
    (hL : WalkMarkedLocalRegAEStatement.{u} (Real.pi / 2) false) (hM : WalkUnionMeanRegAEStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg' : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) :
    ∀ᵐ ω₀ ∂P, BetweenLawAt κ b h (condExpKernel P (jointPast κ b jumps E) ω₀)
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀))
      (ExplState.ordinarySet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
      (ExplState.ordinarySet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) := by
  set wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwR
  set wL := boundaryWalkSpec b jumps (Real.pi / 2) false with hwL
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨-, hAo, -, hlocJ⟩ := walkUnion_markedAE hdet hR hL hκ hκ4 hb hh hE hreg hreg' hu₀
  obtain ⟨A', hAm, hA'ae, μ, hμm, hμc, hμmean, hμchart⟩ := hM κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg u₀ hu₀
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  have hJle : jointPast κ b jumps E ≤ mΩ := sup_le ((hE _ hprR).2.1 _) ((hE _ hprL).2.1 _)
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hlocJ' := isHistoryAvoidanceLocal_congr_ae (hA'ae.mono fun ω h => h.symm) hlocJ
  have hAcU : ∀ᵐ ω ∂P, walkUnionSet κ b jumps E ω ⊆ H ∧ IsOpen (H \ walkUnionSet κ b jumps E ω) := by
    filter_upwards [hAo] with ω hω
    exact ⟨union_subset (walkSet_subset_H _ _ _ _ _ _) (walkSet_subset_H _ _ _ _ _ _), hω⟩
  have hAc : ∀ᵐ ω ∂P, A' ω ⊆ H ∧ IsOpen (H \ A' ω) := by
    filter_upwards [hAcU, hA'ae] with ω h1 h2
    rw [h2]
    exact h1
  have hA'k := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hA'ae
  -- the regular conditional laws given the joined past live on fibres of the retained pasts
  obtain ⟨NR, hNR, hfibR⟩ := exists_run_eq_of_pastMap_eq (hreg _ hprR) wR.2.2.length
  obtain ⟨NL, hNL, hfibL⟩ := exists_run_eq_of_pastMap_eq (hreg _ hprL) wL.2.2.length
  have hpRm : Measurable[jointPast κ b jumps E] (Exist.Staged.pastMap κ b jumps wR (E wR) wR.2.2.length) :=
    (comap_measurable _).mono le_sup_left le_rfl
  have hpLm : Measurable[jointPast κ b jumps E] (Exist.Staged.pastMap κ b jumps wL (E wL) wL.2.2.length) :=
    (comap_measurable _).mono le_sup_right le_rfl
  have hfR := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hJle hpRm
  have hfL := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hJle hpLm
  have hNRk := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hNR
  have hNLk := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hNL
  have hu₀c : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := hu₀.1.continuousOn
  -- the kernel identity at each test function
  have hcfh : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω₀ ∂P,
      tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀))
        (ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)) →
      ∫ ω, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂(condExpKernel P (jointPast κ b jumps E) ω₀) =
        Complex.exp (Complex.I * ((∫ z, μ ω₀ z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) φ φ : ℝ) : ℂ)) := by
    intro φ
    obtain ⟨M, -, hM1, hM2⟩ := WholeField.exists_condExp_germSigma_history hh0 hAm hJle hlocJ' hAc φ
    have hFk := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hJle (hμm φ)
    have hM1k := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hM1
    have hmeank := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle (hμmean φ)
    have htow := ae_integral_cexp_eq_of_tower (P := P) hJle (germSigma_le hAm hh0.measurable)
      (WholeField.measurable_centredField hh.1 u₀) φ hM2
      (S := {ω₀ | tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀))
        (ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)) ∧ ω₀ ∈ NR ∧ ω₀ ∈ NL ∧
          A' ω₀ = walkUnionSet κ b jumps E ω₀})
      (c := fun ω₀ => (∫ z, μ ω₀ z * φ z) - ∫ z, u₀ z * φ z)
      (q := fun ω₀ => zeroGFFTestCov (H \ relClosureH (A' ω₀)) φ φ) (by
        filter_upwards [hfR, hfL, hNRk, hNLk, hM1k, hmeank, hFk, hA'k] with ω₀ hfRω hfLω hNRω hNLω hM1ω hmeanω hFω
          hA'ω hS
        obtain ⟨hsupp, hω₀R, hω₀L, hA'₀⟩ := hS
        filter_upwards [hfRω, hfLω, hNRω, hNLω, hM1ω, hmeanω, hFω, hA'ω] with ω e1 e2 n1 n2 m1 m2 f1 a1
        have hphysR : ExplState.physSet κ b jumps wR (fun k => E wR k ω) =
            ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) :=
          StagedReg.physSet_eq_of_run_eq (hfibR ω n1 ω₀ hω₀R e1)
        have hphysL : ExplState.physSet κ b jumps wL (fun k => E wL k ω) =
            ExplState.physSet κ b jumps wL (fun k => E wL k ω₀) :=
          StagedReg.physSet_eq_of_run_eq (hfibL ω n2 ω₀ hω₀L e2)
        have hA : A' ω = A' ω₀ := by
          rw [a1, hA'₀]
          simp only [walkUnionSet, walkSet]
          rw [hphysR, hphysL]
        refine ⟨?_, by rw [hA]⟩
        have hs : tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) := by
          rw [hphysR, hphysL]
          exact hsupp
        rw [m1, m2 hs, f1])
    filter_upwards [htow, hNR, hNL, hAcU, hA'ae] with ω₀ ht hR0 hL0 hAc0 hA0 hsupp
    have hUo' : IsOpen (H \ (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) ∪
        ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) := by
      rw [← H_diff_walkSet_union]
      exact hAc0.2
    have hQ : zeroGFFTestCov (H \ relClosureH (A' ω₀)) φ φ =
        zeroGFFTestCov (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) φ φ := by
      rw [hA0, relClosureH_eq hAc0.1 hAc0.2, walkUnionSet, H_diff_walkSet_union]
      exact GW3Joint.zeroGFFTestCov_eq_of_split (isOpen_betweenUnion hUo') (isOpen_sdiff_betweenUnion hUo')
        betweenUnion_subset hsupp hsupp
    have hrel : ∀ ω, Complex.exp (Complex.I * (h ω φ : ℂ)) =
        Complex.exp (Complex.I * (WholeField.centredField h u₀ ω φ : ℂ)) *
          Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) := fun ω => by
      rw [← Complex.exp_add]
      congr 1
      have e : WholeField.centredField h u₀ ω φ = h ω φ - ∫ z, u₀ z * φ z := by
        simp only [WholeField.centredField, sub_apply,
          SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c]
        simp_rw [mul_comm (φ _) (u₀ _)]
      rw [e]
      push_cast
      ring
    simp_rw [hrel]
    rw [integral_mul_const, ht ⟨hsupp, hR0, hL0, hA0⟩, hQ, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hK := ae_isZBGFFProcess_condExpKernel_of_integral (𝒢 := jointPast κ b jumps E) (P := P) hh.1
    (U := fun ω => betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
      (ExplState.physSet κ b jumps wL (fun k => E wL k ω)))
    (fun ω z hz => (betweenUnion_subset hz).1) (M := μ) hcfh
  filter_upwards [hK, hμc, hμchart, hAcU] with ω₀ hKω hcω hchω hAcω
  have hUo' : IsOpen (H \ (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) ∪
      ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) := by
    rw [← H_diff_walkSet_union]
    exact hAcω.2
  exact ⟨hUo', μ ω₀, hKω (isOpen_betweenUnion hUo') hcω, hchω⟩


end Main

/-- **`GW3UnionLawBetweenRegStatement` from the R58 walk statements** (WALKLAW's regularization argument unchanged). -/
theorem gw3UnionLawBetweenRegStatement_of_walkLawsAE (hdet : PastDetRegStatement.{u})
    (hR : WalkMarkedLocalRegAEStatement.{u} (-(Real.pi / 2)) true)
    (hL : WalkMarkedLocalRegAEStatement.{u} (Real.pi / 2) false) (hM : WalkUnionMeanRegAEStatement.{u}) :
    GW3UnionLawBetweenRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hreg wR wL
  obtain ⟨hE', hreg'', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_regHist (hreg spec hs)
  have hbody := ae_betweenLawAt_of_walkLawsAE_reg hdet hR hL hM hκ hκ4 hb hh hcf hζ' hE' hR' hreg''
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  -- the conditional laws given the two retained pasts agree almost surely
  have hpm : ∀ (E₁ : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E₁ spec)) →
      Measurable fun ω => (Exist.Staged.pastMap κ b jumps wR (E₁ wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (E₁ wL) wL.2.2.length ω) := fun E₁ hE₁ =>
    (Measurable.of_comap_le ((hE₁ _ hprR).2.1 _)).prodMk (Measurable.of_comap_le ((hE₁ _ hprL).2.1 _))
  have hjp : ∀ (E₁ : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), jointPast κ b jumps E₁ =
      MeasurableSpace.comap (fun ω => (Exist.Staged.pastMap κ b jumps wR (E₁ wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (E₁ wL) wL.2.2.length ω)) inferInstance := fun E₁ =>
    (MeasurableSpace.comap_prodMk _ _).symm
  have hpae : (fun ω => (Exist.Staged.pastMap κ b jumps wR (StagedReg.regFam E wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (StagedReg.regFam E wL) wL.2.2.length ω)) =ᵐ[P]
      fun ω => (Exist.Staged.pastMap κ b jumps wR (E wR) wR.2.2.length ω,
        Exist.Staged.pastMap κ b jumps wL (E wL) wL.2.2.length ω) := by
    filter_upwards [StagedReg.ae_pastMap_regHist (hreg _ hprR) wR.2.2.length,
      StagedReg.ae_pastMap_regHist (hreg _ hprL) wL.2.2.length] with ω h1 h2
    exact Prod.ext h1 h2
  have hker := StagedReg.ae_condExpKernel_eq_of_ae_eq (P := P) (hpm _ hE') (hpm _ hE) hpae
  rw [← hjp, ← hjp] at hker
  filter_upwards [hbody, hker, hrun _ hprR, hrun _ hprL] with ω₀ hbω hkω hrR hrL
  have e1 := StagedReg.physSet_eq_of_run_eq (κ := κ) (b := b) (jumps := jumps) (hrR wR.2.2.length)
  have e2 := StagedReg.physSet_eq_of_run_eq (κ := κ) (b := b) (jumps := jumps) (hrL wL.2.2.length)
  have e3 := ordinarySet_eq_of_run_eq (κ := κ) (b := b) (jumps := jumps) (hrR wR.2.2.length)
  have e4 := ordinarySet_eq_of_run_eq (κ := κ) (b := b) (jumps := jumps) (hrL wL.2.2.length)
  rw [hkω, e1, e2, e3, e4] at hbω
  exact hbω

/-- **`GW3UnionLawBetweenRegStatement` from Theorems 1.2–1.3, the per-stage kernel inputs of both walks and the R58
union mean** (Theorem 1.4 only). -/
theorem gw3UnionLawBetweenRegStatement_of_kernel (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hkR : WalkStageKernelLocalStatement.{u} (-(Real.pi / 2)) true)
    (hkL : WalkStageKernelLocalStatement.{u} (Real.pi / 2) false) (hM : WalkUnionMeanRegAEStatement.{u}) :
    GW3UnionLawBetweenRegStatement.{u} :=
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  gw3UnionLawBetweenRegStatement_of_walkLawsAE hdet (walkMarkedLocalRegAEStatement_right hdet hkR)
    (walkMarkedLocalRegAEStatement_left hdet hkL) hM

end WalkLaw

end Theorem14

end InteractingSLE
