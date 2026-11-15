/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw
import InteractingSLE.Spec.Supplement.WalkUnionLawKernel
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Supplement.GW1LaterR51
import InteractingSLE.Spec.Sec7.Aux122Disint
import InteractingSLE.Spec.Restart.R1Flow
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Supplement.KernelTower2

/-!
# Lemma GW3's union law on the components between the walks, from the per-walk laws

Packet PROVE-T14-WALKLAW. Lemma GW3, proof (`source/spec/p625-671.md` L210–L226, pp. 636–637) and the follow-up note's
D.6 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L934–L1004): "The two finite-stage marked local sets have
their complete kernels by GW1. Their union […] retain[s] the marked Gaussian union law"; "The marked union kernel
supplies the zero-boundary Green covariance and conditional independence in the selected components. Therefore the
exact component heights are […]".

**`gw3UnionLawBetweenRegStatement_of_walkLaws`**: `GW3Between.GW3UnionLawBetweenRegStatement` from

* the per-walk marked locality of both walks (`WalkMarkedLocalRegStatement`, D.2);
* the determination of the retained pasts by the field (`PastDetRegStatement`, PROVE-T14-SB7's (a1));
* the identification of the union mean on the between components (`WalkUnionMeanRegStatement`, D.5–D.6).

The proof: the union of the two walks is a local set of the centred field `h⁰` marked by both retained pasts
(`walkUnion_marked`, `WalkLaw.isHistoryAvoidanceLocal_union_of_det`); Aux. lemma 18 with marks gives the conditional
characteristic functional of `h⁰(φ)` given the germs and the marks; the tower property along the regular conditional
law given the marks alone, on which the walks are frozen (the runs are functions of the retained pasts on a
probability-one set, `exists_run_eq_of_pastMap_eq`; the conditional laws live on fibres, `Aux122Disint`), turns it
into the characteristic value under `condExpKernel P (𝒢_R ⊔ 𝒢_L) ω₀` (`ae_integral_cexp_eq_between`); and
`WalkLaw.ae_isZBGFFProcess_condExpKernel_of_integral` turns these values into the zero-boundary GFF law on the union of
the between components.
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

/-! ### The joined past and the union of the two walks -/

/-- The joined retained past of the two boundary walks (the conditioning σ-algebra of Lemma GW3). -/
@[instance_reducible]
def jointPast (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    MeasurableSpace Ω :=
  pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length ⊔
    pastSigma κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (E (boundaryWalkSpec b jumps (Real.pi / 2) false)) (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length

/-- The union of the ranges in `ℍ` of the two boundary walks. -/
def walkUnionSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (ω : Ω) : Set ℂ :=
  walkSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω ∪
    walkSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (E (boundaryWalkSpec b jumps (Real.pi / 2) false)) ω

/-- **The union of the two walks is a local set of the centred field marked by both retained pasts.** -/
theorem walkUnion_marked (hdet : PastDetRegStatement.{u}) (hR : WalkMarkedLocalRegStatement.{u} (-(Real.pi / 2)) true)
    (hL : WalkMarkedLocalRegStatement.{u} (Real.pi / 2) false) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg' : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[jointPast κ b jumps E] {ω | Disjoint (walkUnionSet κ b jumps E ω) U}) ∧
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
  refine ⟨fun U hU => ?_, ?_, sup_le hdR hdL,
    isHistoryAvoidanceLocal_union_of_det (WholeField.measurable_centredField hh.1 u₀) hAR hAL hdR hdL hlocR hlocL⟩
  · have e : {ω | Disjoint (walkUnionSet κ b jumps E ω) (U : Set ℂ)} =
        {ω | Disjoint (walkSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω) (U : Set ℂ)} ∩
        {ω | Disjoint (walkSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false)) ω) (U : Set ℂ)} := by
      ext ω
      simp only [walkUnionSet, mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
    rw [e]
    exact ((le_sup_left : _ ≤ jointPast κ b jumps E) _ (hAR U hU)).inter
      ((le_sup_right : _ ≤ jointPast κ b jumps E) _ (hAL U hU))
  · filter_upwards [hoR, hoL] with ω h1 h2
    have e : ∀ s t v : Set ℂ, s \ (t ∪ v) = (s \ t) ∩ (s \ v) := fun s t v => Set.ext fun z => by
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
      tauto
    rw [walkUnionSet, e]
    exact h1.inter h2

/-! ### The named input: the union mean on the between components -/

/-- **Named input: the mean of the marked union of the two walks on the components between them (follow-up note
D.5–D.6), R51 form.** In the setting of `GW3Between.GW3UnionLawBetweenRegStatement`, for the centred field
`h⁰ = h − 𝔥₀` there is a mean `μ ω : ℂ → ℝ` read off the two retained pasts such that

* for every test function `φ`, `ω ↦ ∫ μ ω · φ` is measurable for the joined retained past (D.5: "the entire classified
  word is measurable in the past history");
* almost surely `μ ω` is continuous on the union of the between components;
* for every test function `φ`, almost surely on the event that `φ` is supported between the walks, the conditional mean
  of `h⁰(φ)` given the germs of the union of the walks and both retained pasts is `∫ μ ω φ − ∫ 𝔥₀ φ` (D.2–D.6: "the full
  conditional harmonic mean is the canonical finite-piece mean"; "GB2's disk bounds and finite-exception uniqueness
  remove any singular term at every such fiber");
* almost surely every between component has a component chart in which `μ ω ∘ inv + χ · lift ∘ inv` is the bounded
  harmonic extension of a word satisfying (GW3.1) (D.6: "the exact component heights are […] +Λ, H_L ≥ Λ, −Λ,
  H_R ≤ −Λ"). -/
def WalkUnionMeanRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      ∃ μ : Ω → ℂ → ℝ,
        (∀ φ : TestOn upperHalfPlaneOpens,
          Measurable[jointPast κ b jumps E] fun ω => ∫ z, μ ω z * φ z) ∧
        (∀ᵐ ω ∂P, ContinuousOn (μ ω) (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω)))) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) →
          P[fun ω' => WholeField.centredField h u₀ ω' φ |
              germSigma (walkUnionSet κ b jumps E) (WholeField.centredField h u₀) ⊔ jointPast κ b jumps E] ω =
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

/-! ### The runs are functions of the retained past on a probability-one set -/

section Fibre

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **On a probability-one set the run of a staged history is a function of its retained past** (through the
regularized history, PROVE-T14-GW1X's `StagedReg.regHist`, which is regular at every sample and has almost surely the
same runs). -/
theorem exists_run_eq_of_pastMap_eq {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) (n : ℕ) :
    ∃ N : Set Ω, (∀ᵐ ω ∂P, ω ∈ N) ∧ ∀ ω ∈ N, ∀ ω' ∈ N,
      Exist.Staged.pastMap κ b jumps spec E n ω = Exist.Staged.pastMap κ b jumps spec E n ω' →
        ExplState.run κ b jumps spec (fun j => E j ω) n = ExplState.run κ b jumps spec (fun j => E j ω') n := by
  refine ⟨{ω | ∀ k, ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec E j ω) k =
    ExplState.run κ b jumps spec (fun j => E j ω) k}, StagedReg.ae_run_regHist hR, fun ω hω ω' hω' he => ?_⟩
  have h1 : Exist.Staged.pastMap κ b jumps spec (StagedReg.regHist spec E) n ω =
      Exist.Staged.pastMap κ b jumps spec E n ω := by
    unfold Exist.Staged.pastMap
    rw [hω n]
  have h1' : Exist.Staged.pastMap κ b jumps spec (StagedReg.regHist spec E) n ω' =
      Exist.Staged.pastMap κ b jumps spec E n ω' := by
    unfold Exist.Staged.pastMap
    rw [hω' n]
  have key := Exist.StagedLaw.run_eq_of_pastMap_eq (κ := κ) (b := b) (jumps := jumps) spec
    (E := StagedReg.regHist spec E) (k := n) (fun j _ ω => StagedReg.isRegularDriver_regHist j ω)
    (h1.trans (he.trans h1'.symm))
  rw [← hω n, ← hω' n]
  exact key

end Fibre

/-! ### The tower step along the regular conditional law given the marks -/

section Tower

variable {Ω : Type*} {ℋ 𝒜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The tower step at one test function.** If the conditional characteristic value of `X(φ)` given `𝒜 ⊔ ℋ` is
`e^{iM} e^{−Q/2}`, and on an event `S`, under the regular conditional law given `ℋ`, `M` and `Q` are almost surely the
constants `c ω₀`, `q ω₀`, then the characteristic value of `X(φ)` under that law is `e^{i c ω₀} e^{−q ω₀ / 2}`. -/
theorem ae_integral_cexp_eq_of_tower (hℋ : ℋ ≤ mΩ) (h𝒜 : 𝒜 ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (φ : TestOn upperHalfPlaneOpens) {M Q : Ω → ℝ}
    (hcf : (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * Q ω) : ℝ) : ℂ)) =ᵐ[P]
      P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒜 ⊔ ℋ])
    {S : Set Ω} {c q : Ω → ℝ}
    (hconst : ∀ᵐ ω₀ ∂P, ω₀ ∈ S → ∀ᵐ ω ∂(condExpKernel P ℋ ω₀), M ω = c ω₀ ∧ Q ω = q ω₀) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ S →
      ∫ ω, Complex.exp (Complex.I * (X ω φ : ℂ)) ∂(condExpKernel P ℋ ω₀) =
        Complex.exp (Complex.I * (c ω₀ : ℂ)) * ((Real.exp (-(1 / 2) * q ω₀) : ℝ) : ℂ) := by
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) with hf
  have hfi : Integrable f P := GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX)
  have h1 := condExp_ae_eq_integral_condExpKernel hℋ hfi
  have h2 : P[f | ℋ] =ᵐ[P] P[P[f | 𝒜 ⊔ ℋ] | ℋ] := (condExp_condExp_of_le le_sup_right (sup_le h𝒜 hℋ)).symm
  have h3 := condExp_ae_eq_integral_condExpKernel hℋ (integrable_condExp (m := 𝒜 ⊔ ℋ) (μ := P) (f := f))
  have h4 := KernelTower.ae_ae_condExpKernel_of_ae hℋ hcf
  filter_upwards [h1, h2, h3, h4, hconst] with ω₀ h1ω h2ω h3ω h4ω h5ω hS
  rw [← h1ω, h2ω, h3ω]
  have hP' : IsProbabilityMeasure (condExpKernel P ℋ ω₀) := inferInstance
  calc ∫ y, P[f | 𝒜 ⊔ ℋ] y ∂(condExpKernel P ℋ ω₀)
      = ∫ _y, Complex.exp (Complex.I * (c ω₀ : ℂ)) * ((Real.exp (-(1 / 2) * q ω₀) : ℝ) : ℂ)
          ∂(condExpKernel P ℋ ω₀) := by
        refine integral_congr_ae ?_
        filter_upwards [h4ω, h5ω hS] with y hy hcy
        rw [← hy, hcy.1, hcy.2]
    _ = _ := by simp

end Tower

/-! ### The union law on the between components -/

/-- The conclusion of `GW3Between.GW3UnionLawBetweenRegStatement` at one sample, for walks `R`, `L` with ordinary parts
`ordR`, `ordL` and the conditional law `ν`. -/
def BetweenLawAt (κ : ℝ) (b : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistOn upperHalfPlaneOpens)
    (ν : Measure Ω) (R L ordR ordL : Set ℂ) : Prop :=
  ∃ (hUo : IsOpen (H \ (R ∪ L))) (m : ℂ → ℝ),
    LQGMetric.IsZBGFFProcess ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩
      (fun ψ ω => h ω (GFF.testIncl ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩ upperHalfPlaneOpens ψ) -
        ∫ z, m z * ψ z) ν ∧
    ∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c ∧
      ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
        IsComponentBoundaryData κ b ordR ordL c.2.1 bC jumpsC ∧
        ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀ →
          ∀ w ∈ H, u₀ w = m (c.2.1 w) + QuantumZipper.chiC κ * c.2.2 (c.2.1 w)

/-- **The between-component union law for staged families regular at every sample**, from the per-walk laws. -/
theorem ae_betweenLawAt_of_walkLaws_reg (hdet : PastDetRegStatement.{u})
    (hR : WalkMarkedLocalRegStatement.{u} (-(Real.pi / 2)) true)
    (hL : WalkMarkedLocalRegStatement.{u} (Real.pi / 2) false) (hM : WalkUnionMeanRegStatement.{u})
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
  obtain ⟨hAv, hAo, -, hlocJ⟩ := walkUnion_marked hdet hR hL hκ hκ4 hb hh hE hreg hreg' hu₀
  obtain ⟨μ, hμm, hμc, hμmean, hμchart⟩ := hM κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg u₀ hu₀
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  have hJle : jointPast κ b jumps E ≤ mΩ := sup_le ((hE _ hprR).2.1 _) ((hE _ hprL).2.1 _)
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the union of the walks is a random closed set
  have hAm : Measurable[mΩ, hittingSigma] (walkUnionSet κ b jumps E) := by
    refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
    rintro _ ⟨V, hVo, hVH, rfl⟩
    have e : walkUnionSet κ b jumps E ⁻¹' {B | (B ∩ V).Nonempty} =
        {ω | Disjoint (walkUnionSet κ b jumps E ω) ((⟨V, hVo⟩ : Opens ℂ) : Set ℂ)}ᶜ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
      rfl
    rw [e]
    exact (hJle _ (hAv ⟨V, hVo⟩ hVH)).compl
  have hAc : ∀ᵐ ω ∂P, walkUnionSet κ b jumps E ω ⊆ H ∧ IsOpen (H \ walkUnionSet κ b jumps E ω) := by
    filter_upwards [hAo] with ω hω
    exact ⟨union_subset (walkSet_subset_H _ _ _ _ _ _) (walkSet_subset_H _ _ _ _ _ _), hω⟩
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
    obtain ⟨M, -, hM1, hM2⟩ := WholeField.exists_condExp_germSigma_history hh0 hAm hJle hlocJ hAc φ
    have hFk := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hJle (hμm φ)
    have hM1k := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle hM1
    have hmeank := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hJle (hμmean φ)
    have htow := ae_integral_cexp_eq_of_tower (P := P) hJle (germSigma_le hAm hh0.measurable)
      (WholeField.measurable_centredField hh.1 u₀) φ hM2
      (S := {ω₀ | tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀))
        (ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)) ∧ ω₀ ∈ NR ∧ ω₀ ∈ NL})
      (c := fun ω₀ => (∫ z, μ ω₀ z * φ z) - ∫ z, u₀ z * φ z)
      (q := fun ω₀ => zeroGFFTestCov (H \ relClosureH (walkUnionSet κ b jumps E ω₀)) φ φ) (by
        filter_upwards [hfR, hfL, hNRk, hNLk, hM1k, hmeank, hFk] with ω₀ hfRω hfLω hNRω hNLω hM1ω hmeanω hFω hS
        obtain ⟨hsupp, hω₀R, hω₀L⟩ := hS
        filter_upwards [hfRω, hfLω, hNRω, hNLω, hM1ω, hmeanω, hFω] with ω e1 e2 n1 n2 m1 m2 f1
        have hphysR : ExplState.physSet κ b jumps wR (fun k => E wR k ω) =
            ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) :=
          StagedReg.physSet_eq_of_run_eq (hfibR ω n1 ω₀ hω₀R e1)
        have hphysL : ExplState.physSet κ b jumps wL (fun k => E wL k ω) =
            ExplState.physSet κ b jumps wL (fun k => E wL k ω₀) :=
          StagedReg.physSet_eq_of_run_eq (hfibL ω n2 ω₀ hω₀L e2)
        have hA : walkUnionSet κ b jumps E ω = walkUnionSet κ b jumps E ω₀ := by
          simp only [walkUnionSet, walkSet]
          rw [hphysR, hphysL]
        refine ⟨?_, by rw [hA]⟩
        have hs : tsupport φ ⊆ betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
            (ExplState.physSet κ b jumps wL (fun k => E wL k ω)) := by
          rw [hphysR, hphysL]
          exact hsupp
        rw [m1, m2 hs, f1])
    filter_upwards [htow, hNR, hNL, hAc] with ω₀ ht hR0 hL0 hAc0 hsupp
    have hUo' : IsOpen (H \ (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) ∪
        ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) := by
      rw [← H_diff_walkSet_union]
      exact hAc0.2
    have hQ : zeroGFFTestCov (H \ relClosureH (walkUnionSet κ b jumps E ω₀)) φ φ =
        zeroGFFTestCov (betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀))
          (ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) φ φ := by
      rw [relClosureH_eq hAc0.1 hAc0.2, walkUnionSet, H_diff_walkSet_union]
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
    rw [integral_mul_const, ht ⟨hsupp, hR0, hL0⟩, hQ, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hK := ae_isZBGFFProcess_condExpKernel_of_integral (𝒢 := jointPast κ b jumps E) (P := P) hh.1
    (U := fun ω => betweenUnion (ExplState.physSet κ b jumps wR (fun k => E wR k ω))
      (ExplState.physSet κ b jumps wL (fun k => E wL k ω)))
    (fun ω z hz => (betweenUnion_subset hz).1) (M := μ) hcfh
  filter_upwards [hK, hμc, hμchart, hAc] with ω₀ hKω hcω hchω hAcω
  have hUo' : IsOpen (H \ (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) ∪
      ExplState.physSet κ b jumps wL (fun k => E wL k ω₀))) := by
    rw [← H_diff_walkSet_union]
    exact hAcω.2
  exact ⟨hUo', μ ω₀, hKω (isOpen_betweenUnion hUo') hcω, hchω⟩


/-! ### Regularization -/

section Reg

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The regularized history of a `StagedPiecesRegular` history is `StagedPiecesRegular`** (on the probability-one
set where the runs agree, every launched piece of the regularized history is the original piece on its own stop
interval: `StagedReg.regularize_eq_of_le`). -/
theorem stagedPiecesRegular_regHist {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    StagedPiecesRegular κ b jumps P spec (StagedReg.regHist spec E) := by
  filter_upwards [hR, StagedReg.ae_run_regHist hR] with ω hω hrun
  intro k θ t c hk hl
  rw [hrun (k + 1)] at hl
  obtain ⟨h0, hc, η, hη, htr⟩ := hω k θ t c hk hl
  have ht : Exist.StagedLaw.instrTime spec k = t := by
    simp only [Exist.StagedLaw.instrTime, hk]
  have heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min t (E k ω).2 → (StagedReg.regHist spec E k ω).1 s = (E k ω).1 s :=
    fun s hs => by
      simp only [StagedReg.regHist, ht]
      exact StagedReg.regularize_eq_of_le h0 hc hs
  rw [StagedReg.regHist_snd]
  refine ⟨(heq 0 (by simp)).trans h0, hc.congr fun s hs => heq s hs, η,
    Sec7.IsGeneratingTrace.congr_lt hη fun s hs => heq s hs.le, htr⟩

/-- Equal runs have equal ordinary parts. -/
theorem ordinarySet_eq_of_run_eq {spec : ExplSpec} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h : ExplState.run κ b jumps spec D' spec.2.2.length = ExplState.run κ b jumps spec D spec.2.2.length) :
    ExplState.ordinarySet κ b jumps spec D' = ExplState.ordinarySet κ b jumps spec D := by
  unfold ExplState.ordinarySet
  rw [h]

end Reg

/-- **Lemma GW3's union law on the components between the walks, from the per-walk laws** (Lemma GW3, proof, p. 636;
follow-up note D.2–D.6): `GW3Between.GW3UnionLawBetweenRegStatement` from the marked locality of each walk
(`WalkMarkedLocalRegStatement`), the determination of the retained pasts (`PastDetRegStatement`) and the union mean on
the between components (`WalkUnionMeanRegStatement`). The staged family is first replaced by its regularization
(`StagedReg.regFam`: staged, regular at every sample, almost surely the same runs); the walks, their ordinary parts
and the regular conditional laws given the retained pasts agree almost surely
(`StagedReg.ae_condExpKernel_eq_of_ae_eq`). -/
theorem gw3UnionLawBetweenRegStatement_of_walkLaws (hdet : PastDetRegStatement.{u})
    (hR : WalkMarkedLocalRegStatement.{u} (-(Real.pi / 2)) true)
    (hL : WalkMarkedLocalRegStatement.{u} (Real.pi / 2) false) (hM : WalkUnionMeanRegStatement.{u}) :
    GW3UnionLawBetweenRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hreg wR wL
  obtain ⟨hE', hreg'', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_regHist (hreg spec hs)
  have hbody := ae_betweenLawAt_of_walkLaws_reg hdet hR hL hM hκ hκ4 hb hh hcf hζ' hE' hR' hreg''
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

end WalkLaw

end Theorem14

end InteractingSLE
