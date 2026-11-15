/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawJointIndep
import InteractingSLE.Spec.Supplement.GW3Sided
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.GFF.LocalSets.Characterization

/-!
# Lemma GW3's one-chart field law from the marked union law of the two walks

Packet PROVE-T14-GW7. Lemma GW3, proof (`source/spec/p625-671.md` L210–L226, pp. 636–637): "The two finite-stage marked
local sets have their complete kernels by GW1. Their union, and the increasing proper completions of their last
pieces, retain the marked Gaussian union law. […] These prove (GW3.1) in the single connected normalization just
fixed. […] Marked union locality gives the zero-boundary Green covariance and the conditional independence of the
component fields."

The proof has two parts. The first — the conditional law of the field given both complete walks is a mean plus the
zero-boundary GFF of the complement `ℍ \ (R ∪ L)`, and in a common-lift chart of each between-component that mean is
the bounded harmonic extension of the word (GW3.1) — is recorded as the named input `GW3UnionLawRegStatement` (R51
form). The second, proved here (`exists_oneChart_of_unionLaw`, `gw3FieldLawOneChartRegStatement_of_unionLaw`), turns it
into the one-chart field law `GW3Joint.GW3FieldLawOneChartRegStatement`:

* the zero-boundary GFF of `U = ℍ \ (R ∪ L)` restricts to the zero-boundary GFF of each component `C` (the dual
  Dirichlet norm splits over the open pieces `C`, `U \ C`: `isZBGFFProcess_restrict_of_split`);
* read in the component chart it is the zero-boundary GFF of `ℍ` (`Chart.isZBGFFProcess_chartTransport`), with mean
  `m ∘ inv + χ · lift ∘ inv`, which is the bounded harmonic extension of the word by the input; so the transported
  field is a GFF with that boundary data (`IsGFFWithBoundaryData`);
* the component fields are independent (`iIndepFun_componentFields`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3Joint

/-! ### The pointwise reduction -/

/-- The image of `ℍ` under the inverse of a component chart is the component. -/
theorem image_inv_eq_of_isComponentChart {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) :
    c.2.1 '' H = C := by
  refine Subset.antisymm hc.2.2.1.image_subset fun z hz => ⟨c.1 z, hc.2.1 hz, hc.2.2.2.1.1 hz⟩

/-- **Lemma GW3's field law in one choice of charts, pointwise, from the union law.** For fixed walks `R`, `L` with
open complement `U = ℍ \ (R ∪ L)`: if under `ν` the field `h` (measurable) restricted to `U` is the zero-boundary GFF
of `U` plus the mean `m`, and every between-component has a component chart in which `m ∘ inv + χ · lift ∘ inv` is the
bounded harmonic extension of a word `bC` satisfying (GW3.1), then the conclusion of the one-chart field law holds. -/
theorem exists_oneChart_of_unionLaw {κ : ℝ} {b : ℝ → ℝ} {R L ordR ordL : Set ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) (hUo : IsOpen (H \ (R ∪ L)))
    {m : ℂ → ℝ}
    (hZ : LQGMetric.IsZBGFFProcess ⟨H \ (R ∪ L), hUo⟩
      (fun ψ ω => h ω (GFF.testIncl ⟨H \ (R ∪ L), hUo⟩ upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ν)
    (hcomp : ∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c ∧
      ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
        IsComponentBoundaryData κ b ordR ordL c.2.1 bC jumpsC ∧
        ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀ →
          ∀ w ∈ H, u₀ w = m (c.2.1 w) + QuantumZipper.chiC κ * c.2.2 (c.2.1 w)) :
    ∃ (cs : Set ℂ → Chart) (hC : Set ℂ → Ω → DistOn upperHalfPlaneOpens),
      (∀ C ∈ betweenComponents R L,
        IsComponentChart R L C (cs C) ∧
        (∀ ω, IsChartTransport (cs C) 1 0 (QuantumZipper.chiC κ) (h ω) (hC C ω)) ∧
        ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
          IsComponentBoundaryData κ b ordR ordL (cs C).2.1 bC jumpsC ∧
          IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
      iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν := by
  classical
  choose! cs hcs bC jumpsC hpc hbd hmean using hcomp
  set χ := QuantumZipper.chiC κ with hχ
  have hUH : (⟨H \ (R ∪ L), hUo⟩ : TopologicalSpace.Opens ℂ) ≤ upperHalfPlaneOpens := fun z hz => hz.1
  -- the components
  have hcc : ∀ C ∈ betweenComponents R L, ∃ z, C = connectedComponentIn (H \ (R ∪ L)) z := by
    rintro C ⟨z, -, -, -, rfl⟩
    exact ⟨z, rfl⟩
  have hCo : ∀ C ∈ betweenComponents R L, IsOpen C := fun C hC => by
    obtain ⟨z, rfl⟩ := hcc C hC
    exact hUo.connectedComponentIn
  have hCU : ∀ C ∈ betweenComponents R L, C ⊆ H \ (R ∪ L) := fun C hC => by
    obtain ⟨z, rfl⟩ := hcc C hC
    exact connectedComponentIn_subset _ _
  have hUC : ∀ C ∈ betweenComponents R L, IsOpen ((H \ (R ∪ L)) \ C) := fun C hC => by
    obtain ⟨z, rfl⟩ := hcc C hC
    exact isOpen_sdiff_connectedComponentIn hUo z
  have hconf : ∀ C ∈ betweenComponents R L, (cs C).IsConformal := fun C hC =>
    GW3Law.isConformal_of_isComponentChart (hcs C hC) (hCo C hC) ((hCU C hC).trans sdiff_subset)
  have hℓc : ∀ C ∈ betweenComponents R L, ContinuousOn (fun w => (cs C).2.2 ((cs C).2.1 w)) H := fun C hC =>
    (hcs C hC).2.2.2.2.2.1.comp (hconf C hC).1.continuousOn (hcs C hC).2.2.1
  -- the transported fields
  set T : Set ℂ → Ω → DistOn upperHalfPlaneOpens := fun C ω =>
    if hc : (cs C).IsConformal then Chart.chartTransport hc 1 0 χ (h ω) else h ω with hT
  have hTC : ∀ C (hC : C ∈ betweenComponents R L),
      T C = fun ω => Chart.chartTransport (hconf C hC) 1 0 χ (h ω) := fun C hC => by
    funext ω
    simp only [hT, hconf C hC, ↓reduceDIte]
  have htr : ∀ C ∈ betweenComponents R L, ∀ ω, IsChartTransport (cs C) 1 0 χ (h ω) (T C ω) := fun C hC ω => by
    rw [hTC C hC]
    exact Chart.isChartTransport_chartTransport (hconf C hC)
      (Chart.locallyIntegrableOn_of_continuousOn (hℓc C hC)) 1 0 χ (h ω)
  refine ⟨cs, T, fun C hC => ⟨hcs C hC, htr C hC, bC C, jumpsC C, hpc C hC, hbd C hC, ?_⟩, ?_⟩
  · -- the field law in the component chart
    have hc := hconf C hC
    have hdom : ((cs C).dom : Set ℂ) = C := by rw [hc.coe_dom, image_inv_eq_of_isComponentChart (hcs C hC)]
    have hdomU : (cs C).dom ≤ ⟨H \ (R ∪ L), hUo⟩ := fun z hz => hCU C hC (hdom ▸ hz)
    have hZC := isZBGFFProcess_restrict_of_split hUH hdomU
      (show IsOpen ((H \ (R ∪ L)) \ ((cs C).dom : Set ℂ)) by rw [hdom]; exact hUC C hC) hZ
    have hTr := Chart.isZBGFFProcess_chartTransport hc (Chart.locallyIntegrableOn_of_continuousOn (hℓc C hC)) χ hZC
    refine ⟨by rw [hTC C hC]; exact (Chart.measurable_chartTransport hc 1 0 χ).comp hhm, fun u₀ hu₀ => ?_⟩
    have hmean' := hmean C hC u₀ hu₀
    have hu₀c : ContinuousOn u₀ H := hu₀.1.continuousOn
    have key : ∀ φ : TestOn upperHalfPlaneOpens,
        (∫ w, m ((cs C).2.1 w) * φ w) + χ * ∫ w, (cs C).2.2 ((cs C).2.1 w) * φ w = ∫ z, u₀ z * φ z := by
      intro φ
      have hφH : tsupport φ ⊆ H := φ.tsupport_subset
      have hpt : (fun w => m ((cs C).2.1 w) * φ w) =
          fun w => u₀ w * φ w - χ * ((cs C).2.2 ((cs C).2.1 w) * φ w) := by
        funext w
        by_cases hw : w ∈ tsupport φ
        · rw [hmean' w (hφH hw)]
          ring
        · rw [image_eq_zero_of_notMem_tsupport hw]
          ring
      rw [hpt, integral_sub (Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₀c φ hφH)
        ((Coupling.MartMeans2.integrable_mul_test_of_continuousOn (hℓc C hC) φ hφH).const_mul χ),
        integral_const_mul]
      ring
    have e : (fun φ ω => T C ω φ - ∫ z, u₀ z * φ z) = fun φ ω => Chart.chartTransport hc 1 0 χ (h ω) φ -
        ((∫ w, m ((cs C).2.1 w) * φ w) + χ * ∫ w, (cs C).2.2 ((cs C).2.1 w) * φ w) := by
      funext φ ω
      rw [hTC C hC, key φ]
    rw [e]
    exact hTr
  · -- independence
    have hX : IsGaussianProcess (fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ H \ (R ∪ L)}) ω =>
        h ω φ.1 - ∫ z, m z * φ.1 z) ν := by
      have hg := hZ.gaussian.comp_right fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ H \ (R ∪ L)}) =>
        LocalSets.testOnOfSubset (U := ⟨H \ (R ∪ L), hUo⟩) φ.1 φ.2
      have e : ((fun ψ ω => h ω (GFF.testIncl ⟨H \ (R ∪ L), hUo⟩ upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ∘
          fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ H \ (R ∪ L)}) =>
            LocalSets.testOnOfSubset (U := ⟨H \ (R ∪ L), hUo⟩) φ.1 φ.2) =
          fun φ ω => h ω φ.1 - ∫ z, m z * φ.1 z := by
        funext φ ω
        simp only [Function.comp_apply, LocalSets.testIncl_testOnOfSubset hUH]
        rfl
      rwa [e] at hg
    have hcov : ∀ φ ψ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (R ∪ L) → tsupport ψ ⊆ H \ (R ∪ L) →
        cov[fun ω => h ω φ - ∫ z, m z * φ z, fun ω => h ω ψ - ∫ z, m z * ψ z; ν] =
          QuantumZipper.zeroGFFTestCov (H \ (R ∪ L)) φ ψ := by
      intro φ ψ hφ hψ
      have := hZ.covariance_eq (LocalSets.testOnOfSubset (U := ⟨H \ (R ∪ L), hUo⟩) φ hφ)
        (LocalSets.testOnOfSubset (U := ⟨H \ (R ∪ L), hUo⟩) ψ hψ)
      simp only [LocalSets.testIncl_testOnOfSubset hUH] at this
      exact this
    exact iIndepFun_componentFields hUo (M := fun φ => ∫ z, m z * φ z) hX
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp hhm) hcov hcs htr

/-! ### The named input and the statement-level reductions -/

/-- **Named input: the marked union law of the two complete walks, with the GW3.1 mean, R51 form** (Lemma GW3,
proof, p. 636: "Their union, and the increasing proper completions of their last pieces, retain the marked Gaussian
union law"; "These prove (GW3.1) in the single connected normalization just fixed"). In the setting of
`GW3FieldLawOneChartRegStatement`, almost surely: `U = ℍ \ (R ∪ L)` is open, and for some mean `m` the field `h`
restricted to `U` is, under the conditional law `ν` given both walk histories, `m` plus the zero-boundary GFF of `U`;
and every component between the walks has a component chart in which `m ∘ inv + χ · lift ∘ inv` is the bounded
harmonic extension of a word `bC` satisfying (GW3.1). -/
def GW3UnionLawRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∃ (hUo : IsOpen (H \ (R ∪ L))) (m : ℂ → ℝ),
          LQGMetric.IsZBGFFProcess ⟨H \ (R ∪ L), hUo⟩
            (fun ψ ω => h ω (GFF.testIncl ⟨H \ (R ∪ L), hUo⟩ upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ν ∧
          ∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c ∧
            ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC ∧
              ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀ →
                ∀ w ∈ H, u₀ w = m (c.2.1 w) + QuantumZipper.chiC κ * c.2.2 (c.2.1 w)

/-- **Lemma GW3's field law in one choice of charts (R51 form) from the marked union law.** -/
theorem gw3FieldLawOneChartRegStatement_of_unionLaw (hU : GW3UnionLawRegStatement.{u}) :
    GW3FieldLawOneChartRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hU κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  obtain ⟨hUo, m, hZ, hcomp⟩ := hω
  exact exists_oneChart_of_unionLaw hh.1 hUo hZ hcomp

/-- **Lemma GW3's field law for every choice of charts (R51 form)** from the sided geometry, the walks' no common
continuum and the marked union law. -/
theorem gw3FieldLawRegStatement_of_unionLaw (hGS : GW3Sided.GW3GeometrySidedRegStatement.{u})
    (hN : WalkCont.WalkNoCommonContinuumRegStatement.{u}) (hU : GW3UnionLawRegStatement.{u}) :
    GW3FieldLawRegStatement.{u} :=
  GW3Sided.gw3FieldLawRegStatement_of_sided hGS hN (gw3FieldLawOneChartRegStatement_of_unionLaw hU)

end GW3Joint

end Theorem14

end InteractingSLE
