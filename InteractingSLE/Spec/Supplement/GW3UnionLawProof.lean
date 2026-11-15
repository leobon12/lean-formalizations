/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawJointUnion

/-!
# Lemma GW3's union law on the components between the walks

Packet PROVE-T14-WALKLAW. Lemma GW3, proof (`source/spec/p625-671.md` L210–L226, pp. 636–637): "The two finite-stage
marked local sets have their complete kernels by GW1. Their union […] retain[s] the marked Gaussian union law. […]
Marked union locality gives the zero-boundary Green covariance and the conditional independence of the component
fields." Follow-up note D.6 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L934–L1004): "The marked union
kernel supplies the zero-boundary Green covariance and conditional independence **in the selected components**."

PROVE-T14-GW7's named input `GW3Joint.GW3UnionLawRegStatement` asks for the zero-boundary law of the field on the
whole complement `ℍ \ (R ∪ L)` of the two walks, including the pockets cut off by one walk alone (the components on
the right of `R` or on the left of `L`). Its only consumer, the one-chart field law
`GW3Joint.GW3FieldLawOneChartRegStatement`, reads the field on the components **between** the walks only. This file
records the weaker input that the consumer needs and proves the reduction:

* `betweenUnion R L`: the union of the components between the walks; it is open with open complement in
  `ℍ \ (R ∪ L)` (`isOpen_betweenUnion`, `isOpen_sdiff_betweenUnion`);
* **`GW3UnionLawBetweenRegStatement`** (named input): the union law of `GW3UnionLawRegStatement` on `betweenUnion R L`
  instead of `ℍ \ (R ∪ L)` (no pocket kernels);
* `gw3UnionLawBetweenRegStatement_of_unionLaw`: it follows from `GW3UnionLawRegStatement` (restriction to an open
  union of components);
* **`exists_oneChart_of_betweenLaw`**, **`gw3FieldLawOneChartRegStatement_of_betweenLaw`**: the one-chart field law
  from the between-component union law (PROVE-T14-GW7's `exists_oneChart_of_unionLaw` with the covariance and the
  independence taken on `betweenUnion R L`).

So the pockets of each walk need no conditional kernel for Theorem 1.4's component kernels: Part D.2's "earlier frozen
fields keep their kernels" is used only for components that end up between the walks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3Between

open GW3Joint

/-! ### The union of the components between the walks -/

section Union

variable {R L : Set ℂ}

/-- The union of the components between the walks `R` and `L`. -/
def betweenUnion (R L : Set ℂ) : Set ℂ := ⋃₀ betweenComponents R L

theorem subset_betweenUnion {C : Set ℂ} (hC : C ∈ betweenComponents R L) : C ⊆ betweenUnion R L :=
  subset_sUnion_of_mem hC

theorem betweenUnion_subset : betweenUnion R L ⊆ H \ (R ∪ L) := by
  refine sUnion_subset fun C hC => ?_
  obtain ⟨z, -, rfl⟩ := exists_eq_connectedComponentIn_of_mem_betweenComponents hC
  exact connectedComponentIn_subset _ _

theorem isOpen_betweenUnion (hUo : IsOpen (H \ (R ∪ L))) : IsOpen (betweenUnion R L) :=
  isOpen_sUnion fun C hC => by
    obtain ⟨z, -, rfl⟩ := exists_eq_connectedComponentIn_of_mem_betweenComponents hC
    exact hUo.connectedComponentIn

/-- The component of `ℍ \ (R ∪ L)` of a point between the walks is a component between the walks. -/
theorem connectedComponentIn_mem_betweenComponents {z : ℂ} (hz : z ∈ betweenUnion R L) :
    connectedComponentIn (H \ (R ∪ L)) z ∈ betweenComponents R L := by
  obtain ⟨C, hC, hzC⟩ := hz
  obtain ⟨w, -, rfl⟩ := exists_eq_connectedComponentIn_of_mem_betweenComponents hC
  rw [← connectedComponentIn_eq hzC]
  exact hC

/-- The rest of the complement of the walks outside the between components is open (a union of components). -/
theorem isOpen_sdiff_betweenUnion (hUo : IsOpen (H \ (R ∪ L))) :
    IsOpen ((H \ (R ∪ L)) \ betweenUnion R L) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨connectedComponentIn (H \ (R ∪ L)) z,
    fun w hw => ⟨connectedComponentIn_subset _ _ hw, fun hwB => hz.2 ?_⟩, hUo.connectedComponentIn,
    mem_connectedComponentIn hz.1⟩
  have h1 := connectedComponentIn_mem_betweenComponents hwB
  rw [← connectedComponentIn_eq hw] at h1
  exact subset_betweenUnion h1 (mem_connectedComponentIn hz.1)

/-- A between component is open, and so is the rest of the between union. -/
theorem isOpen_of_mem_betweenComponents (hUo : IsOpen (H \ (R ∪ L))) {C : Set ℂ}
    (hC : C ∈ betweenComponents R L) : IsOpen C := by
  obtain ⟨z, -, rfl⟩ := exists_eq_connectedComponentIn_of_mem_betweenComponents hC
  exact hUo.connectedComponentIn

theorem isOpen_betweenUnion_sdiff (hUo : IsOpen (H \ (R ∪ L))) {C : Set ℂ} (hC : C ∈ betweenComponents R L) :
    IsOpen (betweenUnion R L \ C) := by
  obtain ⟨z, -, rfl⟩ := exists_eq_connectedComponentIn_of_mem_betweenComponents hC
  have e : betweenUnion R L \ connectedComponentIn (H \ (R ∪ L)) z =
      betweenUnion R L ∩ ((H \ (R ∪ L)) \ connectedComponentIn (H \ (R ∪ L)) z) := by
    ext w
    simp only [Set.mem_sdiff, mem_inter_iff]
    exact ⟨fun h => ⟨h.1, betweenUnion_subset h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact (isOpen_betweenUnion hUo).inter (isOpen_sdiff_connectedComponentIn hUo z)

end Union

/-! ### The named input -/

/-- **Named input: the marked union law of the two complete walks on the components between them, R51 form**
(Lemma GW3, proof, p. 636; follow-up note D.6, L983: "The marked union kernel supplies the zero-boundary Green
covariance and conditional independence in the selected components"). `GW3Joint.GW3UnionLawRegStatement` with the
zero-boundary law asked on the union of the between components instead of the whole complement `ℍ \ (R ∪ L)`: in the
setting of `GW3FieldLawOneChartRegStatement`, almost surely `ℍ \ (R ∪ L)` is open, and for some mean `m` the field `h`
restricted to the between components is, under the conditional law `ν` given both walk histories, `m` plus the
zero-boundary GFF of their union; and every component between the walks has a component chart in which
`m ∘ inv + χ · lift ∘ inv` is the bounded harmonic extension of a word `bC` satisfying (GW3.1). -/
def GW3UnionLawBetweenRegStatement : Prop :=
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
          LQGMetric.IsZBGFFProcess ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩
            (fun ψ ω => h ω (GFF.testIncl ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩ upperHalfPlaneOpens ψ) -
              ∫ z, m z * ψ z) ν ∧
          ∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c ∧
            ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC ∧
              ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u₀ →
                ∀ w ∈ H, u₀ w = m (c.2.1 w) + QuantumZipper.chiC κ * c.2.2 (c.2.1 w)

/-! ### The between law from the full union law -/

/-- **The union law on the whole complement gives it on the between components** (restriction to an open union of
components). -/
theorem gw3UnionLawBetweenRegStatement_of_unionLaw (hU : GW3UnionLawRegStatement.{u}) :
    GW3UnionLawBetweenRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hU κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  obtain ⟨hUo, m, hZ, hcomp⟩ := hω
  refine ⟨hUo, m, ?_, hcomp⟩
  have hUH : (⟨H \ (ExplState.physSet κ b jumps wR (fun k => E wR k ω₀) ∪
      ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)), hUo⟩ : TopologicalSpace.Opens ℂ) ≤
      upperHalfPlaneOpens := fun z hz => hz.1
  exact isZBGFFProcess_restrict_of_split hUH (fun z hz => betweenUnion_subset hz)
    (isOpen_sdiff_betweenUnion hUo) hZ

/-! ### The one-chart field law from the between law -/

/-- **Lemma GW3's field law in one choice of charts, pointwise, from the between law.** As
`GW3Joint.exists_oneChart_of_unionLaw`, with the zero-boundary law of `h − m` asked only on the union of the components
between the walks. -/
theorem exists_oneChart_of_betweenLaw {κ : ℝ} {b : ℝ → ℝ} {R L ordR ordL : Set ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) (hUo : IsOpen (H \ (R ∪ L)))
    {m : ℂ → ℝ}
    (hZ : LQGMetric.IsZBGFFProcess ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩
      (fun ψ ω => h ω (GFF.testIncl ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩ upperHalfPlaneOpens ψ) -
        ∫ z, m z * ψ z) ν)
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
  set B : TopologicalSpace.Opens ℂ := ⟨betweenUnion R L, isOpen_betweenUnion hUo⟩ with hBdef
  have hBH : B ≤ upperHalfPlaneOpens := fun z hz => (betweenUnion_subset hz).1
  have hCo : ∀ C ∈ betweenComponents R L, IsOpen C := fun C hC => isOpen_of_mem_betweenComponents hUo hC
  have hCB : ∀ C ∈ betweenComponents R L, C ⊆ betweenUnion R L := fun C hC => subset_betweenUnion hC
  have hBC : ∀ C ∈ betweenComponents R L, IsOpen (betweenUnion R L \ C) := fun C hC =>
    isOpen_betweenUnion_sdiff hUo hC
  have hconf : ∀ C ∈ betweenComponents R L, (cs C).IsConformal := fun C hC =>
    GW3Law.isConformal_of_isComponentChart (hcs C hC) (hCo C hC)
      ((hCB C hC).trans (betweenUnion_subset.trans sdiff_subset))
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
    have hdomB : (cs C).dom ≤ B := fun z hz => hCB C hC (hdom ▸ hz)
    have hZC := isZBGFFProcess_restrict_of_split hBH hdomB
      (show IsOpen ((B : Set ℂ) \ ((cs C).dom : Set ℂ)) by rw [hdom]; exact hBC C hC) hZ
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
  · -- independence, from the Gaussian law on the between union
    have hX : IsGaussianProcess (fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ betweenUnion R L}) ω =>
        h ω φ.1 - ∫ z, m z * φ.1 z) ν := by
      have hg := hZ.gaussian.comp_right fun (φ : {φ : TestOn upperHalfPlaneOpens //
        tsupport φ ⊆ betweenUnion R L}) => LocalSets.testOnOfSubset (U := B) φ.1 φ.2
      have e : ((fun ψ ω => h ω (GFF.testIncl B upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ∘
          fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ betweenUnion R L}) =>
            LocalSets.testOnOfSubset (U := B) φ.1 φ.2) =
          fun φ ω => h ω φ.1 - ∫ z, m z * φ.1 z := by
        funext φ ω
        simp only [Function.comp_apply, LocalSets.testIncl_testOnOfSubset hBH]
        rfl
      rwa [e] at hg
    have hcov : ∀ φ ψ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ betweenUnion R L →
        tsupport ψ ⊆ betweenUnion R L →
        cov[fun ω => h ω φ - ∫ z, m z * φ z, fun ω => h ω ψ - ∫ z, m z * ψ z; ν] =
          zeroGFFTestCov (betweenUnion R L) φ ψ := by
      intro φ ψ hφ hψ
      have := hZ.covariance_eq (LocalSets.testOnOfSubset (U := B) φ hφ) (LocalSets.testOnOfSubset (U := B) ψ hψ)
      simp only [LocalSets.testIncl_testOnOfSubset hBH] at this
      exact this
    have hcc : ∀ C : betweenComponents R L, ∃ z ∈ H \ (R ∪ L),
        C.1 = connectedComponentIn (H \ (R ∪ L)) z :=
      fun C => exists_eq_connectedComponentIn_of_mem_betweenComponents C.2
    choose z hz hCz using hcc
    have hd : Pairwise fun C C' : betweenComponents R L => Disjoint C.1 C'.1 := fun C C' hne => by
      show Disjoint C.1 C'.1
      rw [hCz C, hCz C']
      refine disjoint_connectedComponentIn_of_ne fun he => hne (Subtype.ext ?_)
      rw [hCz C, hCz C', he]
    exact iIndepFun_of_isChartTransport (C := fun C : betweenComponents R L => C.1)
      (c := fun C : betweenComponents R L => cs C.1) (isOpen_betweenUnion hUo)
      (fun w hw => (betweenUnion_subset hw).1) hX (fun φ => (LQGMetric.measurable_distOn_apply φ).comp hhm) hcov
      (fun C => hCo C.1 C.2) (fun C => hBC C.1 C.2) (fun C => hCB C.1 C.2) hd (fun C => hconf C.1 C.2)
      (fun C => (hcs C.1 C.2).2.2.1.image_subset) fun C ω => htr C.1 C.2 ω

/-- **Lemma GW3's field law in one choice of charts (R51 form) from the between-component union law.** -/
theorem gw3FieldLawOneChartRegStatement_of_betweenLaw (hU : GW3UnionLawBetweenRegStatement.{u}) :
    GW3FieldLawOneChartRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hU κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  obtain ⟨hUo, m, hZ, hcomp⟩ := hω
  exact exists_oneChart_of_betweenLaw hh.1 hUo hZ hcomp

end GW3Between

end Theorem14

end InteractingSLE
