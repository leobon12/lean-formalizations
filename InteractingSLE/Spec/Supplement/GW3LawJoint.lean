/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkContinuum

/-!
# Lemma GW3's field law: the R51 form and the pointwise chart change

Packet PROVE-T14-GW7. Lemma GW3 (`source/spec/p625-671.md` L203–L226, pp. 636–637): conditionally on both complete
walks, in a common-lift chart of each between-component the field is a GFF with the boundary word (GW3.1), and the
component fields are conditionally independent.

The frozen Theorem 1.4 anchors (version 2, ruling R51) assume that every staged family is `StagedPiecesRegular`. This
file states Lemma GW3's field law and its one-chart form with that hypothesis (`GW3FieldLawRegStatement`,
`GW3FieldLawOneChartRegStatement`; the unregularized forms of PROVE-T14-GW5 imply them), together with the openness of
the between-components (`BetweenComponentsOpenRegStatement`), and proves the R51 form of PROVE-T14-GW5's reduction
"every chart from one chart" (`gw3FieldLawRegStatement_of_oneChart`). For this, PROVE-T14-GW5's argument is restated
pointwise (`exists_fieldLaw_of_oneChart`: fixed walks `R, L`, conditional law `ν`), so that both forms follow from one
proof.

The one-chart law itself (`GW3FieldLawOneChartRegStatement`) is not proved here; the exact missing ingredients are in
`planning/handoffs/PROVE-T14-GW7.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3Joint

open GW3Law

/-! ### The pointwise chart change -/

/-- **Lemma GW3's field law for every choice of charts, from one choice, pointwise** (PROVE-T14-GW5's
`gw3FieldLawStatement_of_oneChart`, for fixed walks `R`, `L`, ordinary parts `ordR`, `ordL` and conditional law `ν`).
If the between-components are open and the walks share no nondegenerate connected set, a field law in one choice of
component charts `cs₀` (with their lifts) gives the field law in every choice `cs`, with the lifts of `cs₀`. -/
theorem exists_fieldLaw_of_oneChart {κ : ℝ} {b : ℝ → ℝ} {R L ordR ordL : Set ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    (hO : ∀ C ∈ betweenComponents R L, IsOpen C)
    (hN : ∀ S ⊆ R ∩ L, IsPreconnected S → S.Subsingleton)
    (h1 : ∃ (cs : Set ℂ → Chart) (hC : Set ℂ → Ω → DistOn upperHalfPlaneOpens),
      (∀ C ∈ betweenComponents R L,
        IsComponentChart R L C (cs C) ∧
        (∀ ω, IsChartTransport (cs C) 1 0 (QuantumZipper.chiC κ) (h ω) (hC C ω)) ∧
        ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
          IsComponentBoundaryData κ b ordR ordL (cs C).2.1 bC jumpsC ∧
          IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
      iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν) :
    ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
      ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → DistOn upperHalfPlaneOpens),
        (∀ C ∈ betweenComponents R L,
          IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
          (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω) (hC C ω)) ∧
          ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
            IsComponentBoundaryData κ b ordR ordL (cs C).2.1 bC jumpsC ∧
            IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
        iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν := by
  intro cs hcs
  obtain ⟨cs₀, hC₀, hC₀p, hind⟩ := h1
  have hCH : ∀ C ∈ betweenComponents R L, C ⊆ H := by
    rintro C ⟨z, -, -, -, rfl⟩
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hdil : ∀ C ∈ betweenComponents R L, ∃ r : ℝ, 0 < r ∧ (∀ w ∈ H, (cs C).1 ((cs₀ C).2.1 w) = (r : ℂ) * w) ∧
      ∀ w ∈ H, (cs C).2.1 w = (cs₀ C).2.1 (w / r) := fun C hC =>
    inv_eq_of_isComponentChart (hC₀p C hC).1 (hcs C hC) (hO C hC) hN
  choose! r hr hfwd hinv using hdil
  set χ := QuantumZipper.chiC κ with hχ
  set T : Set ℂ → DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens := fun C x =>
    if hrC : 0 < r C then Chart.chartTransport (Chart.isConformal_dilation hrC) 1 0 χ x else x with hT
  have hTm : ∀ C, Measurable (T C) := fun C => by
    by_cases hrC : 0 < r C
    · simp only [hT, hrC, ↓reduceDIte]; exact Chart.measurable_chartTransport _ 1 0 χ
    · simp only [hT, hrC, ↓reduceDIte]; exact measurable_id
  refine ⟨fun C => (cs₀ C).2.2, fun C ω => T C (hC₀ C ω), fun C hC => ?_, ?_⟩
  · obtain ⟨hch₀, htr₀, bC, jumpsC, hpc, hbd, hgff⟩ := hC₀p C hC
    have hCo := hO C hC
    have hrC := hr C hC
    have hTC : T C = Chart.chartTransport (Chart.isConformal_dilation hrC) 1 0 χ := by
      funext x; simp only [hT, hrC, ↓reduceDIte]
    have hfwdC : EqOn (cs C).1 (fun z => (r C : ℂ) * (cs₀ C).1 z) C := by
      intro z hz
      have hw : (cs₀ C).1 z ∈ H := hch₀.2.1 hz
      have := hfwd C hC _ hw
      rwa [hch₀.2.2.2.1.1 hz] at this
    have hc₀ := isConformal_of_isComponentChart hch₀ hCo (hCH C hC)
    have hcD := Chart.isConformal_dilation hrC
    have hℓ₀ : ContinuousOn (fun w => (cs₀ C).2.2 ((cs₀ C).2.1 w)) H :=
      hch₀.2.2.2.2.2.1.comp hc₀.1.continuousOn hch₀.2.2.1
    have hℓD : ContinuousOn (fun w => (Chart.dilation (r C)).2.2 ((Chart.dilation (r C)).2.1 w)) H :=
      continuousOn_const
    refine ⟨isComponentChart_lift hch₀ (hcs C hC) hCo hrC hfwdC, fun ω => ?_, ?_⟩
    · have ht₂ := Chart.isChartTransport_chartTransport hcD (Chart.locallyIntegrableOn_of_continuousOn hℓD) 1 0 χ
        (hC₀ C ω)
      have ht := IsChartTransport.trans hc₀ hcD hℓ₀ hℓD (htr₀ ω) ht₂
      show IsChartTransport ((cs C).1, (cs C).2.1, (cs₀ C).2.2) 1 0 χ (h ω) (T C (hC₀ C ω))
      rw [hTC]
      refine isChartTransport_congr (c := (cs₀ C).trans (Chart.dilation (r C)))
        (c' := ((cs C).1, (cs C).2.1, (cs₀ C).2.2)) hCo
        (fun w hw => hch₀.2.2.1 (Chart.div_mem_H hrC hw)) (fun w hw => hinv C hC w hw)
        (fun z hz => hfwdC hz) (fun z _ => ?_) ht
      simp only [Chart.trans_lift, Chart.dilation_lift, zero_add]
    · refine ⟨fun x => bC (x / r C), jumpsC.image fun y => r C * y, isPiecewiseConstant_dilation hrC hpc,
        isComponentBoundaryData_dilation hrC (hinv C hC) hbd, ?_⟩
      show IsGFFWithBoundaryData ν (fun ω => T C (hC₀ C ω)) _ _
      rw [show (fun ω => T C (hC₀ C ω)) = fun ω => Chart.chartTransport hcD 1 0 χ (hC₀ C ω) from by rw [hTC]]
      exact_mod_cast isGFFWithBoundaryData_dilation hrC χ hgff
  · exact hind.comp (fun C => T C.1) fun C => hTm C.1

/-! ### The statements in the R51 form -/

/-- **Named input: Lemma GW3's field law in one choice of component charts, R51 form**:
`GW3Law.GW3FieldLawOneChartStatement` for staged families that are also `StagedPiecesRegular`. -/
def GW3FieldLawOneChartRegStatement : Prop :=
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
        ∃ (cs : Set ℂ → Chart) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C (cs C) ∧
            (∀ ω, IsChartTransport (cs C) 1 0 (QuantumZipper.chiC κ) (h ω) (hC C ω)) ∧
            ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν

/-- **Lemma GW3's field law, R51 form**: `GW4.GW3FieldLawStatement` for staged families that are also
`StagedPiecesRegular`. -/
def GW3FieldLawRegStatement : Prop :=
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
        ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
          ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens),
            (∀ C ∈ betweenComponents R L,
              IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
              (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
                (hC C ω)) ∧
              ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
                IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                  (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
                IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν

/-- **The components between the walks are open, R51 form**: `GW3Word.BetweenComponentsOpenStatement` for staged
families that are also `StagedPiecesRegular`. -/
def BetweenComponentsOpenRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)), IsOpen C

/-! ### Bridges and the reduction -/

/-- The unregularized one-chart law implies its R51 form. -/
theorem gw3FieldLawOneChartRegStatement_of_unreg (h1 : GW3Law.GW3FieldLawOneChartStatement.{u}) :
    GW3FieldLawOneChartRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact h1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized field law implies its R51 form. -/
theorem gw3FieldLawRegStatement_of_unreg (hF : GW4.GW3FieldLawStatement.{u}) : GW3FieldLawRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized openness of the between-components implies its R51 form. -/
theorem betweenComponentsOpenRegStatement_of_unreg (hO : GW3Word.BetweenComponentsOpenStatement.{u}) :
    BetweenComponentsOpenRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- **Lemma GW3's field law for every choice of component charts, R51 form**, from the law in one choice of charts,
open components and no common continuum of the walks (PROVE-T14-GW5's reduction, through
`exists_fieldLaw_of_oneChart`). -/
theorem gw3FieldLawRegStatement_of_oneChart (hO : BetweenComponentsOpenRegStatement.{u})
    (hN : WalkCont.WalkNoCommonContinuumRegStatement.{u}) (h1 : GW3FieldLawOneChartRegStatement.{u}) :
    GW3FieldLawRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    h1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hOω hNω h1ω
  exact exists_fieldLaw_of_oneChart hOω hNω h1ω

end GW3Joint

end Theorem14

end InteractingSLE
