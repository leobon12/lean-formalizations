import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.InterfaceV2




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 
def PrintedSizeWindow (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (ε b r : Set.Ioi (0 : ℝ)) (hbr hrz : ℝ) : Prop :=
  ε ^ (2 * (ξ : ℝ) * (Q + 3)) * b ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * hbr) ≤
    r ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ∧
  r ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ≤
    ε ^ ((ξ : ℝ) * (Q - 3)) *
      b ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)

 

def PrintedCountingBadEventV2 {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cPlus : ℝ≥0∞)
    (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set DistC)
    (b ε : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) : Set Ω :=
  {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ ≥
      cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ -
        ENNReal.ofReal ((1 / 2 : ℝ) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) *
          (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) ∧
    (∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ ε * (b : ℝ) →
      ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
        ∃ hrz : ℝ, IsCircleAverage (h ω) r z hrz ∧
          PrintedSizeWindow ξ Q ε b r hbr hrz) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈
          Metric.ball z ((r : ℝ) / 25) ∧
        h ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)}

 
def PrintedOpenEndSavingV2 {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cPlus : ℝ≥0∞)
    (b ν δ κ : Set.Ioi (0 : ℝ)) : Set Ω :=
  {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    ∀ i j : ℤ × ℤ,
      let s := (δ : ℝ) ^ (ν : ℝ) * (b : ℝ)
      let z := LQGMetric.GM.gridPt (s / 100) i
      let w := LQGMetric.GM.gridPt (s / 100) j
      z ∈ Metric.ball (0 : ℂ) b → w ∈ Metric.ball (0 : ℂ) b →
      κ * (b : ℝ) ≤ dist z w →
      κ * (b : ℝ) ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b) →
      OptimalConstants.Ratios.setDist (D' (h ω)) (Metric.ball z s) (Metric.ball w s) ≤
        cPlus * OptimalConstants.Ratios.setDist (D (h ω)) (Metric.ball z s) (Metric.ball w s) -
          ENNReal.ofReal ((δ : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * hbr))}

 

theorem PrintedSizeWindow.to_corrected
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (ε b r : Set.Ioi (0 : ℝ))
    (hε : (ε : ℝ) ≤ 1) (hbr hrz : ℝ)
    (h : PrintedSizeWindow ξ Q ε b r hbr hrz) :
    SizeWindow ξ Q ε b r hbr hrz := by
  rcases h with ⟨hlower, hupper⟩
  refine ⟨hlower, hupper.trans ?_⟩
  have hex : (ξ : ℝ) * min (Q - 3) (2 * (Q - 3)) ≤
      (ξ : ℝ) * (Q - 3) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) ξ.property.le
  have hp : (ε : ℝ) ^ ((ξ : ℝ) * (Q - 3)) ≤
      (ε : ℝ) ^ ((ξ : ℝ) * min (Q - 3) (2 * (Q - 3))) :=
    Real.rpow_le_rpow_of_exponent_ge ε.property hε hex
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (Real.rpow_pos_of_pos b.property _).le)
    (Real.exp_pos _).le

 

theorem printedCountingBadEvent_subset_corrected
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set DistC)
    (b ε : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hε : (ε : ℝ) ≤ 1) :
    PrintedCountingBadEventV2 h D D' ξ Q cPlus R event b ε K₁ K₂ ⊆
      CountingBadEventV2 h D D' ξ Q cPlus R event b ε K₁ K₂ := by
  intro ω hω
  rcases hω with ⟨hbr, hcircle, hgap, hsize, hcover⟩
  refine ⟨hbr, hcircle, hgap, ?_, hcover⟩
  intro r hr hrlo hrhi z hz
  obtain ⟨hrz, hcircleR, hwindow⟩ := hsize r hr hrlo hrhi z hz
  exact ⟨hrz, hcircleR, hwindow.to_corrected ξ Q ε b r hε hbr hrz⟩

 
def T58Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus) : Prop :=
  ∀ pbar : Set.Ioo (0 : ℝ) 1,
    Nonempty (ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)

 

def C45CorrectedNonemptyInternal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii)
    (params : Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r) : Prop :=
  ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
      ∀ K₁ K₂ : Set ℂ,
        K₁.Nonempty → K₂.Nonempty → IsCompact K₁ → IsCompact K₂ →
        Disjoint K₁ K₂ →
        K₁ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        K₂ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ K₂ →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
          euclidSetDist K₁ (Metric.sphere (0 : ℂ) b) →
        P (CountingBadEventV2 h D D' ξ Q cPlus R
          (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂) ≤
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ))

 

def C45Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii)
    (params : Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r) : Prop :=
  ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
      ∀ K₁ K₂ : Set ℂ,
        IsCompact K₁ → IsCompact K₂ →
        Disjoint K₁ K₂ →
        K₁ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        K₂ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ K₂ →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
          euclidSetDist K₁ (Metric.sphere (0 : ℂ) b) →
        P (PrintedCountingBadEventV2 h D D' ξ Q cPlus R
          (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂) ≤
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ))

 

theorem c45_printed_of_corrected_nonempty
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii)
    (params : Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r)
    (hCorrected : C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar R params family) :
    ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
      ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
        ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
        ∀ K₁ K₂ : Set ℂ,
          K₁.Nonempty → K₂.Nonempty → IsCompact K₁ → IsCompact K₂ →
          Disjoint K₁ K₂ →
          K₁ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
          K₂ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
          ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ K₂ →
          ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
            euclidSetDist K₁ (Metric.sphere (0 : ℂ) b) →
          P (PrintedCountingBadEventV2 h D D' ξ Q cPlus R
            (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂) ≤
            ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)) := by
  intro μ η
  obtain ⟨C, ε₀, hEstimate⟩ := hCorrected μ η
  refine ⟨C, ε₀, ?_⟩
  intro ε hε hεsmall b K₁ K₂ hK₁ hK₂ hCompact₁ hCompact₂ hDisj
    hBall₁ hBall₂ hDist hSphere
  have hεone : ε ≤ 1 := le_trans hεsmall ε₀.property.2.le
  exact (measure_mono (printedCountingBadEvent_subset_corrected h D D' ξ Q
    cPlus R (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂ hεone)).trans
    (hEstimate ε hε hεsmall b K₁ K₂ hK₁ hK₂ hCompact₁ hCompact₂
      hDisj hBall₁ hBall₂ hDist hSphere)

 

def R52ClosedEndSavingInternal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar) : Prop :=
  ∀ (ν κG κEnd : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
      ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ → ∀ b : Set.Ioi (0 : ℝ),
        ENNReal.ofReal (κG : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κG
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg
              objs.cMid'_lower⟩) →
        ENNReal.ofReal (1 - (η : ℝ)) ≤
          P (ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd)

 


def R52Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    : Prop :=
  ∃ pbar : Set.Ioo (0 : ℝ) 1,
    ∃ objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar,
  ∀ (ν κG κEnd : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
      ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ → ∀ b : Set.Ioi (0 : ℝ),
        ENNReal.ofReal (κG : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κG
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg
              objs.cMid'_lower⟩) →
        ENNReal.ofReal (1 - (η : ℝ)) ≤
          P (PrintedOpenEndSavingV2 h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd)

 

def R53OfObjectsInternal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (θ : Set.Ioi (0 : ℝ)) : Prop :=
  ∀ (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
    (p : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) cPlus.toReal,
      ∀ δ : ℝ, (hδ : 0 < δ) → (hδsmall : δ ≤ δ₀) →
      ∀ b : Set.Ioi (0 : ℝ),
        ENNReal.ofReal (κ : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg
              objs.cMid'_lower⟩) →
        P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q b a
          ⟨cPlus.toReal - δ,
            by exact sub_pos.mpr (lt_of_le_of_lt hδsmall δ₀.property.2)⟩ θ g}) <
            ENNReal.ofReal (p : ℝ)
 

def R53Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    : Prop :=
  ∃ pbar : Set.Ioo (0 : ℝ) 1,
    ∃ objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar,
  ∀ θ : Set.Ioi (0 : ℝ), ∀ (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
    (p : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) cPlus.toReal,
      ∀ δ : ℝ, (hδ : 0 < δ) → (hδsmall : δ ≤ δ₀) →
      ∀ b : Set.Ioi (0 : ℝ),
        ENNReal.ofReal (κ : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg
              objs.cMid'_lower⟩) →
        P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q b a
          ⟨cPlus.toReal - δ,
            by exact sub_pos.mpr (lt_of_le_of_lt hδsmall δ₀.property.2)⟩ θ g}) <
            ENNReal.ofReal (p : ℝ)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
