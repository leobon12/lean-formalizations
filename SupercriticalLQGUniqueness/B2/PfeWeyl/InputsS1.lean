import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsW3
import SupercriticalLQGUniqueness.B2.PfeWeyl.Inputs
import SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP
import SupercriticalLQGUniqueness.B2.Iface.Statements

 


























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
def SubseqLimitNormalized (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      (∀ᵐ ω ∂P,
        LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
          (D (h ω)).toLSCFun.1) ∧
      (∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
        ∀ᵐ ω ∂P,
          Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
            setDistance (lfppDistance (ξ : ℝ) (X (ε n) ω)) O O') atTop
            (𝓝 (setDistance (D (h ω)).1 O O')))

 

def NormalizedLimitGeometry (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    (∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace) ∧
    (∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)

 
def NormalizedAcrossTails (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ k : ℕ, AcrossTailInput P (fun ω => D (h ω)) ((k : ℝ) + 1) (Nat.cast_add_one_pos k)

 
def NormalizedSmallAnnuli (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
          (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))

 

def BoundedShiftWeyl (ξ : Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ F : Ω → C(ℂ, ℝ), Measurable F → (∀ ω, ∃ M : ℝ, ∀ z, |F ω z| ≤ M) →
      ∀ᵐ ω ∂P, (D (addFun (h ω) (F ω))).1 = weylScale (ξ : ℝ) (F ω) (D (h ω))

 

def NormalizedLscLimit (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      ∀ᵐ ω ∂P,
        LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
          (D (h ω)).toLSCFun.1

 




def NormalizedPointCircles (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      ∀ x y r x' y' r' : ℚ, 0 ≤ r → 0 ≤ r' → (r = 0 ∨ r' = 0) →
        ∀ᵐ ω ∂P,
          Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
            setDistance (lfppDistance (ξ : ℝ) (X (ε n) ω))
              (Metric.sphere (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ))
              (Metric.sphere (Complex.mk (x' : ℝ) (y' : ℝ)) (r' : ℝ))) atTop
            (𝓝 (setDistance (D (h ω)).1
              (Metric.sphere (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ))
              (Metric.sphere (Complex.mk (x' : ℝ) (y' : ℝ)) (r' : ℝ))))

end SupercriticalLQGUniqueness.B2.PfeWeyl
