import SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs
import SupercriticalLQGUniqueness.B2.Median.Inputs
import SupercriticalLQGUniqueness.B2.PfeLocal.OpenInternalBridge
import SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent

 

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs

open SupercriticalLQGUniqueness.B2.Iface

 
def LimitEuclideanControl0 : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), IsLFPPExponent ξ Q →
    ∀ (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric),
    (∀ δ, IsLFPPNormalizer ξ δ (m δ)) →
    Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
    SubseqLimit ξ m ε D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
        ∃ η : ℝ, 0 < η ∧
          ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ

 
def LimitLengthSpace0 : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), IsLFPPExponent ξ Q →
    ∀ (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric),
    (∀ δ, IsLFPPNormalizer ξ δ (m δ)) →
    Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
    SubseqLimit ξ m ε D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace

 
theorem limitEuclideanControl0_of_limitEuclideanControl
    (h : LimitEuclideanControl) : LimitEuclideanControl0 :=
  fun ξ _Q _hQ m ε D _hm _hε hD => h ξ m ε D hD

 
theorem limitLengthSpace0_of_limitLengthSpace
    (h : LimitLengthSpace) : LimitLengthSpace0 :=
  fun ξ _Q _hQ m ε D _hm _hε hD => h ξ m ε D hD

 
theorem ae_finitePathsEuclideanContinuous_of_inputs0
    (hInput : LimitEuclideanControl0)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, FinitePathsEuclideanContinuous (D (h ω)) := by
  filter_upwards [hInput ξ Q hQ m ε D hm hε hD P h hh] with ω hω
  exact finitePathsEuclideanContinuous_of_control (D (h ω)) hω

 

theorem ae_euclideanForget_continuous_of_inputs0
    (hInput : LimitEuclideanControl0)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Continuous (B2.Median.Inputs.euclideanForget (D (h ω))) := by
  filter_upwards [hInput ξ Q hQ m ε D hm hε hD P h hh] with ω hω
  exact B2.PfeLocal.continuous_euclidForget_of_small_metric (D (h ω)) hω

 


theorem ae_euclideanForget_continuous_of_inputs0_existsExponent
    (hInput : LimitEuclideanControl0)
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Continuous (B2.Median.Inputs.euclideanForget (D (h ω))) := by
  obtain ⟨Q, hQ, _⟩ := existsUnique_isLFPPExponent ξ
  exact ae_euclideanForget_continuous_of_inputs0 hInput ξ Q hQ m ε D
    hm hε hD P h hh

end SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs
