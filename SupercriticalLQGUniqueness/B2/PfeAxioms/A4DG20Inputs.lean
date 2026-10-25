import SupercriticalLQGUniqueness.B2.DG20Lim.DG20LimitSkCOfInputs
import SupercriticalLQGUniqueness.B2.PfeAxioms.A4RealAxiomV
import SupercriticalLQGUniqueness.B2.PfeAxioms.A3W3MeasurableSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationLimitSkC

 












set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem dg20LimitSkC_of_dg20Inputs
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive) : B2.DG20Lim.DG20LimitSkC :=
  B2.DG20Lim.dg20LimitSkC_of_inputs hS hPerc hRatio hRel hPos B2.LscTop.iface_lscTop

 
theorem limitLengthSpace0_of_dg20Inputs
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive) : Inputs.LimitLengthSpace0 := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  exact B2.DG20Lim.limitLengthSpace0_of_dg20LimitSkC
    (dg20LimitSkC_of_dg20Inputs hS hPerc hRatio hRel hPos)

 
theorem limitEuclideanControl0_of_dg20Inputs
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive) : Inputs.LimitEuclideanControl0 := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  exact B2.DG20Lim.limitEuclideanControl0_of_dg20LimitSkC
    (dg20LimitSkC_of_dg20Inputs hS hPerc hRatio hRel hPos)

 

theorem exists_pfe_normalizer_axiomV_of_dg20Inputs
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        (∃ Λ : ℝ, 1 < Λ ∧
          ∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
            Λ⁻¹ * (δ : ℝ) ^ Λ ≤
              (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              Λ * (δ : ℝ) ^ (-Λ)) ∧
        ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ D : DistC → LSCMetric,
          SubseqLimit ξ m (fun n => ε (φ (ψ n))) D →
          PfeWeyl.NormalizedSmallAnnuli ξ m (fun n => ε (φ (ψ n))) D →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
            ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
            (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
            ∀ A : EuclideanAnnulus,
              IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
                ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
                  acrossDist (D (h ω)) (A.dilate r r.2)) ∧
              IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
                ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
                  aroundDist (D (h ω)) (A.dilate r r.2)) := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  exact exists_pfe_normalizer_axiomV_of_skC
    (dg20LimitSkC_of_dg20Inputs hS hPerc hRatio hRel hPos) hS hPerc ξ Q hQ m hm ε hε

 
theorem xiAdditiveLocality_of_dg20Inputs_w3
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hgeo : ∀ k : ℕ, PfeWeyl.AcrossTailInput P (fun ω => D (h ω))
      ((k : ℝ) + 1) (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V) :
    B2.PfeLocal.Inputs.LscXiAdditiveLocality (ξ : ℝ) P h
      (fun ω => D (h ω)) := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  exact xiAdditiveLocality_of_dg20LimitSkC_w3
    (dg20LimitSkC_of_dg20Inputs hS hPerc hRatio hRel hPos)
    ξ Q hQ m hm ε hε D hD P h hh X hX hgeo hsmall hAnn

 
theorem ae_translation_of_dg20Inputs_w3
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (hRatio : DG20QuantileRatio) (hRel : DG20ExponentRelation)
    (hPos : DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (htail : PfeWeyl.NormalizedAcrossTails D)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε D)
    (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      D (translateDist z (h ω)) (u, v) = D (h ω) (u + z, v + z) := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  exact ae_translation_of_dg20LimitSkC_w3
    (dg20LimitSkC_of_dg20Inputs hS hPerc hRatio hRel hPos)
    ξ Q hQ m hm ε hε D hD P h hh X hX htail hsmall z

end SupercriticalLQGUniqueness.B2.PfeAxioms
