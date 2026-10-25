import SupercriticalLQGUniqueness.B2.PfeAxioms.S2Identities
import SupercriticalLQGUniqueness.B2.PfeAxioms.A4RealAxiomV
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Circles

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem subseqLimit_patchWitness (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric)
    (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)
    (hpts : PfeWeyl.NormalizedPointCircles ξ m ε Φ) :
    SubseqLimit ξ m ε (patchWitness ξ m ε) :=
  PfeWeyl.subseqLimit_of_normalized_of_inputs ξ m ε hε (patchWitness ξ m ε)
    (PfeWeyl.subseqLimitNormalized_of_inputs ξ m ε (patchWitness ξ m ε)
      (normalizedLscLimit_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)
      (normalizedSmallAnnuli_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)
      (normalizedPointCircles_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall hpts))
    (normalizedLimitGeometry_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)
    (normalizedAcrossTails_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)
    (normalizedSmallAnnuli_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)
    (boundedShiftWeyl_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)

 

theorem pfeAxiomV_patchWitness
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Φ : DistC → LSCMetric)
    (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    (htail : PfeWeyl.NormalizedAcrossTails Φ)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)
    (hpts : PfeWeyl.NormalizedPointCircles ξ m ε Φ)
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
        (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
        ∀ A : EuclideanAnnulus,
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
              acrossDist (patchWitness ξ m ε (h ω)) (A.dilate r r.2)) ∧
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
              aroundDist (patchWitness ξ m ε (h ω)) (A.dilate r r.2)) :=
  pfeAxiomV_of_section4_perc_skC hSkC hS hPerc ξ Q hQ m hm ε hε (patchWitness ξ m ε)
    (subseqLimit_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall hpts)
    (normalizedSmallAnnuli_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall) c hc Λ hΛ hV

end SupercriticalLQGUniqueness.B2.PfeAxioms
