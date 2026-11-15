/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3PrimeDomains
import InteractingSLE.Spec.Supplement.SBS3AssemblyData

/-!
# S3: construct the marked comparison from actual local-set means

Apply the committed per-prime-end Proposition 3.8 twice, through the same
actual union mean. Restrict the resulting harmonic representatives to the
intersection of the two protected component domains. Thus `MarkedUnionMeans`
is produced from local-set laws, rather than postulated as comparison data.
The statement applies to any probability measure, including a retained
conditional kernel when its local-set hypotheses have been established.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF CondIndepEv)
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open LocalSets

/-- Actual single and joint local-set means supply the marked comparison on
every common protected component domain, on one probability-one event for
all representatives, contact points and positive radii. -/
theorem ae_markedUnionMeans_of_freeNear {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A B : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hBm : Measurable[mΩ, hittingSigma] B)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hA : IsLocalSet A h P) (hB : IsLocalSet B h P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbB : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z))
    {GA GB : Ω → DistOn upperHalfPlaneOpens}
    (hGA : IsLocalSetMean A h P GA) (hGB : IsLocalSetMean B h P GB) :
    ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        GA ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω →
        GB ω φ = ∫ z, vB z * φ z) →
      ∀ p : ℂ, p ∈ A ω ∪ {z : ℂ | z.im = 0} → p ∈ B ω ∪ {z : ℂ | z.im = 0} →
      ∀ rA > 0, ∀ rB > 0,
        MarkedUnionMeans (A ω) (B ω)
          (FinRel.freeNear (B ω) (A ω) p rA ∩ FinRel.freeNear (A ω) (B ω) p rB) p vA vB := by
  obtain ⟨G, hG⟩ := IsLocalSet.isGermConditionalLaw_union hh hAm hBm hci hA hB
  have hG' : IsLocalSetMean (fun ω => B ω ∪ A ω) h P G := by
    rw [show (fun ω => B ω ∪ A ω) = (fun ω => A ω ∪ B ω) from
      funext fun ω => union_comm (B ω) (A ω)]
    exact hG
  have hcmpA := FinRel.ae_tendsto_sub_of_union_comp hh hBm hAm hci.symm hB hA hunbA hG' hGA
  have hcmpB := FinRel.ae_tendsto_sub_of_union_comp hh hAm hBm hci hA hB hunbB hG hGB
  filter_upwards [hcmpA, hcmpB, hA.2.1, hB.2.1] with
    ω ⟨ua, hua, hrepA, hlimA⟩ ⟨ub, hub, hrepB, hlimB⟩ hAo hBo
  intro vA vB hvA hvrA hvB hvrB p hpA hpB rA hrA rB hrB
  rw [union_comm (B ω) (A ω)] at hua hrepA
  have hO := inter_freeNear_subset_joint (A := A ω) (B := B ω) (p := p) (r₁ := rA) (r₂ := rB)
  refine ⟨(isOpen_freeNear hAo.2 p rA).inter (isOpen_freeNear hBo.2 p rB),
    hO.trans (sdiff_subset_sdiff_right subset_union_left),
    hO.trans (sdiff_subset_sdiff_right subset_union_right),
    G ω, GA ω, GB ω, ua, ub, hvA, hvrA, hvB, hvrB,
    (fun z hz => hua z (hO hz)), (fun φ hφ => hrepA φ (hφ.trans hO)),
    (fun z hz => hub z (hO hz)), (fun φ hφ => hrepB φ (hφ.trans hO)), ?_, ?_⟩
  · exact (hlimA p hpA rA hrA).mono_left (nhdsWithin_mono p inter_subset_left)
  · exact (hlimB p hpB rB hrB).mono_left (nhdsWithin_mono p inter_subset_right)

end InteractingSLE.Theorem14.SB.S3
