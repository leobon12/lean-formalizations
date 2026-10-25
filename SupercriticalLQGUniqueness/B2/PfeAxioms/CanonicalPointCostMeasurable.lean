import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4BufferedFinite

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem aemeasurable_canonical_normalized_crossLenIn
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (δ : Ioo (0 : ℝ) 1)
    (U : TopologicalSpace.Opens ℂ) (hUc : IsConnected (U : Set ℂ))
    (x y : ℂ) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    AEMeasurable (fun g : DistC =>
      ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
        crossLenIn (ξ : ℝ) (heatMollify (δ : ℝ) g) U {x} {y}) normGFFLaw := by
  let : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hh := normalized_canonical_model.2
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  let E (t : Ioi (0 : ℝ)) := exists_heatVersion_bdd hb t
  let X (t : Ioi (0 : ℝ)) : DistC → C(ℂ, ℝ) := (E t).choose
  have hX : ∀ t, IsHeatSmoothing normGFFLaw id t (X t) :=
    fun t => (E t).choose_spec.2
  have hcost := (hS ξ Q hQ m hm).1 normGFFLaw id hh X hX U hUc x y hx hy hxy
  have hEq : ∀ᵐ g ∂normGFFLaw,
      ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
        crossLenIn (ξ : ℝ) (heatMollify (δ : ℝ) g) U {x} {y} =
      ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
        crossLenIn (ξ : ℝ) (X ⟨(δ : ℝ), δ.property.1⟩ g) U {x} {y} := by
    filter_upwards [(E ⟨(δ : ℝ), δ.property.1⟩).choose_spec.1] with g hg
    congr 1
    congr 1
    funext z
    exact (hg z).symm
  exact (hcost.1 δ).congr (by filter_upwards [hEq] with g hg; exact hg.symm)

end SupercriticalLQGUniqueness.B2.PfeAxioms
