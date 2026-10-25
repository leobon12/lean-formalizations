import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedUpper

 








set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

def neighborhoodLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (V : Set ℂ) (x y : V) (ρ : ℝ) : ℝ≥0∞ :=
  ⨅ (u : V) (_ : dist (u : ℂ) x < ρ),
    ⨅ (v : V) (_ : dist (v : ℂ) y < ρ),
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDOn ξ φ V u v

theorem neighborhoodInternal_normalized_le_neighborhoodLFPP
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {V : Set ℂ} (x y : V) (ρ : ℝ) :
    neighborhoodInternal (PfeWeyl.normalizedLFPPMetric ξ a φ) V x y ρ ≤
      neighborhoodLFPP ξ a φ V x y ρ := by
  unfold neighborhoodInternal neighborhoodLFPP
  apply iInf_mono
  intro u
  apply iInf_mono
  intro hu
  apply iInf_mono
  intro v
  apply iInf_mono
  intro hv
  exact normalizedLFPPMetric_internal_le_lfppDOn ξ a φ u v

end SupercriticalLQGUniqueness.B2.PfeAxioms
