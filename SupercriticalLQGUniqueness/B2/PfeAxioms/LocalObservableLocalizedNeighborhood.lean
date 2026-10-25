import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedEvent

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem neighborhoodInternal_le_const_mul
    (E F : LSCMetric) {V : Set ℂ} (x y : V) (ρ : ℝ)
    {c : ℝ} (hc : 0 < c)
    (hEF : ∀ u v : V, E.internal V (u, v) ≤
      ENNReal.ofReal c * F.internal V (u, v)) :
    neighborhoodInternal E V x y ρ ≤
      ENNReal.ofReal c * neighborhoodInternal F V x y ρ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  unfold neighborhoodInternal
  simp only [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  apply iInf_mono
  intro u
  apply iInf_mono
  intro hu
  apply iInf_mono
  intro v
  apply iInf_mono
  intro hv
  exact hEF u v

theorem normalized_localized_heat_neighborhood_compare
    (ξ : Set.Ioi (0 : ℝ)) (a ε : Set.Ioi (0 : ℝ))
    (g : LQGMetric.DistC) (φ : C(ℂ, ℝ))
    {V : Set ℂ} (hV : IsOpen V) (x y : V) (ρ : ℝ)
    {c : ℝ} (hc : 0 < c)
    (hcomp : ∀ z w : ℂ,
      localizedLFPP ξ ε g V z w ≤
        ENNReal.ofReal c * LQGMetric.LFPP.lfppDOn (ξ : ℝ) φ V z w ∧
      LQGMetric.LFPP.lfppDOn (ξ : ℝ) φ V z w ≤
        ENNReal.ofReal c * localizedLFPP ξ ε g V z w) :
    neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)) V x y ρ ≤
      ENNReal.ofReal c *
        neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a φ) V x y ρ ∧
    neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a φ) V x y ρ ≤
      ENNReal.ofReal c *
        neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)) V x y ρ := by
  have h := fun (u v : V) =>
    normalized_localized_heat_internal_compare ξ a ε g φ hV hc.le hcomp u v
  exact ⟨neighborhoodInternal_le_const_mul _ _ x y ρ hc (fun u v => (h u v).1),
    neighborhoodInternal_le_const_mul _ _ x y ρ hc (fun u v => (h u v).2)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
