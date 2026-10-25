import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedNeighborhood

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_eventually_normalized_localized_heat_neighborhood_compare
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (ξ : Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (a : ℕ → Set.Ioi (0 : ℝ))
    (X : ℕ → Ω → C(ℂ, ℝ))
    (hX : ∀ᵐ ω ∂P, ∀ n z, X n ω z = heatMollify (ε n : ℝ) (h ω) z) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, 1 < c →
      ∀ᶠ n in atTop, ∀ (x y : V) (ρ : ℝ),
        neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ)
            (ε n).property (h ω))) V x y ρ ≤
          ENNReal.ofReal c *
            neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
              (X n ω)) V x y ρ ∧
        neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (X n ω)) V x y ρ ≤
          ENNReal.ofReal c *
            neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
              (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ)
                (ε n).property (h ω))) V x y ρ := by
  filter_upwards [ae_eventually_normalized_localized_heat_internal_compare
    hh ξ hV hVb ε hε a X hX] with ω hω
  intro c hc
  filter_upwards [hω c hc] with n hn
  intro x y ρ
  have hpos : 0 < c := lt_trans zero_lt_one hc
  exact ⟨neighborhoodInternal_le_const_mul _ _ x y ρ hpos
      (fun u v => (hn u v).1),
    neighborhoodInternal_le_const_mul _ _ x y ρ hpos
      (fun u v => (hn u v).2)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
