import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLiminfCompare

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem ae_lowerNeighborhoodObservable_localized_eq_heat
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (ξ : Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (a : ℕ → Set.Ioi (0 : ℝ))
    (X : ℕ → Ω → C(ℂ, ℝ))
    (hX : ∀ᵐ ω ∂P, ∀ n z, X n ω z = heatMollify (ε n : ℝ) (h ω) z) :
    ∀ᵐ ω ∂P, ∀ x y : V,
      lowerNeighborhoodObservable
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ)
            (ε n).property (h ω))) V x y =
      lowerNeighborhoodObservable
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n) (X n ω)) V x y := by
  filter_upwards [ae_eventually_normalized_localized_heat_neighborhood_compare
    hh ξ hV hVb ε hε a X hX] with ω hω
  intro x y
  apply iSup_congr
  intro k
  apply liminf_eq_of_eventually_mul_both
  intro c hc
  exact ⟨(hω c hc).mono fun n hn => (hn x y _).1,
    (hω c hc).mono fun n hn => (hn x y _).2⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
