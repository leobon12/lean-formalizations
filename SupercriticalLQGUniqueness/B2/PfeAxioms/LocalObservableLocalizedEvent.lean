import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedCompare

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_eventually_normalized_localized_heat_internal_compare
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (ξ : Set.Ioi (0 : ℝ))
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (a : ℕ → Set.Ioi (0 : ℝ))
    (X : ℕ → Ω → C(ℂ, ℝ))
    (hX : ∀ᵐ ω ∂P, ∀ n z, X n ω z = heatMollify (ε n : ℝ) (h ω) z) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, 1 < c →
      ∀ᶠ n in atTop, ∀ x y : U,
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ)
            (ε n).property (h ω))).internal U (x, y) ≤
          ENNReal.ofReal c *
            (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
              (X n ω)).internal U (x, y) ∧
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (X n ω)).internal U (x, y) ≤
          ENNReal.ofReal c *
            (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
              (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ)
                (ε n).property (h ω))).internal U (x, y) := by
  have hεgt : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε, Eventually.of_forall fun n => (ε n).property⟩
  filter_upwards [localizedLFPP_compare hh hUb ξ, hX] with ω hω hXω
  intro c hc
  have hev := hεgt.eventually (hω.2 c hc)
  filter_upwards [hev] with n hn
  intro x y
  have heq : (X n ω : ℂ → ℝ) = heatMollify (ε n : ℝ) (h ω) :=
    funext (hXω n)
  apply normalized_localized_heat_internal_compare ξ (a n) (ε n) (h ω)
    (X n ω) hU (le_trans zero_lt_one.le hc.le)
  intro z w
  simpa only [heq, localizedLFPP] using (hn (ε n).property z w)

end SupercriticalLQGUniqueness.B2.PfeAxioms
