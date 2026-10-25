import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusCoordLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem bad_ratio_limit_probability_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (a b : ℕ → Ω → ℝ≥0∞) (aLim bLim : Ω → ℝ≥0∞)
    (C bound : ℝ≥0∞) (hC : C ≠ ∞)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => (a n ω, b n ω)) atTop (𝓝 (aLim ω, bLim ω)))
    (hbound : ∀ᶠ n in atTop,
      P {ω | C * a n ω < b n ω} ≤ bound) :
    P {ω | C * aLim ω < bLim ω} ≤ bound := by
  let bad : Set (ℝ≥0∞ × ℝ≥0∞) := {p | C * p.1 < p.2}
  have hbad : IsOpen bad :=
    isOpen_lt ((ENNReal.continuous_const_mul hC).comp continuous_fst)
      continuous_snd
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hbound
  let S : ℕ → Set Ω := fun N =>
    {ω | ∀ n : ℕ, N ≤ n → C * a n ω < b n ω}
  have hSm : Monotone S := by
    intro N M hNM ω hω n hn
    exact hω n (hNM.trans hn)
  have hSN (N : ℕ) : P (S N) ≤ bound := by
    have hsub : S N ⊆ {ω | C * a (max N N₀) ω < b (max N N₀) ω} := by
      intro ω hω
      exact hω _ (le_max_left _ _)
    exact (measure_mono hsub).trans (hN₀ _ (le_max_right _ _))
  have hAS : {ω | C * aLim ω < bLim ω} ≤ᵐ[P] ⋃ N, S N := by
    filter_upwards [hconv] with ω hω hlim
    have hevent : ∀ᶠ n in atTop, C * a n ω < b n ω := by
      have hnhds : bad ∈ 𝓝 (aLim ω, bLim ω) := hbad.mem_nhds hlim
      exact hω.eventually hnhds
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
    exact mem_iUnion.mpr ⟨N, fun n hn => hN n hn⟩
  calc
    P {ω | C * aLim ω < bLim ω} ≤ P (⋃ N, S N) := measure_mono_ae hAS
    _ = ⨆ N, P (S N) := hSm.measure_iUnion
    _ ≤ bound := iSup_le hSN

end SupercriticalLQGUniqueness.B2.DG20Lim
