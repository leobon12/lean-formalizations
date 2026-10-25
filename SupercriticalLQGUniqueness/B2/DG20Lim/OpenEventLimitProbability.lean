import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteGoodCoordLaw
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusLimitProbability

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem open_event_limit_probability_le
    {Ω T : Type*} [MeasurableSpace Ω] [TopologicalSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T) (Ylim : Ω → T) (E : Set T)
    (hE : IsOpen E)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (bound : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, P {ω | Y n ω ∈ E} ≤ bound) :
    P {ω | Ylim ω ∈ E} ≤ bound := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hbound
  let F : ℕ → Set Ω := fun N =>
    {ω | ∀ n : ℕ, N ≤ n → Y n ω ∈ E}
  have hFm : Monotone F := by
    intro N M hNM ω hω n hn
    exact hω n (hNM.trans hn)
  have hFN (N : ℕ) : P (F N) ≤ bound := by
    have hsub : F N ⊆ {ω | Y (max N N₀) ω ∈ E} := by
      intro ω hω
      exact hω _ (le_max_left _ _)
    exact (measure_mono hsub).trans (hN₀ _ (le_max_right _ _))
  have hAF : {ω | Ylim ω ∈ E} ≤ᵐ[P] ⋃ N, F N := by
    filter_upwards [hconv] with ω hω hlim
    have hevent : ∀ᶠ n in atTop, Y n ω ∈ E :=
      hω.eventually (hE.mem_nhds hlim)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
    exact mem_iUnion.mpr ⟨N, fun n hn => hN n hn⟩
  calc
    P {ω | Ylim ω ∈ E} ≤ P (⋃ N, F N) := measure_mono_ae hAF
    _ = ⨆ N, P (F N) := hFm.measure_iUnion
    _ ≤ bound := iSup_le hFN

end SupercriticalLQGUniqueness.B2.DG20Lim
