import SupercriticalLQGUniqueness.B2.DG20Lim.CircleLowerTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_pos_of_uniform_small_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ≥0∞) (y : Ω → ℝ≥0∞)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (y ω)))
    (htail : ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ᶠ n in atTop, P {ω | Y n ω < δ} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, 0 < y ω := by
  have hbound (η : ℝ) (hη : 0 < η) :
      P {ω | y ω = 0} ≤ ENNReal.ofReal η := by
    obtain ⟨δ, hδ, htailδ⟩ := htail η hη
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp htailδ
    let S : ℕ → Set Ω := fun N =>
      {ω | ∀ n : ℕ, N ≤ n → Y n ω < δ}
    have hSm : Monotone S := by
      intro N M hNM ω hω n hn
      exact hω n (hNM.trans hn)
    have hSN (N : ℕ) : P (S N) ≤ ENNReal.ofReal η := by
      have hsub : S N ⊆ {ω | Y (max N N₀) ω < δ} := by
        intro ω hω
        exact hω _ (le_max_left _ _)
      exact (measure_mono hsub).trans (hN₀ _ (le_max_right _ _))
    have hAS : {ω | y ω = 0} ≤ᵐ[P] ⋃ N, S N := by
      filter_upwards [hconv] with ω hω hzero
      have hlim : ∀ᶠ n in atTop, Y n ω < δ := by
        have hnhds : Set.Iio δ ∈ 𝓝 (y ω) := by
          rw [hzero]
          exact isOpen_Iio.mem_nhds hδ
        exact hω.eventually hnhds
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlim
      exact mem_iUnion.mpr ⟨N, fun n hn => hN n hn⟩
    calc
      P {ω | y ω = 0} ≤ P (⋃ N, S N) := measure_mono_ae hAS
      _ = ⨆ N, P (S N) := hSm.measure_iUnion
      _ ≤ ENNReal.ofReal η := iSup_le hSN
  have hzero : P {ω | y ω = 0} = 0 := by
    by_contra hne
    have hp : 0 < P {ω | y ω = 0} :=
      lt_of_le_of_ne bot_le (Ne.symm hne)
    have hfin : P {ω | y ω = 0} ≠ ∞ :=
      ne_top_of_le_ne_top (by simp : P Set.univ ≠ ∞)
        (measure_mono (subset_univ _))
    have hr : 0 < (P {ω | y ω = 0}).toReal :=
      ENNReal.toReal_pos hp.ne' hfin
    have hlt : ENNReal.ofReal ((P {ω | y ω = 0}).toReal / 2) <
        P {ω | y ω = 0} := by
      calc
        _ < ENNReal.ofReal (P {ω | y ω = 0}).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hr).2 (by linarith)
        _ = P {ω | y ω = 0} := ENNReal.ofReal_toReal hfin
    exact (not_lt_of_ge (hbound _ (half_pos hr))) hlt
  have hne : ∀ᵐ ω ∂P, y ω ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using hzero
  filter_upwards [hne] with ω hω
  exact pos_iff_ne_zero.mpr hω

end SupercriticalLQGUniqueness.B2.DG20Lim
