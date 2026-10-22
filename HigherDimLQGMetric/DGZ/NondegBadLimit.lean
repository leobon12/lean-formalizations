import HigherDimLQGMetric.DGZ.NondegOpenBound

/-! Persistent probability of crossings tending to zero excludes full positive-crossing mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_limit_positiveCross_le_of_bad
    {rGrid r : ℝ} (ν : ℕ → ProbabilityMeasure (nd_Joint d rGrid))
    (μ : ProbabilityMeasure (nd_Joint d rGrid))
    (hlim : Tendsto ν atTop (𝓝 μ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (θ : ℝ≥0∞) (hθ : θ ≤ 1)
    (hbad : ∀ n,
      θ ≤ (ν n : Measure (nd_Joint d rGrid))
        {s | nd_crossPhi 0 (2 * r) r s.1 ≤ δ n}) :
    (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) ≤ 1 - θ := by
  let g : nd_Joint d rGrid → ℝ := fun s => nd_crossPhi 0 (2 * r) r s.1
  have hg : Continuous g := (nd_continuous_crossPhi 0 (2 * r) r).comp continuous_fst
  have hθfin : θ ≠ ∞ := ne_top_of_le_ne_top (by simp) hθ
  apply nd_measure_pos_le_of_open_threshold_bounds (μ : Measure (nd_Joint d rGrid))
    g (1 - θ)
  intro ε hε
  let G : Set (nd_Joint d rGrid) := {s | ε < g s}
  have hG : IsOpen G := isOpen_lt continuous_const hg
  have hev := hδ.eventually (eventually_lt_nhds hε)
  have hpre : ∀ᶠ n : ℕ in atTop,
      (ν n : Measure (nd_Joint d rGrid)) G ≤ 1 - θ := by
    filter_upwards [hev] with n hn
    have hsub : {s : nd_Joint d rGrid | g s ≤ δ n} ⊆ Gᶜ := by
      intro s hs hGmem
      change ε < g s at hGmem
      exact (not_lt_of_ge hs) (hn.trans hGmem)
    have hbadcomp : θ ≤ (ν n : Measure (nd_Joint d rGrid)) Gᶜ :=
      (hbad n).trans (measure_mono hsub)
    have hsum : (ν n : Measure (nd_Joint d rGrid)) G + θ ≤ 1 := by
      calc
        (ν n : Measure (nd_Joint d rGrid)) G + θ ≤
            (ν n : Measure (nd_Joint d rGrid)) G +
              (ν n : Measure (nd_Joint d rGrid)) Gᶜ := add_le_add le_rfl hbadcomp
        _ = 1 := prob_add_prob_compl hG.measurableSet
    exact (ENNReal.le_sub_iff_add_le_right hθfin hθ).2 hsum
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG).trans
    (liminf_le_of_frequently_le' hpre.frequently)

end HigherDimLQGMetric.DGZ
