import HigherDimLQGMetric.DGZ.NondegBadSample

/-! Small-shell lower tails for one fixed dyadic realization, from compactness and zero-one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_smallShell_nondeg_fixed_of_limit_inputs
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ)
    (hjoint : ∀ ns : ℕ → ℕ,
      ∃ μ : ProbabilityMeasure (nd_Joint d rGrid), ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧ Tendsto
          (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns (ψ k)))
          atTop (𝓝 μ))
    (hzero : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ μ : ProbabilityMeasure (nd_Joint d rGrid),
        Tendsto
          (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
          atTop (𝓝 μ) →
        (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 0 ∨
          (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 1)
    (c : ℝ) (hc : 0 < c)
    (hcross : ∀ n : ℕ, ENNReal.ofReal c ≤
      P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 * r) r})
    (θ : ℝ≥0∞) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
        δ * aQ P H ξ n q} ≤ θ := by
  by_contra hno
  push Not at hno
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hbadall : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      θ < P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
        δ k * aQ P H ξ n q} := by
    intro k
    exact hno (δ k) (hδpos k) k
  choose ns hns_ge hbad using hbadall
  have hns : Tendsto ns atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (hns_ge k)
  obtain ⟨μ, ψ, hψ, hlim⟩ := hjoint ns
  have hnsψ : Tendsto (ns ∘ ψ) atTop atTop :=
    hns.comp hψ.tendsto_atTop
  have hδlim : Tendsto (δ ∘ ψ) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψ.tendsto_atTop
  have hbadlim : (μ : Measure (nd_Joint d rGrid))
      (nd_positiveCrossEvent rGrid r) ≤ 1 - θ := by
    apply nd_limit_positiveCross_le_of_bad
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid
        (ns (ψ k))) μ hlim (δ ∘ ψ) hδlim θ hθ1
    intro k
    exact nd_jointLaw_badCross_prob h hH hq0 hq1 rGrid r (δ (ψ k))
      (ns (ψ k)) (hbad (ψ k)).le
  have hpos : ENNReal.ofReal c ≤
      (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) :=
    nd_limit_positiveCross_prob h hH hq0 hq1 rGrid r c hc hcross
      (ns ∘ ψ) hlim
  rcases hzero (ns ∘ ψ) hnsψ μ hlim with hz | hz
  · have hcpos : (0 : ℝ≥0∞) < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
    rw [hz] at hpos
    exact (not_le_of_gt hcpos) hpos
  · rw [hz] at hbadlim
    exact (not_le_of_gt (ENNReal.sub_lt_self (by simp) (by simp) hθ0.ne')) hbadlim

end HigherDimLQGMetric.DGZ
