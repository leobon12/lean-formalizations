import HigherDimLQGMetric.DGZ.NondegCollarGeom

/-! A positive interior-distance collar is nonempty and compact. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid : ℝ}

def nd_interiorDist (i : nd_DomainIndex d rGrid) (x : Rd d) : ℝ :=
  Metric.infDist x (nd_domain rGrid i)ᶜ

theorem nd_continuous_interiorDist (i : nd_DomainIndex d rGrid) :
    Continuous (nd_interiorDist i) := by
  change @Continuous (Rd d) ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    _ (fun x => Metric.infDist x (nd_domain rGrid i)ᶜ)
  exact Metric.continuous_infDist_pt _

theorem nd_interiorDist_eq_zero_of_not_mem (i : nd_DomainIndex d rGrid)
    {x : Rd d} (hx : x ∉ nd_domain rGrid i) : nd_interiorDist i x = 0 :=
  Metric.infDist_zero_of_mem hx

theorem nd_interiorDist_frontier_zero (i : nd_DomainIndex d rGrid)
    {x : Rd d} (hx : x ∈ frontier (nd_domain rGrid i)) :
    nd_interiorDist i x = 0 := by
  have hdisj : Disjoint (frontier (nd_domain rGrid i)) (nd_domain rGrid i) :=
    disjoint_frontier_iff_isOpen.mpr (nd_isOpen_domain rGrid i)
  exact nd_interiorDist_eq_zero_of_not_mem i ((Set.disjoint_left.mp hdisj) hx)

theorem nd_levelCollar_nonempty_of_inside {i : nd_DomainIndex d rGrid}
    {g : Rd d → ℝ} (hg : Continuous g)
    (hgU : ∀ x, x ∉ nd_domain rGrid i → g x ≤ 0)
    {c ρ : ℝ} (hc : 0 < c) (hcρ : c ≤ ρ)
    (a : nd_domain rGrid i) (ha : ρ ≤ g a.1)
    (b : Rd d) (hb : g b ≤ 0) :
    (nd_levelCollar rGrid i g c).Nonempty := by
  let γ : ℝ → Rd d := fun t => (1 - t) • b + t • a.1
  have hγ : Continuous γ := by fun_prop
  have hγ0 : γ 0 = b := by simp [γ]
  have hγ1 : γ 1 = a.1 := by simp [γ]
  have hf : Continuous (fun t : ℝ => g (γ t)) := hg.comp hγ
  have hmid : c ∈ Set.Icc (g (γ 0)) (g (γ 1)) := by
    rw [hγ0, hγ1]
    constructor <;> linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hmid
  change g (γ t) = c at ht
  have htU : γ t ∈ nd_domain rGrid i := by
    by_contra hnot
    have := hgU (γ t) hnot
    rw [ht] at this
    linarith
  exact ⟨⟨γ t, htU⟩, ht⟩

end HigherDimLQGMetric.DGZ
