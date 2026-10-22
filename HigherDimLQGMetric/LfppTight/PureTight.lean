import HigherDimLQGMetric.LfppTight.SmallTight
import HigherDimLQGMetric.LfppTight.FarTight

/-! The first two clauses of the pure normalized LGF tight-family statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_pure_normalized_tight (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    IsTightMeasureSet {μ : Measure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map (fun ω =>
          toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))} := by
  obtain ⟨ε₀, hε₀, hε₀1, hSmall⟩ :=
    l6a_small_normalized_tight hL1e hDGZ hAdapter P h hh
  have hFar := l6a_far_normalized_tight hDGZ.dim κ hDGZ.kernel ξ
    hDGZ.xi_pos P h hh hε₀
  apply (hSmall.union hFar).subset
  rintro μ ⟨ε, hε, rfl⟩
  by_cases he : ε < ε₀
  · exact Or.inl ⟨ε, ⟨hε.1, he⟩, rfl⟩
  · exact Or.inr ⟨ε, ⟨le_of_not_gt he, hε.2⟩, rfl⟩

end HigherDimLQGMetric
