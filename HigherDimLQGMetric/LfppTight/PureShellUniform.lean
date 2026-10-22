import HigherDimLQGMetric.LfppTight.PureShellFar

/-! All-cutoff compact shell lower tail for normalized LGF LFPP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_pure_shell_tail (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (c : Rd d) {r₁ r₂ θ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) (hθ : 0 < θ) :
    ∃ m : ℝ, 0 < m ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m} ≤
          ENNReal.ofReal θ := by
  obtain ⟨m₁, εs, hm₁, hεs, hs⟩ := l6a_pure_shell_tail_small hL1e
    hDGZ hAdapter P h hh c hr₂ hr hθ
  obtain ⟨m₂, hm₂, hf⟩ := l6a_pure_shell_tail_far hDGZ.dim κ
    hDGZ.kernel ξ P h hh c hr₂ hr hεs hθ
  let m := min m₁ m₂
  refine ⟨m, lt_min hm₁ hm₂, ?_⟩
  intro ε hε
  by_cases he : ε < εs
  · have hsub : {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m} ⊆
      {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m₁} := by
      intro ω hω
      change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m at hω
      change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m₁
      exact hω.trans (min_le_left _ _)
    exact (measure_mono hsub).trans (hs ε ⟨hε.1, he⟩)
  · have hsub : {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m} ⊆
      {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m₂} := by
      intro ω hω
      change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m at hω
      change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m₂
      exact hω.trans (min_le_right _ _)
    exact (measure_mono hsub).trans (hf ε ⟨le_of_not_gt he, hε.2⟩)

end HigherDimLQGMetric
