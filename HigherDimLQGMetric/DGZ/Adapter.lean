import HigherDimLQGMetric.DGZ.AdapterConfinement

/-! The real-cutoff adapter consumed by the weak-metric construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

/-- Real cutoffs, Euclidean balls and spheres, whole-space medians, confinement, and the
whole-space median exponent, as required by [1] Lemma 3.3 and Theorem 1.6. -/
theorem realEpsAdapter (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ)
    (hHolder : HolderTightShape d κ ξ Q)
    (hNondeg : NondegShape d κ ξ Q)
    (_hDistInf : DistInfShape d κ ξ Q) :
    RealEpsAdapterShape d κ ξ Q := by
  intro h β hβ0 hβ Ω _ P W G hW hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R θ hR hθ
    exact adapter_holder_real h hHolder hNondeg hβ0 hβ hW hG R θ hR hθ
  · intro c r₁ r₂ θ hr₂ hr hθ
    exact adapter_nondeg_real h hHolder hNondeg hβ0 hβ hW hG c r₁ r₂ θ hr₂ hr hθ
  · intro r θ hr hθ
    exact adapter_confinement_real h hHolder hNondeg hβ0 hβ hW hG r θ hr hθ
  · exact adapter_aHat_exponent h hHolder hNondeg hW hG

end HigherDimLQGMetric.DGZ
