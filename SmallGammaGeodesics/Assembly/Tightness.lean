import SmallGammaGeodesics.Assembly.Reduction
import SmallGammaGeodesics.CC.MasterLE
import SmallGammaGeodesics.Upper.Lemma42Holds
import SmallGammaGeodesics.Tight.Main

/-!
# Provider: `SmallGammaGeodesics.Assembly/Tightness`

`implementation.module` of the frozen anchor `functional_tightness` (Theorem 1.2, (1.10)–(1.11); manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`). `functional_tightness_impl` has exactly the frozen
statement.

Proof: the reduction to the coordinate space (`functional_tightness_of_internal`) and the §6 assembly
(`tightConcl_of_interfaces`), with the interface inputs discharged by `CC.masterCCLE_holds` (track CC) and
`lemma42_holds`. This module must never import the frozen anchors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics
open LQGMetric

/-- **Theorem 1.2** (functional tightness): the frozen statement of `functional_tightness`, proved. -/
theorem functional_tightness_impl :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    (∀ γ, 0 < γ → γ < 2 →
      AEMeasurable (fun ω => rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω)) P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K : Set C(unitInterval, ℂ), IsCompact K ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      P {ω | rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω) ∉ K} ≤ ENNReal.ofReal ε) ∧
    TendstoInMeasure P (fun γ ω => horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) (𝓝[>] 0) (fun _ => 0) :=
  functional_tightness_of_internal (fun G η₀ hm hη =>
    tightConcl_of_interfaces G (fun γ h0 h2 => CC.masterCCLE_holds γ h0 h2 _ (G.hD γ h0 h2))
      lemma42_holds η₀ hm hη)

end SmallGammaGeodesics
