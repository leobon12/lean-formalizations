import HigherDimLFPP.TwoD.CircleCorollary
import HigherDimLFPP.Exist.Exponent

/-!
# Provider of the frozen `gff_circle_average_lfpp`

The d = 2 corollary for circle-average LFPP of the whole-plane GFF normalized by `h₁(0) = 0` (ruling
H12): the LFPP exponent exists for all small `ξ > 0` and `λ(ξ)/ξ^{4/3} → κ₂`. It combines

* `gff_circle_average_lfpp_of_exponentExists` (`TwoD/CircleCorollary.lean`, worker P-X10): circle
  averages of the κ-kernel all-scale field, Lemma A.1, exponent and law transfer, and
  `LQGDimension.theorem11_lambda`, conditional on the existence of the d = 2 white-noise exponent;
* `exponent_exists` (`Exist/Exponent.lean`, worker P-X8): that existence, for every `d ≥ 2`
  (Ding–Gwynne–Zhuang Prop. 1.1 and App. A.1).

It is the `implementation.module` of the anchor `HigherDimLFPP/Frozen/GFFCircleAverage.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- Implementation of the frozen `gff_circle_average_lfpp`. -/
theorem gff_circle_average_lfpp_impl :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage h P →
      (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, ∃ lam : ℝ, LQGDimension.IsLFPPExponent h P ξ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, LQGDimension.IsLFPPExponent h P ξ (lam ξ)) →
        Tendsto (fun ξ => lam ξ / ξ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa 2)) :=
  gff_circle_average_lfpp_of_exponentExists fun κ hκ ζ hζ => by
    obtain ⟨lam, hlam⟩ := exponent_exists.{0} 2 le_rfl κ hκ ζ hζ
    exact ⟨lam, fun Ω _ P W H hW hH => hlam Ω P W hW H hH⟩

end HigherDimLFPP
