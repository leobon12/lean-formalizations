import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Annulus.MarginalRealize

/-!
# Equality in law of the rescaled pair (packet RZP)

Source: `planning/audits/MA1-sections-1-3.md` Details A10.3 (realization) and A3 (law transfer); the docstring of
`HigherDimLFPPAS.Core.PairLaw`.

For `0 < ε ≤ r ≤ 1` and a centre `z`, the recentred field `h^{z,r} = recentAff r z h` is a normalized LGF
(`HigherDimLQGMetric.isNormalizedLGF_recentAff`), so it has the law `normLGFLaw d` of `h`
(`HigherDimLQGMetric.l9b_map_eq_normLGFLaw`). The pair `g ↦ (D g, 𝔐_{ε,ε/r}(g))` is a measurable map of the field:
`D` is measurable (`IsStrongExpMetric.measurable`), and `𝔐_{ε,ε/r}` is measurable by packet L32p's
`HigherDimLFPPAS.Annulus.l32p_measurable_MepsR` when `ε < 1`. At the endpoint `ε = r = 1` the truncation radius is
`locRad 1 / 1 = 0`, the test function of `locFieldR` is the junk `0`, and `𝔐_{1,1}(g)` does not depend on `g`
(`rzp_MepsR_one_one`), so it is measurable as a constant. Composition (`Measure.map_map`) transfers the law.

Mathlib convention (L32p's handoff): `Measure.map` of a non-a.e.-measurable map is a Dirac mass, not `0`; here both maps
are genuinely measurable (the field `h` is measurable as part of `IsNormalizedLGF`), so no junk is involved.

* `rzp_locRad_one`, `rzp_locFieldR_one_one`, `rzp_MepsR_one_one`: the endpoint `ε = r = 1`.
* `rzp_measurable_MepsR`: `g ↦ 𝔐_{ε,ε/r}(g)` is measurable for `0 < ε ≤ r ≤ 1` (smooth kernel, positive `𝔞_{ε/r}`).
* `rzp_map_eq_of_normalized`: any measurable functional of the field has the same law under two normalized LGFs.
* `pairLaw_holds`: the interface `Core.PairLaw` from the standing hypotheses `Core.Setting`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPPAS.Rescale

open HigherDimLFPPAS.Core HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The endpoint `ε = r = 1` -/

/-- `locRad 1 = 0` (the logarithmic factor `(log 1⁻¹)^10` vanishes). -/
theorem rzp_locRad_one : locRad 1 = 0 := by
  unfold locRad
  rw [inv_one, Real.log_one, zero_pow (by norm_num), mul_zero]

/-- At `ε = r = 1` the localized field vanishes identically: the truncation radius `locRad 1 / 1` is `0`, so the test
function is the junk `0` of `locTest`. -/
theorem rzp_locFieldR_one_one (κ : Rd d → ℝ) (g : DistRd d) (x : Rd d) : locFieldR κ 1 1 g x = 0 := by
  have hns : ¬(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ 0 < locRad 1 / 1) := by
    rintro ⟨-, hs⟩
    rw [rzp_locRad_one, zero_div] at hs
    exact lt_irrefl 0 hs
  have htest : locTest κ (1 / 1) (locRad 1 / 1) x = 0 := by
    unfold locTest
    rw [dite_eq_right hns]
  unfold locFieldR
  rw [htest, map_zero, mul_zero]

/-- At `ε = r = 1` the rescaled localized metric `𝔐_{1,1}(g)` does not depend on the field `g`. -/
theorem rzp_MepsR_one_one (κ : Rd d → ℝ) (ξ : ℝ) (g : DistRd d) :
    MepsR κ ξ 1 1 g = MepsR κ ξ 1 1 0 := by
  have hfield : locFieldR κ 1 1 g = locFieldR κ 1 1 0 :=
    funext fun x => by rw [rzp_locFieldR_one_one, rzp_locFieldR_one_one]
  unfold MepsR locFieldRC
  rw [hfield]

/-! ### Measurability of the rescaled pair -/

/-- **`g ↦ 𝔐_{ε,ε/r}(g)` is measurable** on the parameter range of `PairLaw` (`0 < ε ≤ r ≤ 1`), for a smooth kernel and
positive `𝔞_{ε/r}`: packet L32p's `l32p_measurable_MepsR` for `ε < 1`, a constant map at `ε = r = 1`. -/
theorem rzp_measurable_MepsR {κ : Rd d → ℝ} {ξ ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hε : 0 < ε) (hεr : ε ≤ r) (hr1 : r ≤ 1)
    (ha : 0 < aEps κ ξ (ε / r)) :
    Measurable (fun g : DistRd d => MepsR κ ξ ε r g) := by
  rcases lt_or_eq_of_le (hεr.trans hr1) with hε1 | hε1
  · exact Annulus.l32p_measurable_MepsR hK
      (div_pos (Annulus.l32p_locRad_pos hε hε1) (lt_of_lt_of_le hε hεr)) ha
  · have hr : r = 1 := le_antisymm hr1 (hε1 ▸ hεr)
    subst hε1 hr
    have hconst : (fun g : DistRd d => MepsR κ ξ 1 1 g) = fun _ => MepsR κ ξ 1 1 0 :=
      funext fun g => rzp_MepsR_one_one κ ξ g
    rw [hconst]
    exact measurable_const

/-- **Law transfer** (MA1 A3, A10.3): a measurable functional of the field has the same law under any two normalized
LGFs on the same probability space (both have the law `normLGFLaw d`). -/
theorem rzp_map_eq_of_normalized {β : Type*} [MeasurableSpace β] {F : DistRd d → β} (hF : Measurable F)
    (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g h : Ω → DistRd d} (hg : IsNormalizedLGF g P) (hh : IsNormalizedLGF h P) :
    Measure.map (fun ω => F (g ω)) P = Measure.map (fun ω => F (h ω)) P := by
  have eg : Measure.map (fun ω => F (g ω)) P = Measure.map F (Measure.map g P) :=
    (Measure.map_map hF hg.1.measurable).symm
  have eh : Measure.map (fun ω => F (h ω)) P = Measure.map F (Measure.map h P) :=
    (Measure.map_map hF hh.1.measurable).symm
  rw [eg, eh, l9b_map_eq_normLGFLaw hd hg, l9b_map_eq_normLGFLaw hd hh]

/-! ### The interface `PairLaw` -/

/-- **Equality in law of the rescaled pair** (MA1 A10.3, interface `Core.PairLaw`): under the standing hypotheses, for
`0 < ε ≤ r ≤ 1` and every centre `z`, the pair `(D_h, 𝔐_{ε,ε/r}(h))` is (a.e.-)measurable and
`(D_{h^{z,r}}, 𝔐_{ε,ε/r}(h^{z,r}))`, `h^{z,r} = recentAff r z h`, has the same law. -/
theorem pairLaw_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.PairLaw κ ξ D P h := by
  intro ε r hε hεr hr1 z
  have hd2 : 2 ≤ d := le_trans (by norm_num) hS.dim
  have hr : 0 < r := lt_of_lt_of_le hε hεr
  have hF : Measurable (fun g : DistRd d => (D g, MepsR κ ξ ε r g)) :=
    hS.strong.measurable.prodMk (rzp_measurable_MepsR hS.seed.kernelSmooth hε hεr hr1
      (hS.seed.aEps_pos ξ (ε / r) (div_pos hε hr)))
  have hgN : IsNormalizedLGF (fun ω => recentAff r z (h ω)) P :=
    isNormalizedLGF_recentAff hd2 hS.field.1 hr z
  exact ⟨(hF.comp hS.field.1.measurable).aemeasurable,
    rzp_map_eq_of_normalized hF hd2 hgN hS.field⟩

end HigherDimLFPPAS.Rescale
