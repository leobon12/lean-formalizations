import GaussianLQG.LQG.Geodesics
import GaussianLQG.LQG.Scaling.Measurability

/-!
# Measurability of the metric functional `sup_{K×K} D`

For a continuous metric `d` the diameter-type supremum `sup_{z,w ∈ K} d(z, w)` may be taken over a
countable dense set (`LQGMetric.measurable_biSup_of_continuous`), so it is measurable on
`ContMetric` (blueprint §1.6, after (S6)): `measurable_iSup_dist_contMetric`, and the random
variable `Setup.measurable_iSup_dist`. The measurability of the Hölder constant `A(K)` and of the
separated infimum `I(K, δ)` (blueprint (1.10)) is `Setup.measurable_holderConst` and
`Setup.measurable_sepInf` (`GaussianLQG/LQG/Scaling/Measurability.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

/-- `d ↦ sup_{z,w ∈ K} d(z, w)` is measurable. -/
theorem measurable_iSup_dist_contMetric (K : Set ℂ) :
    Measurable fun d : ContMetric => ⨆ z ∈ K, ⨆ w ∈ K, ENNReal.ofReal (d.1 (z, w)) := by
  have e : (fun d : ContMetric => ⨆ z ∈ K, ⨆ w ∈ K, ENNReal.ofReal (d.1 (z, w))) =
      fun d => ⨆ p ∈ K ×ˢ K, ENNReal.ofReal (d.1 p) := by
    funext d
    rw [biSup_prod]
  rw [e]
  exact measurable_biSup_of_continuous (fun d => ENNReal.continuous_ofReal.comp d.1.continuous)
    (fun p => (ENNReal.continuous_ofReal.comp (continuous_contMetric_apply.comp
      (continuous_id.prodMk continuous_const))).measurable) _

namespace Setup

variable (S : Setup)

/-- `sup_{z,w ∈ K} D^γ(z, w)` is a random variable. -/
theorem measurable_iSup_dist (γ : ℝ) (K : Set ℂ) :
    Measurable fun ω => ⨆ z ∈ K, ⨆ w ∈ K, ENNReal.ofReal ((S.D γ ω).1 (z, w)) :=
  (measurable_iSup_dist_contMetric K).comp (S.measurable_D γ)

end Setup

/-! ## Compatibility names (cleanup W15)

The measurability of `A(K)` and `I(K, δ)` is proved on `C(ℂ × ℂ, ℝ)` in
`GaussianLQG/LQG/Scaling/Measurability.lean`; the old `ContMetric` forms are kept. -/

theorem measurable_holderConst_contMetric (K : Set ℂ) :
    Measurable fun d : ContMetric => holderConst d.1 K :=
  (measurable_holderConst_cont K).comp measurable_subtype_coe

theorem sepInf_eq_biInf_sepPairs (d : ContMetric) (K : Set ℂ) (δ : ℝ) :
    sepInf d.1 K δ =
      ⨅ p ∈ {p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ ‖p.1 - p.2‖}, ENNReal.ofReal (d.1 p) :=
  sepInf_eq_biInf_pairs _ K δ

theorem measurable_sepInf_contMetric (K : Set ℂ) (δ : ℝ) :
    Measurable fun d : ContMetric => sepInf d.1 K δ :=
  (measurable_sepInf_cont K δ).comp measurable_subtype_coe

end GaussianLQG
