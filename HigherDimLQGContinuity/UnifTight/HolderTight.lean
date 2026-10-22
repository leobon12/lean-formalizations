import HigherDimLQGContinuity.UnifTight.Internal

/-!
# The interface `UHolderTightShape` from the quantile comparability (packet U4)

Blueprint Part D, `d:thm-A1`(c) (NA3 §2.9, §5.3; IA1 N-4). Port of
`HigherDimLQGMetric.DGZ.holderTightShape_of_comparable` / `holderTightShape_of_lambdaComparable`
(`DGZ/TightShapes.lean`, `DGZ/TightExports.lean`).

**Statement** (`uHolderTight_of_quantComp`): `UQuantCompShape d κ → UHolderTightShape d κ` for `d ≥ 2` and `κ`
admissible.

**Why the hypothesis** (reported to the orchestrator; the packet's I8 target needs the interface I7). The interface
`UHolderTightShape` (I8) is normalized by the median `λ^ξ_n = a^ξ_n(1/2)`, while the uniform Lemma 6.2
(`holderTightAQ_unif`, hypothesis-free) bounds `D^ξ_n` by `M a^ξ_n(q₁) ‖x - y‖^β` only for `q₁` close to `1`
(above the percolation threshold `c₄(d, κ)` of the event `𝒜_{r,n}`, U1's `prob_eventA_compl_le_unif`). Passing from
`a^ξ_n(q₁)` to `λ^ξ_n` needs `a^ξ_n(q₁) ≤ C λ^ξ_n` uniformly, i.e. the comparability (A.4) (Part D `d:prop-u64`(b),
interface I7 `UQuantCompShape`, packet U5), which rests on the nondegeneracy (A.3) and the zero-one law along
parameter arrays (`d:prop-u69`). Part D's proof of `d:thm-A1`(c) uses exactly this ("converted to `λ^ξ_n` … by
(f)"), and NA3's plan (§5.3) assigns "the λ_n form of U4" to U5. The fixed-ξ library made the same correction
(`DGZ.holderTightShape_of_comparable` takes `LambdaComparableShape`). Conversely, `UHolderTightShape` at `(0, e₁)`
implies `a^ξ_n(q) ≤ M λ^ξ_n` for `q < 1`, so no route to I8 avoids (A.4). `UQuantCompShape` is produced by U5 from
the hypothesis-free `a^ξ_n(q)`-normalized results of this packet (`tight_unif`, `holderTightAQ_unif`, `uDistInf`,
`nondeg_cross_unit_unif`), so the composition `uHolderTight_of_quantComp hd hκ (uQuantComp hd hκ)` has no cycle.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **U-Hölder tightness from the comparability (A.4)** (Part D `d:thm-A1`(c); port of
`DGZ.holderTightShape_of_comparable`): the interface `UHolderTightShape d κ` (I8) holds as soon as the quantiles are
uniformly comparable (`UQuantCompShape d κ`, I7). Uniform Lemma 6.2 normalized by `a^ξ_n(q₁)`
(`holderTightAQ_unif`) and `a^ξ_n(q₁) ≤ C λ^ξ_n` give the median normalization with the constant `M C`. -/
theorem uHolderTight_of_quantComp (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hQC : UQuantCompShape d κ) : UHolderTightShape d κ := by
  intro b μ hb hμ β hβ0 hβ U V hU hV hVc hVb hVU θ hθ
  have hhalf0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  obtain ⟨q₁, hq₁0, hq₁1, hAQ⟩ := holderTightAQ_unif hd hκ hb hμ hβ0 hβ
  obtain ⟨M, hM, hMb⟩ := hAQ q₁ le_rfl hq₁1 U V hU hV hVc hVb hVU θ hθ
  obtain ⟨C, hC, hCb⟩ := hQC b μ hb hμ q₁ 2⁻¹ hq₁0 hq₁1 hhalf0 hhalf1
  refine ⟨M * C, fun ξ hξU Ω _ P W H hH n =>
    le_trans (measure_mono ?_) (hMb ξ hξU Ω P W H hH n)⟩
  rintro ω ⟨x, hx, y, hy, hlt⟩
  refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hlt⟩
  have h1 : aQ P H ξ n q₁ ≤ C * aQ P H ξ n 2⁻¹ := hCb ξ hξU Ω P W H hH n
  have hs : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
  calc M * aQ P H ξ n q₁ * ‖x - y‖ ^ β ≤ M * (C * aQ P H ξ n 2⁻¹) * ‖x - y‖ ^ β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hM.le) hs
    _ = M * C * aQ P H ξ n 2⁻¹ * ‖x - y‖ ^ β := by ring

end HigherDimLQGContinuity
