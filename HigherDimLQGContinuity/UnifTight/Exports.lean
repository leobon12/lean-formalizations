import HigherDimLQGContinuity.UnifTight.DistInf
import HigherDimLQGContinuity.UnifTight.HolderTight

/-!
# High-quantile exports of packet U4 for the zero-one-law packet U5

Packet U5 (sequence zero-one law, `uQuantComp` = I7, `uNondeg` = I9) runs with the normalization `a^ξ_n(q)` at one
quantile `q` close to `1`, so that it does not need the median-normalized interfaces I8/I10 (I8 needs I7: see
`UnifTight/HolderTight.lean`). Its working inputs are the high-quantile forms of Part D `d:lem-u61`(b) and
`d:lem-u65`(c) with `G = 0`. This file states them in a form that does not depend on any definition of packet U5:

* `holderTightAQShape_unif`: for `0 < β < μ` there is `q₁ ∈ (0, 1)` such that for `q ∈ [q₁, 1)`, `U` open, `V`
  bounded open connected with `V̄ ⊆ U` and `θ > 0` there is `M` with
  `P[∃ x, y ∈ V : M a^ξ_n(q) ‖x - y‖^β < D^ξ_n(x, y; U)] ≤ θ` for all `ξ ∈ S(b, μ)`, realizations and `n`
  (from `holderTightAQ_unif`, dropping `0 < M`);
* `distInfAQShape_unif`: there is `q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)`, `r, θ > 0` and `T` there are `R > r` and
  `N` (`N = 0`) with `P[D^ξ_n(across B_R(0) \ B_r(0)) ≤ T a^ξ_n(q)] ≤ θ` for all `ξ ∈ S(b, μ)`, realizations and
  `n ≥ N` (from `distInf_aq_unif`).

Their statements are, binder for binder, the bodies of U5's draft definitions `UHolderTightAQShape d κ` (with
`UHolderTightAt` unfolded) and `UDistInfAQShape d κ` (with `UDistInfAt` unfolded) as of 2026-10-22 07:30, so
`holderTightAQShape_unif hd hκ : UHolderTightAQShape d κ` and `distInfAQShape_unif hd hκ : UDistInfAQShape d κ` close
by definitional unfolding.
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

/-- **High-quantile uniform Hölder tightness** (Part D `d:lem-u61`(b), `m = 0`; the input of the zero-one-law
packet): `holderTightAQ_unif` in the shape of U5's `UHolderTightAQShape d κ`. -/
theorem holderTightAQShape_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ β : ℝ, 0 < β → β < μ →
      ∃ q₁ : ℝ≥0∞, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q : ℝ≥0∞, q₁ ≤ q → q < 1 →
        ∀ U V : Set (Rd d), IsOpen U → IsOpen V → IsConnected V → Bornology.IsBounded V →
          closure V ⊆ U → ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
            ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
              (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
                P {ω | ∃ x ∈ V, ∃ y ∈ V, M * DGZ.aQ P H ξ n q * ‖x - y‖ ^ β <
                  HigherDimLFPP.lfppDistOn ξ (fun w => H n w ω) U x y} ≤ ENNReal.ofReal θ := by
  intro b μ hb hμ β hβ0 hβ
  obtain ⟨q₁, hq₁0, hq₁1, hAQ⟩ := holderTightAQ_unif hd hκ hb hμ hβ0 hβ
  refine ⟨q₁, hq₁0, hq₁1, fun q hq₁q hq1 U V hU hV hVc hVb hVU θ hθ => ?_⟩
  obtain ⟨M, -, hMb⟩ := hAQ q hq₁q hq1 U V hU hV hVc hVb hVU θ hθ
  exact ⟨M, hMb⟩

/-- **High-quantile uniform distance to infinity** (Part D `d:lem-u65`(c), `G = 0`; the input of the zero-one-law
packet): `distInf_aq_unif` in the shape of U5's `UDistInfAQShape d κ` (with `N = 0`). -/
theorem distInfAQShape_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∀ b μ : ℝ, 0 < b → 0 < μ →
      ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
        ∀ r T θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧ ∃ N : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
            (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
              P {ω | DGZ.acrossDist ξ (fun w => H n w ω) 0 R r ≤ T * DGZ.aQ P H ξ n q} ≤
                ENNReal.ofReal θ := by
  intro b μ hb hμ
  obtain ⟨q₂, hq₂0, hq₂1, hdist⟩ := distInf_aq_unif hd hκ hb hμ
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 r T θ hr hθ => ?_⟩
  obtain ⟨R, hrR, hR⟩ := hdist q hq₂q hq1 r T θ hr hθ
  exact ⟨R, hrR, 0, fun ξ hξU Ω _ P W H hH n _ => hR ξ hξU Ω P W H hH n⟩

end HigherDimLQGContinuity
