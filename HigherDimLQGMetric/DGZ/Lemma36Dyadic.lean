import HigherDimLQGMetric.DGZ.Lemma36
import HigherDimLQGMetric.DGZ.Sec41Defs

/-!
# DGZ Lemma 3.6, lower half, in the dyadic-realization form (packet L3b3, MA7 D-3.6L)

The form of `lemma36_lower` in the language of MA7 Details (c) §D–§E (`DGZHyp`,
`IsDyadicRealization`, defined verbatim in `DGZ/Sec41Defs.lean`), as consumed by D-4.8
(`AcrossLowerShape`, packet L3c3): under the standing hypotheses of DGZ §§4–6, for every `δ > 0`
there is `C > 0` such that for every dyadic realization, all `x, y ∈ B̄₂(0)` with
`|x - y|_∞ ≥ 1/2` and all `n`, `P[D_n(x, y; B₃(0)) < 2^{-(1-ξQ+δ)n}] ≤ C e^{-n/C}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-- **DGZ Lemma 3.6, lower half** (MA7 D-3.6L) under `DGZHyp d κ ξ Q`, for dyadic realizations:
for every `δ > 0` there is `C > 0` with
`P[D_n(x, y; B₃(0)) < 2^{-(1-ξQ+δ)n}] ≤ C e^{-n/C}` for all `x, y ∈ B̄₂(0)` with
`|x - y|_∞ ≥ 1/2` and all `n`. -/
theorem lemma36_lower_of_dgzHyp {κ : Rd d → ℝ} {ξ Q : ℝ} (hD : DGZHyp d κ ξ Q) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ x y : Rd d, x ∈ cbox 0 2 → y ∈ cbox 0 2 → (∃ i, (1 : ℝ) / 2 ≤ |x i - y i|) →
        ∀ n : ℕ, P {ω | lfppDistOn ξ (fun z => H n z ω) (obox 0 3) x y <
          (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  obtain ⟨C, hC, h⟩ := lemma36_lower hD.dim hD.kernel hD.xi_pos
    (fun Ω _ P W H hW hH => hD.exponent Ω P W H ⟨hW, hH⟩) hδ
  exact ⟨C, hC, fun _ _ _ _ _ hR => h hR.whiteNoise hR.band⟩

end HigherDimLQGMetric.DGZ
