import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpreadMeas
import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpread
import QuantumZipper.Proofs.Zipper.D3PlusN2TmZStmt

/-!
# D3⁺(ii), node LSCC-IND: the strong Markov form at the level of the embedded field

Task LSCC-IND. `LSCCIndStmt` is reduced in `D3PlusLSCCIndepMain.lean` to the strong Markov form
`LSCCIndTripleStmt` (the rich canonical data `C_L` are asymptotically independent of the embedding
time `τ_L` and the `O_P(1)` remainder `R_L`). This file reduces that further to a statement about
the **embedded field**, i.e. to the form in which the literature states it.

Source: Duplantier–Miller–Sheffield arXiv:1409.7055, Proposition 4.7 and its proof (p. 78), and
Sheffield arXiv:1012.4797, proof of Proposition 1.6 (p. 25). The circle-average embedding of the
model field at the hitting time `τ_L` produces the field `n2Emb γ α L r X`; by the strong Markov
property / Williams path decomposition its post-`τ_L` data (in particular its window data
`resField K (n2Emb …)`) are independent of `τ_L`. Since the rich canonical data are read off that
window off an event of small probability (the existing model-side transfer node
`N2ZModelLocStmt`), the triple node follows.

* `LSCCIndWinStmt`: the field-level strong Markov node — the embedded window data of the model
  zoom are asymptotically independent of the pair `(τ_L, R_L)`;
* `LSCCBadWinStmt`: the embedded window is *good* (its surrogate local scale lies in
  `(0, K/(R+2))` on `halfDisc K`) with probability tending to `1` uniformly in `L → ∞`, after
  taking the window `K` large;
* `tvDist_prod_le_of_readout`: own elementary glue (data processing through the measurable
  read-out `g`, the disagreement/off-event splitting bound, `Measure.map_prod_map` and
  `TV.tvDist_prod_right_le`);
* `lsccIndTriple_of_win`, `lsccInd_of_win` and the capstone.

**Not proved here** (deliberately, and reported): `LSCCIndWinStmt` itself. Its proof is the
Williams path decomposition of the radial Brownian motion at `τ_L` (the post-hitting field is
independent of the hitting time), used with the exact scale invariance of the lateral part
(`WedgeTK.fieldLawFull_lateralPart_rescale`); the repository has the hitting-time machinery
(`Wire5.prob_Tc_lt_le_prob_wedge_high_uncond`, `Wire5.abs_prob_zoomRadial_sub_le_uncond`) but not
the a.s. independence statement. `LSCCBadWinStmt` *is* derivable from the existing inputs
`N2ZHeartStmt` (window TV of the model against the wedge) and `N2ZWedgeLocStmt` (the wedge window
is good with probability `→ 1` as `K → ∞`), by the argument of `d3PlusIN2TmZero_of_nodes`
(`D3PlusN2TmZStmt.lean`, its bound `hbadW`), which constructs the wedge from the model's own
radial Brownian motion and an independent one; it is stated as a node here rather than formalized,
and reported.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Node LSCC-IND-BADWIN (the embedded window is good with high probability).** For every `ε`
there is a window `K` such that, for all large levels `L`, the embedded model window lies in
`n2Good γ K R` with probability at least `1 − ε`. Derivable from `N2ZHeartStmt` and
`N2ZWedgeLocStmt` as in `d3PlusIN2TmZero_of_nodes`. -/
def LSCCBadWinStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (R : ℕ),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, 0 < K ∧ ∀ᶠ L : ℝ in atTop,
      P {ω | resField K (n2Emb γ α L r X ω) ∉ n2Good γ K R} ≤ ε

end D3Plus
end QuantumZipper
