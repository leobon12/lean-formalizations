import QuantumZipper.Proofs.RS.TransienceMarkov
import QuantumZipper.Proofs.RS.TransienceScale
import QuantumZipper.Blueprint.External

/-!
# EXT-RS node RSS: `Blueprint.RohdeSchrammSimple` is proved (κ ∈ (0,4])

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **RSS** (DECISIONS D1: κ = 4 included).

For a Brownian motion `B` and `0 < κ ≤ 4`, almost surely the SLE_κ trace `η` is a simple chord
(`η 0 = 0`, continuous and injective on `[0,∞)`, in `ℍ` at positive times, `‖η t‖ → ∞`) and
`K_t = η '' (0,t]` for every `t ≥ 0`. Assembled from
* TR4 `ae_sleTrace_good` (existence and continuity of the trace; RS Thm 5.1, p. 20);
* SIM `ae_sleTrace_simple_of_le_four` and HULL `ae_fwdHull_eq_sleTrace_image_of_le_four`
  (RS Thm 6.1, p. 23);
* TRANS: `ae_zero_not_mem_closure_Ici_one` (Markov step, via BASE and KR = RS Lemma 7.2) and
  `transience_of_avoid_zero` (scaling step) — RS Thm 7.1 and its proof, pp. 31, 34.

Source: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Theorems 4.7,
5.1, 6.1, 7.1 and Lemma 7.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace RS

/-- **RSS.** `Blueprint.RohdeSchrammSimple` holds. -/
theorem rohdeSchrammSimple : Blueprint.RohdeSchrammSimple := by
  intro κ hκ hκ4 Ω _ P _ B hB
  have htr := transience_of_avoid_zero hκ (by linarith)
    (by intro Ω' _ P' _ B' hB'; exact ae_zero_not_mem_closure_Ici_one hκ hκ4 hB') P B hB
  obtain ⟨δ, -, hgood⟩ := ae_sleTrace_good hB hκ (by linarith)
  filter_upwards [htr, hgood, ae_sleTrace_simple_of_le_four hB hκ hκ4,
    ae_fwdHull_eq_sleTrace_image_of_le_four hB hκ hκ4] with ω ht hg hs hh
  exact ⟨⟨hg.1, hg.2.1, hs.1, hs.2, ht⟩, hh⟩

end RS
end QuantumZipper
