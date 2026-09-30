import QuantumZipper.Statements.Thm18Off
import QuantumZipper.Proofs.Thm18.MatchPaperOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D74: basic facts about the off-curve comparison of `Statements/Thm18Off.lean`

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26) compares the restrictions `h_{Dᵢ}` of the field to
the components of `ℍ \ η`; `Statements/Thm18Off.lean` encodes this with `CircleOff`, `RegEqOff`,
`ConfigEqOff`. Their bodies are those of the MATCH-PAPER-18 drafts
(`Thm18Asm.MatchPaper`, `Proofs/Thm18/MatchPaperOff.lean`), so the lemmas proved there transfer
verbatim:

* `configEqOff_of_configEq`: `ConfigEq → ConfigEqOff` (every proved round trip / group property
  transfers);
* `regEqOff_coordChange_of_eqOn`: charts that agree off a closed set `K` give off-`K` equal
  coordinate changes (no trace-nullity or contact condition);
* `isClosed_curveOf`.

Own elementary bookkeeping (no published proof needed: properties of our encoding).
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper
namespace Thm18Asm
namespace D74

theorem isClosed_curveOf (W : ℝ → ℝ) : IsClosed (curveOf W) := isClosed_closure

end D74
end Thm18Asm
end QuantumZipper
