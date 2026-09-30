import QuantumZipper.Statements.Thm15Full
import QuantumZipper.Proofs.MainResults13
import QuantumZipper.Proofs.Zipper.Cor15FullCore
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

/-!
# Corollary 1.5, full form (D97)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
`theorem1_5_full_proved : theorem1_5_full`: clauses (a), (b) are `theorem1_5_proved`; clause (c)
(the welding driver of `f^h_t` exists and is unique on `[0,t]`, a.s. for each `t ≥ 0`) is
`Cor15Group.cor15Full_ae_weldUniq` for `t > 0` (Theorems 1.3 and 1.4(a) via the Cor 1.5 chain)
and is trivial at `t = 0` (the zero driver; `[0,0] = {0}` and every driver vanishes at `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace QuantumZipper

/-- **Corollary 1.5, full form, proved** (standard axioms only). -/
theorem theorem1_5_full_proved : theorem1_5_full := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  obtain ⟨ha, hb⟩ := theorem1_5_proved κ hκ hκ4 P B X hB hX hind
  refine ⟨ha, hb, fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht | rfl
  · exact Cor15Group.cor15Full_ae_weldUniq theorem1_3_proved RS.rohdeSchrammSimple hκ hκ4 hB hX
      hind ht
  · refine Filter.Eventually.of_forall fun ω => ⟨⟨_, Cor15Partial.isWeldingDriver_zero _ _⟩,
      fun W₁ W₂ h₁ h₂ s hs => ?_⟩
    obtain rfl : s = 0 := le_antisymm hs.2 hs.1
    rw [h₁.2.1, h₂.2.1]

end QuantumZipper

