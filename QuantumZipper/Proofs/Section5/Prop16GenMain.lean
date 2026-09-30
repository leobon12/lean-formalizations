import QuantumZipper.Proofs.Section5.Prop16GenPos
import QuantumZipper.Proofs.Section5.Prop1617Proved
import QuantumZipper.Statements.Prop16General

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6 without the positivity presupposition: proof (D96)

`theorem1_6_general_proved : theorem1_6_general`. The positivity `0 < E ν_h[a,b]` is proved by
`Prop16Asm.prop16Gen_lintegral_pos` (Prop16GenPos.lean). The rest is `theorem1_6_proved`.
Sheffield, arXiv:1012.4797, Proposition 1.6 (PDF p. 24–25).
-/

namespace QuantumZipper

/-- **Proposition 1.6 with only `E ν_h[a,b] < ∞` assumed (D96).** -/
theorem theorem1_6_general_proved : theorem1_6_general := by
  intro γ hγ hγ2 D c d a b hDo hDc hDb hDH hcd hfr hhd hab hca hbd h0 hh0 Ω _ P _ X hX hfin
  exact theorem1_6_proved γ hγ hγ2 D c d a b hDo hDc hDb hDH hcd hfr hhd hab hca hbd h0 hh0 P X
    hX (Prop16Asm.prop16Gen_lintegral_pos hγ hγ2 ⟨hDo, hDc, hDb, hDH, hcd, hfr, hhd⟩ hab hca hbd
      hh0 hX) hfin

end QuantumZipper
