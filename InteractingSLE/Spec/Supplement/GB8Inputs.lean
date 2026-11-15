/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8InputsRef
import InteractingSLE.Spec.Supplement.GB8InputsRight

/-!
# Lemma GB8 from its one remaining input

Packet PROVE-T14-TIP4. PROVE-T14-TIP2 reduced Lemma GB8 (`Supp8.GB8.GB8Statement`, supplement §8.8, pp. 523–524) to
three named inputs (`Supp8.GB8.gb8Statement_of_inputs`). Two of them are now proved:

* `ReferenceSwallowStatement` (`referenceSwallowStatement`, `GB8InputsRef.lean`: Aux. 22's strip endpoint);
* `RightNoContactStatement` (`rightNoContactStatement`, `GB8InputsRight.lean`: Lemmas GB7a and G12, and GB7a's
  comparison picture when every right mark sits at `x₊`).

So GB8 follows from `EventualSepStatement` alone (`gb8Statement_of_eventualSep`), and conversely
(`eventualSepStatement_of_gb8`, vacuously): `gb8Statement_iff_eventualSep`.

**Warning (see the handoff `planning/handoffs/PROVE-T14-TIP4.md`).** `EventualSepStatement` is not an independent input:
it asks for a uniform lower bound on *every* gap after a rational time on the no-contact event, but the right total
`κ/2 − 2` is critical (the outer right gap is a dimension-two Bessel-type process, whose infimum over `[q, ∞)` is `0`),
so its only proof is through GB8's own conclusion that the no-contact event is null.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace Supp8

namespace GB8

/-- **Lemma GB8 from `EventualSepStatement`** (the other two inputs of PROVE-T14-TIP2's reduction are proved). -/
theorem gb8Statement_of_eventualSep (hSep : EventualSepStatement.{u}) : GB8Statement.{u} :=
  gb8Statement_of_inputs referenceSwallowStatement.{0} hSep rightNoContactStatement.{u}

/-- **GB8 implies `EventualSepStatement`** (vacuously): on GB8's almost sure event the premise "infinite lifetime and
the outer left mark never meets the driver" fails. -/
theorem eventualSepStatement_of_gb8 (h : GB8Statement.{u}) : EventualSepStatement.{u} := by
  intro κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR Ω mΩ P 𝓕 W VL VR B ζ hE htr
  filter_upwards [h κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR P 𝓕 W VL VR B ζ hE htr]
    with ω hω hζ hlt
  obtain ⟨⟨τ, hτ, -⟩, -⟩ := hω
  exfalso
  rcases hτ.2.2 with ⟨-, he⟩ | ⟨hτζ, -⟩
  · exact (hlt τ).ne he
  · rw [hζ] at hτζ
    exact ENNReal.coe_ne_top hτζ

/-- **The remaining input is equivalent to GB8** (given the two proved inputs): `EventualSepStatement` is not a
reduction of GB8 but a reformulation of its main assertion. -/
theorem gb8Statement_iff_eventualSep : GB8Statement.{u} ↔ EventualSepStatement.{u} :=
  ⟨eventualSepStatement_of_gb8, gb8Statement_of_eventualSep⟩

end GB8

end Supp8

end InteractingSLE
