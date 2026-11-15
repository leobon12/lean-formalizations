/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Seal.Final
import InteractingSLE.Spec.AuditFix.StrongCross
import InteractingSLE.Frozen.Spec.IsFlowLine_stays_right_of_lt

/-!
# Closed inputs for the contact-scope extension of Theorem 1.5 (audit fix, contact scope)

Packet PROVE-AF-CONTACT (audit priority 1, audit §2.1, p. 5). The sealed Theorem 1.5 assembly
(`Seal.Final.theorem15Statement_closed`, through `Wire.theorem15Statement_current`) builds its merging and crossing
clauses from five named statements:

* Lemma 7.7's first contact with confinement (`Supp10.Lemma77Statement`),
* the first-contact restart carrier with the active prime end (`Theorem15D5.FirstContactRestartLimStatement`, the
  conditional coupling of Lemma 7.8 / W8 in kernel form),
* Lemma 7.5 in universal form (`Theorem15.Lemma75Statement`, universes `u` and `0`),
* Aux. lemma 25 (`Theorem15.aux25Statement`, already closed),
* Theorem W5 on the canonical space (`Theorem15.W5Statement.{0}`).

None of them restricts the first contact to the open half-plane: Lemma 7.7 starts from any contact of the closed
available paths (`s ≤ ζ₁`, `t ≤ ζ₂`), and the restart carrier applies at every first contact with two nonempty
continuations (`s₀ < ζ₁`, `t₀ < ζ₂`), real or interior. The frozen anchors only *trigger* on interior available
contacts. This file re-derives the five statements as closed theorems, with no new mathematics: each is the term
used inside the sealed chain (or an equal-typed shorter term from the same landed modules), with Theorems 1.2–1.3
supplied by the proved fibre covers (`Sec5.Aux61Cpt.theorem12Statement_of_cptCover`,
`theorem13Statement_of_cptCover`).

* Lemma 7.5 is taken from Theorems 1.2–1.3 directly (`Restart.FCPlumb.lemma75Statement_of_thm12_thm13`), the same
  Prop that the sealed chain obtains as `Wire.lemma75Statement_current`.
* W5 at universe `0` is the first clause of the sealed frozen Theorem 1.5 (i), `IsFlowLine.stays_right_of_lt`
  (`Theorem15.W5Statement` is exactly that clause's universal closure).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.AuditFix.ContactInputs

/-- **Theorem 1.2**, closed (the proved fibre covers). -/
theorem theorem12 : Exist.Theorem12Statement.{u} :=
  Sec5.Aux61Cpt.theorem12Statement_of_cptCover

/-- **Theorem 1.3**, closed (the proved universe-`0` fibre cover). -/
theorem theorem13 : Exist.Theorem13Statement.{u} :=
  Sec5.Aux61Cpt.theorem13Statement_of_cptCover

/-- **Lemma 7.5** (universal determination), closed. -/
theorem lemma75 : Theorem15.Lemma75Statement.{u} :=
  Restart.FCPlumb.lemma75Statement_of_thm12_thm13 theorem12 theorem13

/-- **Lemma 7.7** (first contact of the closed available paths, with confinement), closed: the same term as
PROVE-AF-CROSS's `Cross.lemma77_restartLim_closed` (one copy; ruling R122, seal-closure R48). -/
theorem lemma77 : Supp10.Lemma77Statement.{u} :=
  AuditFix.Cross.lemma77_restartLim_closed.1

/-- **The first-contact restart carrier with the active prime end** (Lemma 7.8 in kernel form, at every first
contact with two nonempty continuations), closed: the same term as `Cross.lemma77_restartLim_closed`. -/
theorem firstContactRestartLim : Theorem15D5.FirstContactRestartLimStatement.{u} :=
  AuditFix.Cross.lemma77_restartLim_closed.2

/-- **Theorem W8 at `σ = 0`** (a contact of the closed available paths forces a first contact), closed. -/
theorem w8FirstContact : Theorem15.W8FirstContactStatement.{u} :=
  Supp10.w8FirstContactStatement_of_lemma77 lemma77

/-- **Theorem 7.12C, equal angles** (merging at every first contact with two nonempty continuations), closed. -/
theorem thm712CMerging : Theorem15.Thm712CMergingStatement.{u} :=
  Restart.thm712CMergingStatement_of_restart
    (Theorem15D5.firstContactRestartStatement_of_lim firstContactRestartLim) lemma75.{0}

/-- **Theorem W5 on the canonical space**: the first clause of the sealed frozen Theorem 1.5 (i) at universe `0`. -/
theorem w5₀ : Theorem15.W5Statement.{0} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  exact (IsFlowLine.stays_right_of_lt hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂).1

/-- **Theorem 7.12C, strict angles** (crossing at every first contact with two nonempty continuations), closed. -/
theorem thm712CCrossing : Theorem15.Thm712CCrossingStatement.{u} :=
  Supp10.thm712CCrossingStatement_of_inputs lemma77
    (Theorem15D5.chartOrderAfterCrossingStatement_of_restartLim firstContactRestartLim w5₀)

end InteractingSLE.AuditFix.ContactInputs
