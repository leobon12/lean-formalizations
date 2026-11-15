/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GjMain
import InteractingSLE.Spec.Supplement.SB2GjBase
import InteractingSLE.Spec.Supplement.SB2CyWord

/-!
# CONDFIN's root canonical objects with the root-word identity

Packet PROVE-GW2-GEOM2, round 17 (decision D79). **`sb2LowerRootCanonXStatement_of_visit`**: CONDFIN's
`Cy.SB2LowerRootCanonXStatement` (the input `hroot` of `Cy.sb2LowerRootDetWStatement_of_canonX`) from Theorems 1.2–1.3
and ROOTX's `Gj.SB2PosRootVisitStatement`: the base word of `Gj.exists_baseLawForX` has `Gj.BaseLawForX` at every
stage and F3LAW's root-word identity `Fp.RootWordAtX` for every root object family, and
`Gj.sb2LowerRootIdentStatementX_of_visit` gives its canonical root objects. This is CONDFIN's
`Cy.sb2LowerRootCanonXStatement_of_ident` with the base word carrying a countable profile cover.
**`sb2LowerRootDetWStatement_of_visit`**: CONDFIN's root determination `Ch.SB2LowerRootDetWStatement` through
`Cy.sb2LowerRootDetWStatement_of_canonX`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.SB.Gj

open Exist

/-- **CONDFIN's root canonical objects with the root-word identity** (Theorems 1.2–1.3 and ROOTX's positive-root
visit). -/
theorem sb2LowerRootCanonXStatement_of_visit (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hvis : SB2PosRootVisitStatement.{u}) :
    Cy.SB2LowerRootCanonXStatement.{u} (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ
  obtain ⟨β, hword, hbase⟩ := exists_baseLawForX h12 h13 h12₀ h13₀ hκ hκ4 hb P h hh hcf hζ' E hE hER u l k hu hlp
    hlθ hL hleft
  obtain ⟨G, K, x₀, Dr, hKc, hKp, hcov, hid⟩ := sb2LowerRootIdentStatementX_of_visit h12 h13 h12₀ h13₀ hvis κ hκ
    hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ β (hbase ℓ)
  exact ⟨G, _, K, x₀, Dr, hKc, hKp, hcov, hid, hword G K x₀ hKc hKp⟩

/-- **SB2(2)'s relative root determined** (CONDFIN's `Ch.SB2LowerRootDetWStatement`, through CONDFIN's
`Cy.sb2LowerRootDetWStatement_of_canonX`), from Theorems 1.2–1.3 and ROOTX's positive-root visit. -/
theorem sb2LowerRootDetWStatement_of_visit (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hvis : SB2PosRootVisitStatement.{u}) :
    Ch.SB2LowerRootDetWStatement.{u} (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  Cy.sb2LowerRootDetWStatement_of_canonX h12 h13 h12₀ h13₀ (sb2LowerRootCanonXStatement_of_visit h12 h13 h12₀ h13₀ hvis)

end InteractingSLE.Theorem14.SB.Gj
