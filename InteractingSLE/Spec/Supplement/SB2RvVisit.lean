/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2RoCover
import InteractingSLE.Spec.Supplement.SB2GjStmt
import InteractingSLE.Spec.Supplement.SB2GjCanon
import InteractingSLE.Spec.Supplement.SB2GjMain
import InteractingSLE.Spec.Wire.T14Asm7

/-!
# A positive relative root visits `R` (GEOM2's `Gj.SB2PosRootVisitStatement`, D79 (3))

PROVE-GW2-ROOTX round 18. GEOM2's root identification (`Gj.sb2LowerRootIdentStatementX_of_visit`,
`Gj.sb2LowerRootDetWStatement_of_visit`, hence `hdet`'s `Ch.SB2LowerRootDetWStatement`) has one input, the named
statement `Gj.SB2PosRootVisitStatement`: almost surely at an upper launch with a positive relative root at `ℓ`
(`Ct.PosRootAt`), B's piece `ℓ` visits `R = max (A ∩ ℝ)` before its lifetime.

It follows from ROOTX's round-17 `Ro.ae_rootEv_of_posRootAt`: the sample lies in the root event `Ne.rootEv`, whose last
clause is `entrR < ζ_ℓ`; if the piece never visited `R`, its entrance time would be its lifetime
(`Ck.entrTime_eq_life`). Theorems 1.2–1.3 are the landed `Wire.T14Asm7.h12`, `h13`, `h12₀`, `h13₀`.

* **`Ro.sb2PosRootVisitStatement : Gj.SB2PosRootVisitStatement`** — exactly as stated, no hypotheses;
* **`Ro.sb2LowerRootDetWStatement_closed`**: the top's `hdet` (`Ch.SB2LowerRootDetWStatement` at
  `theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13`), GEOM2's `Gj.sb2LowerRootDetWStatement_of_visit`
  with it, no hypotheses;
* `Ro.sb2LowerRootIdentStatementX_closed`: GEOM2's root identity `Gj.SB2LowerRootIdentStatementX`, likewise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

universe u

namespace InteractingSLE.Theorem14.SB.Ro

open Exist Exist.Staged Exist.StagedLaw Lk GW1W GW1Bookkeep GW1Conn

/-- **A positive relative root visits `R`** (GEOM2's `Gj.SB2PosRootVisitStatement`, proved). -/
theorem sb2PosRootVisitStatement : Gj.SB2PosRootVisitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlθ hleft ℓ
  filter_upwards [ae_rootEv_of_posRootAt Wire.T14Asm7.h12.{u} Wire.T14Asm7.h13.{u} Wire.T14Asm7.h12₀
    Wire.T14Asm7.h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft] with ω hω hup hpos
  obtain ⟨-, -, -, hent⟩ := hω hup hpos
  by_contra hv
  have he := Ck.entrTime_eq_life hv
  have he' : Nd.entrR κ b jumps E u l k ℓ ω = (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := he
  rw [he'] at hent
  exact lt_irrefl _ hent

/-- **The top's `hdet`, with no hypotheses** (GEOM2's `Gj.sb2LowerRootDetWStatement_of_visit` with the visit). -/
theorem sb2LowerRootDetWStatement_closed :
    Ch.SB2LowerRootDetWStatement.{u}
      (Param12.theorem12ParamStatement_of_thm12_thm13 Wire.T14Asm7.h12 Wire.T14Asm7.h13) :=
  Gj.sb2LowerRootDetWStatement_of_visit Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀
    sb2PosRootVisitStatement

/-- **GEOM2's root identity, with no hypotheses** (`Gj.sb2LowerRootIdentStatementX_of_visit` with the visit). -/
theorem sb2LowerRootIdentStatementX_closed :
    Gj.SB2LowerRootIdentStatementX.{u}
      (Param12.theorem12ParamStatement_of_thm12_thm13 Wire.T14Asm7.h12 Wire.T14Asm7.h13) :=
  Gj.sb2LowerRootIdentStatementX_of_visit Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀
    sb2PosRootVisitStatement

end InteractingSLE.Theorem14.SB.Ro
