/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CpWire
import InteractingSLE.Spec.Supplement.SB2CeTail

/-!
# K2 at the tails, closed (D80 item 2)

Packet PROVE-SB2-CANON, round 8 (D80). **`sb2LowerTailK2Statement`**: CANON's consumer form
`Cz.SB2LowerTailK2Statement` of K2 at the tails holds, by CONDFIN's landed `Ce.ae_k2_tail` in one application. Hence
hcan, the top's hTL and hdet with three of D77's four inputs left: **`sb2LowerStageCanonStatement_of_law`** (hcan from
F3LAW's (P1) `Cz.SB2LowerStageLawInStatement`), **`sb2LowerTailLiftExStatement_of_law`** (hTL from (P1) and GEOM2's
`Ct.SB2LowerRootIdentStatement`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Exist

/-- **K2 at the tails** (`Cz.SB2LowerTailK2Statement`), by CONDFIN's `Ce.ae_k2_tail` (Theorems 1.2–1.3). -/
theorem sb2LowerTailK2Statement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) :
    SB2LowerTailK2Statement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu _ hlθ _ hleft ℓ hℓ u₀ hu₀ 𝓖 A₁ A₂ A₂J h𝓖
    hfam F K x₀ β₁ types pc tL relLife S hKm hKc hKp hKF hx₀ hF hpc htL hent hFae hc hsort hlaw hP8 htypes hcover M hM0
    hMβ hle hlife
  exact Ce.ae_k2_tail h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft hℓ hu₀ h𝓖 hfam S hKm hKc hKp hKF
    hx₀ hF hpc htL hent hFae hc hsort hlaw hP8 htypes hcover hM0 hMβ hle hlife

/-- **hcan from F3LAW's (P1) alone** (Theorems 1.2–1.3). -/
theorem sb2LowerStageCanonStatement_of_law (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hP1 : SB2LowerStageLawInStatement.{u}) :
    Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  sb2LowerStageCanonStatement_of_inputs _ h12 h13 h12₀ h13₀ hP1 (sb2LowerTailK2Statement h12 h13 h12₀ h13₀)

/-- **The top's hTL from F3LAW's (P1) and GEOM2's root identification** (Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_law (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hP1 : SB2LowerStageLawInStatement.{u})
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  sb2LowerTailLiftExStatement_of_inputs h12 h13 h12₀ h13₀ hP1 (sb2LowerTailK2Statement h12 h13 h12₀ h13₀) hI

end InteractingSLE.Theorem14.SB.Cz
