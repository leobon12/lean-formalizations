/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptAdmit
import InteractingSLE.Spec.Wire.T12Asm6

/-!
# Theorems 1.2 and 1.3 from the proved fibre leaf

Packet PROVE-AUX61-CAPTURE. `Aux61Cpt.cptFibreCover` (the fibre leaf, PROVED with no input) at universes `u` and
`0` supplies exactly the `hDy`/`hDy0` binders of `Wire.T12Asm6.theorem12Statement_of_covers` and
`theorem13Statement_of_covers`.

The fibre leaf is an input of Theorems 1.2–1.3 and uses neither (R48); these two theorems are its consumers.
-/

set_option autoImplicit false

namespace InteractingSLE.Sec5.Aux61Cpt

universe u

/-- The universe-`0` fibre leaf (the `hDy0` binder). -/
theorem cptFibreCover₀ :
    Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  cptFibreCover.{0}

/-- **Theorem 1.2's statement** from the proved fibre leaves. -/
theorem theorem12Statement_of_cptCover : Exist.Theorem12Statement.{u} :=
  Wire.T12Asm6.theorem12Statement_of_covers cptFibreCover.{u} cptFibreCover₀

/-- **Theorem 1.3's statement** from the proved universe-`0` fibre leaf. -/
theorem theorem13Statement_of_cptCover : Exist.Theorem13Statement.{u} :=
  Wire.T12Asm6.theorem13Statement_of_covers cptFibreCover₀

end InteractingSLE.Sec5.Aux61Cpt
