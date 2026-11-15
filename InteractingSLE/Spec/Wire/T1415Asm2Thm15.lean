/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T15AsmTop
import InteractingSLE.Spec.ZhanGT4.A1G3LgFinal
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopMain
import InteractingSLE.Spec.ZhanGT4.A1ESRecWire

/-!
# Theorem 1.5 re-assembled: A.1 discharged

Packet PROVE-T1415-ASSEMBLE2. PROVE-T15-ASSEMBLE's main top `T15Asm.theorem15Statement_of_dirsC_dyCover` took, besides
Theorems 1.2–1.3 and the dyadic fibre cover of Prop. 5.1's (E1), three directional C laws of Zhan's A.1 (R83). All
three are now proved for every parameter:

* `ZhanGT4.A1G3L2.g3RectLawSndC_holds` (PROVE-A1-G3LAW2),
* `ZhanGT4.A1G3Lg.g3RectLawFstC_holds`,
* `ZhanGT4.A1ESRec.eightRectLawSndC` (PROVE-A1-EIGHTSNDREC).

So **`theorem15Statement_assembled2`** proves Theorem 1.5 from Theorems 1.2–1.3 (universes `u` and `0`) and
`DyActFibreCoverOn` (small gap, `RefWin`; universes `u` and `0`) alone. These are the same fibre covers the
Theorem 1.2 tops take.

R48: Theorems 1.2–1.3 enter only as hypotheses of this Theorem 1.5 result. A.1's three laws use neither of them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

/-- **Theorem 1.5 from Theorems 1.2–1.3 and the dyadic fibre cover of Prop. 5.1's (E1)** (universes `u` and `0`).
Zhan's A.1 directions, the last non-root inputs of `T15Asm.theorem15Statement_of_dirsC_dyCover`, are proved. -/
theorem theorem15Statement_assembled2
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin) :
    Theorem15Statement.{u} :=
  T15Asm.theorem15Statement_of_dirsC_dyCover h12 h13 h12₀ h13₀
    (fun κ _ _ => ZhanGT4.A1G3L2.g3RectLawSndC_holds κ)
    (fun κ _ _ => ZhanGT4.A1G3Lg.g3RectLawFstC_holds κ)
    (fun κ _ => ZhanGT4.A1ESRec.eightRectLawSndC κ) hDy hDy₀

end InteractingSLE.Wire
