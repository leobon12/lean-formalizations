/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3AsmEntr

/-!
# Lemma S3 in SB2(1)'s form for upper angles `ψ ≤ π/2` — PROVED from Theorems 1.2–1.3

Worker PROVE-R6-CORNER (round 8, decision D22). **`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`**: the statement
`Tc.SB2EntranceNoCommonArcLeStatement` (`SBS3DwBase`) from Theorems 1.2–1.3 (R48), by round 6's
`S3.Asm.ae_entranceNoCommonArc_of_le`. With D22 the wide-angle residual `S3.Asm.SB2EntranceWideAngleStatement` is no
longer an input of anything.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.SB.Tc

/-- **Lemma S3 in SB2(1)'s form, `ψ ≤ π/2`, PROVED** from Theorems 1.2–1.3 (R48). -/
theorem sb2EntranceNoCommonArcLeStatement_of_thm (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2EntranceNoCommonArcLeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP hψ
  exact S3.Asm.ae_entranceNoCommonArc_of_le h12p h13 h12p₀ h13₀ HP hψ.out

end InteractingSLE.Theorem14.SB.Tc
