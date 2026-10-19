import HigherDimLFPP.Frozen.Kappa
import HigherDimLFPP.Frozen.IsLFPPKernel
import HigherDimLFPP.Frozen.IsBandVersion
import HigherDimLFPP.Frozen.IsLFPPExponent

/-!
# Shared definitions

The definitions of the statement surface are frozen, one declaration per file, in
`HigherDimLFPP/Frozen/` (manifest `HigherDimLFPP/Frozen/frozen-anchors.json`, rulings H1–H10 in
`planning/RULINGS.md`). This file re-exports them for the proof modules:

* the variational problem: `Vg`, `energy`, `gCov`, `Ag`, `A`, `kappa`;
* the field: `Rd`, `IsLFPPKernel`, `scaleKernel`, `WN`, `IsWhiteNoise`, `bandKernel`, `bandVec`,
  `IsBandVersion`;
* LFPP: `cube`, `e₁`, `IsAdmissiblePath`, `lfppLength`, `lfppDistance`, `IsLFPPExponent`.

Proof modules must not redefine these objects.
-/
