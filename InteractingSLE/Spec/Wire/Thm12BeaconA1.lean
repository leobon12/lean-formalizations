/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawStmt
import InteractingSLE.Spec.ZhanGT4.A1G3RRMain
import InteractingSLE.Spec.Wire.Thm12LateReference

/-! # R83: the corrected C law inputs, with rows and measurability proved -/
set_option autoImplicit false
noncomputable section
namespace InteractingSLE.Wire.Beacon

/-- G3's proved rows and the C density-to-law input give the unchanged Canon core. -/
theorem coreG3_of_lawC {κ : ℝ} (h : ZhanGT4.A1RLaw.G3RectLawC κ) :
    ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ :=
  ZhanGT4.A1RLaw.a1DualCouplingG3CoreStatement_of_seedGC
    (ZhanGT4.A1RLaw.a1DualCouplingG3SeedGCStatement_of_rowLawC (ZhanGT4.A1G3RR.g3RectRow κ) h)

/-- Eight's C density-to-law input alone gives the unchanged Canon core. -/
theorem coreEight_of_lawC {κ : ℝ} (h : ZhanGT4.A1RLaw.EightRectLawC κ) :
    ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ :=
  ZhanGT4.A1RLaw.a1DualCouplingEightCoreStatement_of_seedMC
    (ZhanGT4.A1RLaw.a1DualCouplingEightSeedMCStatement_of_rectLawC h)

/-- The acyclic R74 Cond44 theorem from the corrected two A.1 law inputs. -/
theorem cond44 (hG : ∀ κ, ZhanGT4.A1RLaw.G3RectLawC κ) (hE : ∀ κ, ZhanGT4.A1RLaw.EightRectLawC κ) :
    Sec7.AdmCode.Theorem12ParamCond44Statement.{0} :=
  late_theorem12ParamCond44Statement (fun κ => coreG3_of_lawC (hG κ)) (fun κ => coreEight_of_lawC (hE κ))

end InteractingSLE.Wire.Beacon
