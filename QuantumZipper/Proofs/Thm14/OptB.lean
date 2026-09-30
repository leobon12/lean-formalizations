import QuantumZipper.Proofs.Thm14.ConsumersOptB
import QuantumZipper.Proofs.Complex.JSShadowRemovable
import QuantumZipper.Proofs.Complex.JSLayerShadowFinal

/-!
# `ae_removable_doubledHull` and OPTB-SWITCH (DECISIONS D6), unconditional in C0/C1

EXT-JS nodes C0 (`JS.removable_of_shadow`) and C1 (`JS.shadowSum_lt_top_of_layerDecay`) discharge
the hypotheses `JS.C0Stmt`, `JS.C1Stmt` of `Proofs/Thm14/RemovableDoubledHull.lean` and
`Proofs/Thm14/ConsumersOptB.lean`. This gives the TASKS §4 / D6 target
`ae_removable_doubledHull` (Jones–Smirnov, Ark. Mat. 38 (2000), Cor. 2, applied through its
proof; Rohde–Schramm, Ann. of Math. 161 (2005), Thm 5.2 via `RS.revMapHolder`) and the Option B
forms of the Theorem 1.4 consumers, whose only remaining blueprint hypotheses are
`RevMapCaratheodory` and `RohdeSchrammSimple` (plus `theorem1_3` and
`RevCouplingBoundaryMeasureRegular` for Theorem 1.4(a), as before).
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace JS

/-- Node C0 in the form `C0Stmt`. -/
theorem c0Stmt : C0Stmt := fun hK _ _ _ _ hF hSH hcov => removable_of_shadow hK hF hSH hcov

/-- Node C1 in the form `C1Stmt`. -/
theorem c1Stmt : C1Stmt := fun hF hL => shadowSum_lt_top_of_layerDecay hF hL

/-- **`ae_removable_doubledHull`** (TASKS §4 "EXT-JS / D6", DECISIONS D6):
`RevMapHolder → RevMapCaratheodory → RohdeSchrammSimple → ∀ κ ∈ (0,4), T > 0`, almost surely the
doubled reverse SLE hull `closure K ∪ conj '' closure K`, `K = revHull (√κ B) T`, is conformally
removable. -/
theorem ae_removable_doubledHull (hRMH : Blueprint.RevMapHolder)
    (hCar : Blueprint.RevMapCaratheodory) (hRSS : Blueprint.RohdeSchrammSimple) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ᵐ ω ∂P, IsConformallyRemovable (closure (revHull (drive κ B ω) T) ∪
        conj '' closure (revHull (drive κ B ω) T)) :=
  ae_removable_doubledHull_of c0Stmt c1Stmt hRMH hCar hRSS

/-- `ae_removable_doubledHull` with `RevMapHolder` discharged by `RS.revMapHolder`. -/
theorem ae_removable_doubledHull' (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ᵐ ω ∂P, IsConformallyRemovable (closure (revHull (drive κ B ω) T) ∪
        conj '' closure (revHull (drive κ B ω) T)) :=
  ae_removable_doubledHull RS.revMapHolder hCar hRSS

end JS

namespace Thm14OptB

open Thm14Determination Thm14WeldingData Thm14GoodDriverSet

/-- **OPTB-SWITCH, `WeldingData.ae_good_drive`.** -/
theorem ae_good_drive' (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧
      IsSimpleCurveHull (revHull (drive κ B ω) T) ∧
      IsConformallyRemovable (closure (revHull (drive κ B ω) T) ∪
        conj '' closure (revHull (drive κ B ω) T)) :=
  ae_good_drive JS.c0Stmt JS.c1Stmt hCar hRSS hκ0 hκ4 hT P B hB

/-- **OPTB-SWITCH, `GoodDriverSet.exists_goodDriverSet`.** -/
theorem exists_goodDriverSet' (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ G : Set C(Icc (0 : ℝ) T, ℝ), MeasurableSet G ∧
      (∀ g ∈ G, GoodDriver T (extIccPath hT.le g)) ∧
      ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ Thm14WeldingData.pathC T (drive κ B ω) ∈ G :=
  exists_goodDriverSet JS.c0Stmt JS.c1Stmt hCar hRSS hκ0 hκ4 hT P B hB

/-- **OPTB-SWITCH, `DriverSide.exists_measurable_driver_of_weldingData`.** -/
theorem exists_measurable_driver_of_weldingData' (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ F : ℝ × (ℚ → ℝ) → (ℝ → ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, F (weldingData (drive κ B ω) T) t = drive κ B ω t :=
  exists_measurable_driver_of_weldingData JS.c0Stmt JS.c1Stmt hCar hRSS hκ0 hκ4 hT P B hB

/-- **OPTB-SWITCH, `FromThm13.theorem1_4a_of_theorem1_3`**: Theorem 1.4(a) from Theorem 1.3,
`RevMapCaratheodory`, `RohdeSchrammSimple` and `RevCouplingBoundaryMeasureRegular` (no longer
`RohdeSchrammHolder` or `JonesSmirnovRemovable`). -/
theorem theorem1_4a_of_theorem1_3' (h13 : theorem1_3) (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple)
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) : theorem1_4a :=
  theorem1_4a_of_theorem1_3 h13 JS.c0Stmt JS.c1Stmt hCar hRSS hReg

end Thm14OptB

end QuantumZipper
