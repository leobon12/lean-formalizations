import QuantumZipper.Proofs.Thm18.RT6bUnz
import QuantumZipper.Proofs.Thm18.G1ZA1aDrv
import QuantumZipper.Proofs.Thm18.G1ZSplitWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: the unzipped driver is a good chordal driver, up to the radial Hölder bound

The simple-chord and hull properties of the driver of `Z^A_{−b} c₀` are deterministic
consequences of those of the SLE driver (`g1zDrvGood_newDrv`: the unzipped and rescaled driver of a
good driver is good; Loewner concatenation). Only the radial Hölder bound of `RS.RadialGood` (the
Rohde–Schramm tip estimate, Rohde–Schramm, Ann. Math. 161 (2005), Thm 3.6 / Prop 3.8, for the
driver restarted at the random length time; Sheffield Thm 1.8: the unzipped curve is again an
SLE curve) remains: `UnzRadialGoodStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Radial Hölder bound for the unzipped driver** (open). -/
def UnzRadialGoodStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
      RS.RadialGood (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv

/-- **The unzipped driver is good**, from its radial Hölder bound. -/
theorem unzDriverGoodStmt_of_radial (hX1 : BaseFin.BaseFiniteStmt) (hR : UnzRadialGoodStmt) :
    UnzDriverGoodStmt := by
  intro γ Ω _ P _ B Y hS hIn b hb
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  filter_upwards [hR γ P B Y hS hIn b hb, ae_g1zDrvGood hS hIn,
    g4UpWeldCoreAStmt_of_X1 hX1 γ P B Y hS hIn hE6 hEq b hb] with ω hr hg hu
  obtain ⟨ha, ht, -, -⟩ := hu
  have e : (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv =
      g1zNewDrv (drive (γ ^ 2) B ω) (lenTimeOpen γ b (wedgeAConfig γ B Y ω).toPair)
        (areaScale (zipCapDownA γ (lenTimeOpen γ b (wedgeAConfig γ B Y ω).toPair)
          (wedgeAConfig γ B Y ω)).area) := by
    have e0 := congrArg Prod.snd (zipLenDownA_toPair_eq γ b (wedgeAConfig γ B Y ω))
    refine e0.trans (funext fun r => ?_)
    simp only [outDrv, g1zNewDrv]
    rw [max_eq_left (by positivity)]
    rfl
  have hG := G1ZA1a.g1zDrvGood_newDrv hg ht ha
  rw [e] at hr ⊢
  exact ⟨hr, hG.2.2.2.1, hG.2.2.2.2⟩

end R18
end QuantumZipper
