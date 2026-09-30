import QuantumZipper.Proofs.Thm18.RT6MODefs
import QuantumZipper.Proofs.Thm18.RT6Neg
import QuantumZipper.Proofs.Thm18.R18RTRound
import QuantumZipper.Proofs.Thm18.R18Zero
import QuantumZipper.Proofs.Thm18.RT5OMain
import QuantumZipper.Proofs.Thm18.RT5FarGeo
import QuantumZipper.Proofs.Thm18.R18RTZipMain
import QuantumZipper.Proofs.Thm18.R18RTMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D87: the D82 round trips, law invariance and continuity for the zipper on the pieces

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8, p. 26: `Z^LEN_t`
acts on the pair of quantum surfaces cut out by the curve, and for `t > 0` it is the inverse of
`Z^LEN_{−t}`. The zip-up pulls back circles off the new curve to circles off the old one, so it
reads only the pieces. In the Lean model this is recorded by two nodes:

* `ZipOffExactAStmt` (N1): at `c₀` (the wedge), zipping up the pieces and zipping up `c₀` give the
  same off-curve data;
* `ZipOffExactUnzAStmt` (N2): the same at `c₁ = Z^A_{−ℓ} c₀`, masked coordinates and driver.

From them and the D82 results (RT1 `ae_πd_offData_roundDown`, RT2 `MaskExactFullAStmt`, RT3
`DownDataMeasCStmt`, RT4's inverse argument, clause (3) `lawMA_of`) we get the two round trips,
time zero, continuity of the drivers, clause (3) and clause (1) for `zipLenMO` (D87).
The RT4 argument is repeated here with its exact conclusion (equal masked coordinates and driver);
the measure-theoretic bookkeeping is an own elementary argument, the mathematics is the paper's.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **N1: zipping up reads only the pieces, at the wedge** (Sheffield arXiv:1012.4797 p. 26: the
zip-up pulls back circles off the new curve to circles off the old one). -/
def ZipOffExactAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ᵐ ω ∂P,
      offData (zipLenUpOA γ ℓ (offConfig γ (wedgeAConfig γ B Y ω))).toPair =
        offData (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).toPair

/-- **N2: zipping up reads only the pieces, at the unzipped wedge** `c₁ = Z^A_{−ℓ} c₀`
(Sheffield arXiv:1012.4797 p. 26), masked coordinates and driver. -/
def ZipOffExactUnzAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
      πd (offData (zipLenUpOA γ ℓ (offConfig γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)))).toPair) =
        πd (offData (zipLenUpA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).toPair)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}

/-- **Deliverable 3: time zero** (D87), masked coordinates and driver. -/
theorem rt6_ae_zeroMO (hZO : ZipOffExactAStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, πd (offData (zipLenMO γ 0 (wedgeAConfig γ B Y ω)).toPair) =
      πd (offData (wedgeAConfig γ B Y ω).toPair) := by
  classical
  obtain ⟨hR, -⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  filter_upwards [hZO γ P B Y hS hIn 0 le_rfl, hR, hS.2.2.1.eval_zero_ae_eq_zero]
    with ω h1 hω h0
  rw [zipLenMO_of_nonneg le_rfl, Function.comp_apply, h1, ← zipLenA_of_nonneg le_rfl,
    toPair_zipLenA_zero (c := wedgeAConfig γ B Y ω) rfl hω.1 hω.2]
  have hW0 : drive (γ ^ 2) B ω 0 = 0 := by simp [drive, h0]
  obtain ⟨e1, -, e3⟩ := zipLenC_zero_data (γ := γ) hω.1 hω.2 hW0
  have hp : (wedgeAConfig γ B Y ω).toPair = (Y ω, drive (γ ^ 2) B ω) := rfl
  rw [hp]
  have hdrv : ∀ u : ℝ, 0 ≤ u → (zipLenC γ 0 (Y ω, drive (γ ^ 2) B ω)).2 u =
      drive (γ ^ 2) B ω u := fun u hu => e3 ⟨u, hu⟩
  have hcur := curveOf_congr hdrv
  refine Prod.ext ?_ ?_
  · funext i
    simp only [πd, offData, lawDataOff]
    rw [hcur, e1]
  · simp only [πd, offData]
    funext t
    exact e3 t

/-- **Deliverable 4: the drivers of `zipLenMO γ ℓ c₀` are continuous on `[0,∞)`** a.s. -/
theorem rt6_ae_contMO (hX1 : BaseFin.BaseFiniteStmt) (hZO : ZipOffExactAStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, Continuous (fun u : ℝ≥0 => (zipLenMO γ ℓ (wedgeAConfig γ B Y ω)).drv u) := by
  by_cases hℓ : 0 ≤ ℓ
  · have hex : ∀ᵐ ω ∂P, ∃ p, IsLenWeldingDriver γ (Y ω) ℓ p := by
      rcases hℓ.lt_or_eq with h | h
      · have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
        have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
        exact (g4WeldAStmt_holds hX1 γ P B Y hS hIn hE6 hEq ℓ h).mono fun ω hw => hw.1
      · subst h
        exact ae_of_all _ fun ω => ⟨_, isLenWeldingDriver_zero_zero γ _⟩
    filter_upwards [hZO γ P B Y hS hIn ℓ hℓ, hex, D74.ae_wedgeConfig_snd_good hS]
      with ω h1 hx hg
    have hZc := continuous_zipLenUpA_drv (γ := γ) (ℓ := ℓ) (c := wedgeAConfig γ B Y ω) hg.1 hg.2
      (lenWeldDriver_spec hx)
    have e : (fun u : ℝ≥0 => (zipLenUpOA γ ℓ (offConfig γ (wedgeAConfig γ B Y ω))).drv u) =
        fun u : ℝ≥0 => (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv u := congrArg Prod.snd h1
    rw [zipLenMO_of_nonneg hℓ, Function.comp_apply, e]
    exact hZc.comp continuous_subtype_val
  · filter_upwards [D74.ae_wedgeConfig_snd_good hS] with ω hg
    rw [zipLenMO_of_neg (not_le.1 hℓ)]
    exact (zipLenDownA_drv_good (γ := γ) (ℓ := -ℓ)
      (continuous_drvOfData_offData (x := (wedgeAConfig γ B Y ω).toPair) hg.1)).1.comp
      continuous_subtype_val

end R18
end QuantumZipper
