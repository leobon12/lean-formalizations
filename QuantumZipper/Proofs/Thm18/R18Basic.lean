import QuantumZipper.Statements.Thm18Paper
import QuantumZipper.Proofs.Zipper.LocLenDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18: bridges between the area-carrying zippers (D76) and the field-normalized ones

`Statements/Thm18Paper.lean` (decision D76) defines configurations `AreaConfig = (field, driver, μ)`
whose zips push `μ` forward and normalize by (1.8) with the carried area (Sheffield,
arXiv:1012.4797, p. 26: "`B₁(0)` has area one in the transformed quantum measure"). This file proves
that the new maps agree with the old ones (`canonConfig`, `zipLenUpC`, `LocLen.zipLenDownArc`)
whenever the carried area gives the same scale as the field's own area (`scaleParam`), and the
definitional identities of the open-arc lengths with `LocLen` (D75). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- `scaleParam` is `areaScale` of the field's own quantum area. -/
theorem areaScale_qAreaMeasure (γ : ℝ) (x : FieldSample) :
    areaScale (qAreaMeasure γ x) = scaleParam γ x := rfl

theorem configLawOff_wedgeAConfig (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) :
    configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P = configLawOff (wedgeConfig γ B Y) P :=
  rfl

/-- The rescaling (1.8) by the carried area is the old `canonConfig` when both give the same scale. -/
theorem toPair_canonAConfig {γ : ℝ} {c : AreaConfig} (h : areaScale c.area = scaleParam γ c.fld) :
    (canonAConfig γ c).toPair = canonConfig γ c.toPair := by
  simp only [canonAConfig, AreaConfig.toPair, canonConfig, canonical, h]

/-- `Z^LEN_ℓ` (zip up) with the carried area agrees with `zipLenUpC` when the pushed area and the
zipped field's own area give the same scale. -/
theorem toPair_zipLenUpA {γ ℓ : ℝ} {c : AreaConfig}
    (h : areaScale (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1 (lenWeldDriver γ c.fld ℓ).2 c).area =
      scaleParam γ (zipWeldUp γ (lenWeldDriver γ c.fld ℓ).1 (lenWeldDriver γ c.fld ℓ).2
        c.toPair).1) :
    (zipLenUpA γ ℓ c).toPair = zipLenUpC γ ℓ c.toPair := by
  rw [zipLenUpA, toPair_canonAConfig h]
  rfl

/-- The open-arc length of the statement is `LocLen.arcLen`. -/
theorem openArcLen_eq : openArcLen = LocLen.arcLen := rfl

theorem unzipLengthsOpen_eq : unzipLengthsOpen = LocLen.unzipLengthsArc := rfl

theorem lenTimeOpen_eq : lenTimeOpen = LocLen.lenTimeArc := rfl

/-- `Z^LEN_{−ℓ}` with the carried area agrees with `LocLen.zipLenDownArc` when the pushed area and
the unzipped field's own area give the same scale. -/
theorem toPair_zipLenDownA {γ ℓ : ℝ} {c : AreaConfig}
    (h : areaScale (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c).area =
      scaleParam γ (zipCapDown γ (lenTimeOpen γ ℓ c.toPair) c.toPair).1) :
    (zipLenDownA γ ℓ c).toPair = LocLen.zipLenDownArc γ ℓ c.toPair := by
  rw [zipLenDownA, toPair_canonAConfig h]
  simp only [zipCapDownA, canonConfig, zipCapDown, LocLen.zipLenDownArc, canonical,
    lenTimeOpen_eq, AreaConfig.toPair]
  refine Prod.ext rfl ?_
  funext s
  simp only
  rw [max_eq_left (mul_nonneg (sq_nonneg _) (le_max_right s 0))]

theorem zipLenA_of_nonneg {γ ℓ : ℝ} (hℓ : 0 ≤ ℓ) : zipLenA γ ℓ = zipLenUpA γ ℓ := by
  simp only [zipLenA, hℓ, ↓reduceIte]

/-! ## The two facts of Sheffield's argument that D76 requires to be proved -/

/-- **The curve has zero quantum area** (Sheffield arXiv:1012.4797 §4.1 p. 48: `η` is a measure
zero set; implicit in "the transformed quantum measure" of the pieces, p. 26). In the Theorem 1.8
setting, a.s. the quantum area of the wedge charges no point of the SLE_κ curve `η = curveOf W`. -/
def CurveAreaNullStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    IsBrownianReal B P → IsQuantumWedge γ (γ - 2 / γ) Y P → IndepFun (pathOf B) Y P →
    ∀ᵐ ω ∂P, qAreaMeasure γ (Y ω) (curveOf (drive (γ ^ 2) B ω)) = 0

end R18
end QuantumZipper
