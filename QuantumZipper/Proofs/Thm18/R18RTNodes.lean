import QuantumZipper.Proofs.Thm18.R18RTDefs
import QuantumZipper.Proofs.Thm18.R18G4Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D82: the two inputs of the inverse transfer (handoff/R18-PLAN.md §6)

Sheffield, arXiv:1012.4797, Theorem 1.8 (1) (p. 26): `Z^LEN_ℓ` is the inverse of `Z^LEN_{−ℓ}`.
The round trip `Z_{−ℓ}(Z_ℓ c) = c` is proved as in the paper: by the law invariance of unzipping
(E6) the wedge configuration `c₀` has the law of `c₁ = Z_{−ℓ} c₀`, and at `c₁` the round trip is
`Z_{−ℓ}(Z_ℓ(Z_{−ℓ} c₀)) = Z_{−ℓ} c₀`, i.e. the proved round trip `Z_ℓ ∘ Z_{−ℓ} = id`. Two inputs:

* `MaskExactAStmt` (task RT2): unzipping the wedge configuration read off its curve gives the
  same masked data as unzipping it. This is the formal content of "`h` may be defined arbitrarily
  on the measure-zero set `η`" (Sheffield §4.1 p. 48; Berestycki–Powell arXiv:2404.16642 Thm 8.16
  and Rem 8.10, p. 283): circles crossing `η` contribute nothing to the regularized pairings of
  the field with measures that only touch `η` (log growth of circle averages, Hu–Miller–Peres,
  Ann. Probab. 38 (2010), Prop 2.1; Beurling estimate for the forward map).
* `DownDataMeasStmt` (task RT3): the unzipping of the pieces is a Borel function of the masked
  data on a Borel set carrying the wedge data (the paper treats `Z^LEN_{−ℓ}` as a measurable map;
  cf. `LocLen.unzipMeasArc_of_localAbsRich` for the full-data version along the sample).

Data are projected to the circle coordinates and the driver, `πd d = (d.1.1, d.2)`: the pieces
`configOfData γ d` only read these.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The circle coordinates and the driver of the data. -/
def πd (d : E6.FullData) : (ℕ → ℝ) × (ℝ≥0 → ℝ) := (d.1.1, d.2)

theorem measurable_πd : Measurable πd :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

/-- **RT2 (masked exactness of unzipping the wedge).** In the Theorem 1.8 setting, for `ℓ > 0`,
a.s. unzipping the pieces (`zipLenDownMA`) and unzipping the configuration (`zipLenDownA`) give
the same masked circle coordinates and the same driver on `[0,∞)`, and for every test function
the same masked pairing a.s. -/
def MaskExactAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ →
      (∀ᵐ ω ∂P, πd (offData (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)).toPair) =
        πd (offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair)) ∧
      ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
        (offData (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)).toPair).1.2 ρ =
          (offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair).1.2 ρ

end R18
end QuantumZipper
