import QuantumZipper.Proofs.Thm18.R18RTNodes
import QuantumZipper.Proofs.Thm18.RT5ODefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D87: the length zipper acting on the pieces for all times

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (p. 26): `Z^LEN_t`
acts on the pair of quantum surfaces cut out by the curve (p. 17; §4.1 p. 48), and `Z^LEN_t`,
`t > 0`, is the inverse of `Z^LEN_{−t}`. Decision D87 (DECISIONS.md): besides unzipping (D82,
`zipLenDownMA`), zipping up also reads the configuration off its curve first:
`zipLenMO γ ℓ = zipLenUpOA γ ℓ ∘ offConfig γ` for `ℓ ≥ 0`. The target `theorem1_8PaperMO` is
`theorem1_8PaperM` with `zipLenMO` in place of `zipLenMA`. Old definitions are untouched.

Every map `zipLenMO γ ℓ` is a function of the masked circle coordinates and driver `πd (offData c)`
(`zipLenMO_eq_zipRead`), which is what makes Sheffield's inverse argument (clause (2)) available.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **The length zipper of D87**: `Z^LEN_ℓ` re-welds the pieces (`zipLenUpOA`, D86, after `offConfig`)
for `ℓ ≥ 0`, and unzips the pieces (`zipLenDownMA`) for `ℓ < 0`. -/
def zipLenMO (γ ℓ : ℝ) : AreaConfig → AreaConfig :=
  if 0 ≤ ℓ then zipLenUpOA γ ℓ ∘ offConfig γ else zipLenDownMA γ (-ℓ)

/-- **Theorem 1.8, zipper stationarity, D87 form** (`theorem1_8_zipperStationarityPaperM` with
`zipLenMO`). -/
def theorem1_8_zipperStationarityPaperMO (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) : Prop :=
  (∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
    (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
    qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ ∧
    (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
      p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s) ∧
    ConfigEqOff (zipLenDownMA γ ℓ (zipLenMO γ ℓ (wedgeAConfig γ B Y ω))).toPair
      (wedgeAConfig γ B Y ω).toPair ∧
    ConfigEqOff (zipLenMO γ ℓ (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω))).toPair
      (wedgeAConfig γ B Y ω).toPair) ∧
  (∀ s t : ℝ, ∀ᵐ ω ∂P,
    ConfigEqOff (zipLenMO γ (s + t) (wedgeAConfig γ B Y ω)).toPair
      (zipLenMO γ s (zipLenMO γ t (wedgeAConfig γ B Y ω))).toPair) ∧
  (∀ t : ℝ, configLawOff (fun ω => (zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair) P =
    configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P)

/-- **Theorem 1.8** (Sheffield, arXiv:1012.4797, p. 26), D87 form: `theorem1_8PaperM` with the
zipper acting on the pieces for all times. -/
def theorem1_8PaperMO : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    IsBrownianReal B P → IsQuantumWedge γ (γ - 2 / γ) Y P → IndepFun (pathOf B) Y P →
    theorem1_8_decomposition γ P B Y ∧ theorem1_8_lengthsAgreePaper γ P B Y ∧
      theorem1_8_zipperStationarityPaperMO γ P B Y

/-- **Clause (2), D87 form.** -/
def G4GroupMOStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ s t : ℝ, ∀ᵐ ω ∂P,
      ConfigEqOff (zipLenMO γ (s + t) (wedgeAConfig γ B Y ω)).toPair
        (zipLenMO γ s (zipLenMO γ t (wedgeAConfig γ B Y ω))).toPair

theorem zipLenMO_of_nonneg {γ ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    zipLenMO γ ℓ = zipLenUpOA γ ℓ ∘ offConfig γ := by
  simp [zipLenMO, hℓ]

theorem zipLenMO_of_neg {γ ℓ : ℝ} (hℓ : ℓ < 0) : zipLenMO γ ℓ = zipLenDownMA γ (-ℓ) := by
  simp [zipLenMO, not_le.2 hℓ]

/-- The data with only the circle coordinates and the driver kept (pairings set to `0`). -/
def liftπ (e : (ℕ → ℝ) × (ℝ≥0 → ℝ)) : E6.FullData := ((e.1, fun _ => 0), e.2)

/-- The pieces read from the data depend only on the circle coordinates and the driver. -/
theorem configOfData_liftπ (γ : ℝ) (d : E6.FullData) :
    configOfData γ (liftπ (πd d)) = configOfData γ d := rfl

/-- The zipper on the pieces, as a function of the masked coordinates and driver. -/
def zipRead (γ ℓ : ℝ) (e : (ℕ → ℝ) × (ℝ≥0 → ℝ)) : AreaConfig :=
  (if 0 ≤ ℓ then zipLenUpOA γ ℓ else zipLenDownA γ (-ℓ)) (configOfData γ (liftπ e))

/-- **`Z^LEN_ℓ` of D87 reads only the pieces**: it is `zipRead` of the masked data. -/
theorem zipLenMO_eq_zipRead (γ ℓ : ℝ) (c : AreaConfig) :
    zipLenMO γ ℓ c = zipRead γ ℓ (πd (offData c.toPair)) := by
  unfold zipRead
  rw [configOfData_liftπ]
  by_cases hℓ : 0 ≤ ℓ
  · rw [zipLenMO_of_nonneg hℓ, if_pos hℓ]; rfl
  · rw [zipLenMO_of_neg (not_le.1 hℓ), if_neg hℓ]; rfl

end R18
end QuantumZipper
