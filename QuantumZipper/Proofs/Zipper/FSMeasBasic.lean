import QuantumZipper.Proofs.LQG.WedgeMeasurable
import QuantumZipper.Zipper.Maps

/-!
# FS-MEAS (D27): measurable versions of field-valued random variables

`FieldSample = Measure ℂ → ℝ` carries the product σ-algebra over *all* measures on `ℂ`,
including the non-s-finite ones. For a field-valued random variable built by a coordinate change
(e.g. `ω ↦ canonical γ (Z ω)`), the coordinates at s-finite measures are measurable functions of
countably many circle averages (`WedgeMeas.measurable_resc_apply`), but nothing controls the
coordinates at non-s-finite measures, so `AEMeasurable Y P` and `IndepFun Y V P` (as
`FieldSample`-valued statements) are in general unavailable.

Decision D27 (`DECISIONS.md`): keep every internal predicate (e.g. `Thm13Asm.IsPStarSample`) and
**replace the field by a measurable version** that agrees with it at every s-finite measure:
`sfTrunc x μ = x μ` if `μ` is s-finite and `0` otherwise. Everything the project reads from a
field is read at finite measures (folded circles, test densities, push-forwards thereof), so
`sfTrunc x` and `x` have the same `avgReg`, `evalReg`, `coordChange`, `coordsFull`, `pairRaw`,
`dataFull`, `unzipLengths` and `fieldLawFull` (§1). For canonical fields, `canonVer γ c` is the
measurable version built from the dyadic coordinates `c = coords x` (§2).

Own elementary arguments (bookkeeping of the product σ-algebra); no literature source applies.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace QuantumZipper
namespace FSMeas

open Factorization CoordsFull

/-! ## 1. The s-finite truncation -/

open Classical in
/-- The s-finite truncation of a field sample: unchanged at s-finite measures, `0` elsewhere. -/
def sfTrunc (x : FieldSample) : FieldSample := fun μ => if SFinite μ then x μ else 0

theorem sfTrunc_apply (x : FieldSample) (μ : Measure ℂ) [h : SFinite μ] :
    sfTrunc x μ = x μ := by
  simp only [sfTrunc, h, ↓reduceIte]

theorem avgReg_sfTrunc (x : FieldSample) : avgReg (sfTrunc x) = avgReg x := by
  funext k z
  simp only [avgReg, sfTrunc_apply]

theorem coordsFull_sfTrunc (x : FieldSample) : coordsFull (sfTrunc x) = coordsFull x := by
  funext i
  simp only [coordsFull, sfTrunc_apply]

theorem pairRaw_sfTrunc (x : FieldSample) (ρ : ℂ → ℝ) : pairRaw (sfTrunc x) ρ = pairRaw x ρ := by
  simp only [pairRaw, sfTrunc_apply]

/-- Fields that agree a.s. after truncation have the same `fieldLawFull`. -/
theorem fieldLawFull_congr_sfTrunc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y Y' : Ω → FieldSample} (h : ∀ᵐ ω ∂P, Y ω = sfTrunc (Y' ω)) (U : Set ℂ) :
    fieldLawFull U Y P = fieldLawFull U Y' P := by
  unfold fieldLawFull
  refine Measure.map_congr ?_
  filter_upwards [h] with ω hω
  simp only [hω, coordsFull_sfTrunc, pairRaw_sfTrunc]

/-- `IsQuantumWedge` only reads `fieldLawFull H`, hence is insensitive to the truncation. -/
theorem isQuantumWedge_congr_sfTrunc {γ α : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y Y' : Ω → FieldSample} (h : ∀ᵐ ω ∂P, Y ω = sfTrunc (Y' ω)) :
    IsQuantumWedge γ α Y P ↔ IsQuantumWedge γ α Y' P := by
  unfold IsQuantumWedge
  rw [fieldLawFull_congr_sfTrunc h H]

/-! ## 2. The measurable canonical version from coordinates -/

/-- The truncated rescaled reconstruction is a *measurable* `FieldSample`-valued function of
`(c, s)`: at s-finite `μ` by `WedgeMeas.measurable_resc_apply`, and constant elsewhere. -/
theorem measurable_sfTrunc_resc (Q : ℝ) :
    Measurable fun p : (ℕ → ℝ) × ℝ => sfTrunc (WedgeMeas.resc Q p) := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : SFinite μ
  · simp only [sfTrunc, h, ↓reduceIte]
    exact WedgeMeas.measurable_resc_apply Q μ
  · simp only [sfTrunc, h, ↓reduceIte]
    exact measurable_const

/-- The measurable version of `(canonical γ x, scaleParam γ x)` read from `c = coords x`. -/
def canonVer (γ : ℝ) (c : ℕ → ℝ) : FieldSample × ℝ :=
  (sfTrunc (WedgeMeas.resc (Qc γ) (c, WedgeMeas.scaleG γ c)), WedgeMeas.scaleG γ c)

theorem measurable_canonVer (γ : ℝ) : Measurable (canonVer γ) :=
  ((measurable_sfTrunc_resc (Qc γ)).comp
    (measurable_id.prodMk (WedgeMeas.measurable_scaleG γ))).prodMk
    (WedgeMeas.measurable_scaleG γ)

/-- On good samples, `canonVer` of the coordinates is the truncated canonical field and its
scale. -/
theorem canonVer_coords {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    canonVer γ (coords x) = (sfTrunc (canonical γ x), scaleParam γ x) := by
  simp only [canonVer, WedgeMeas.scaleG_coords hx, WedgeMeas.canonical_eq_resc]

/-- **Replace by the measurable version (general form).** If `c` is an a.e.-measurable version
of the coordinates of a field `W` that is a.s. good, then `canonVer γ ∘ c` is a.e.-measurable, it
is a.s. `(sfTrunc (canonical γ W), scaleParam γ W)`, and it inherits every independence of `c`. -/
theorem canonVer_spec {γ : ℝ} {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {W : Ω → FieldSample} {c : Ω → ℕ → ℝ} {V : Ω → β}
    (hc : AEMeasurable c P) (hcW : ∀ᵐ ω ∂P, c ω = coords (W ω))
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (W ω)) (hI : IndepFun c V P) :
    AEMeasurable (fun ω => canonVer γ (c ω)) P ∧
      IndepFun (fun ω => canonVer γ (c ω)) V P ∧
      ∀ᵐ ω ∂P, canonVer γ (c ω) = (sfTrunc (canonical γ (W ω)), scaleParam γ (W ω)) := by
  refine ⟨(measurable_canonVer γ).comp_aemeasurable hc,
    hI.comp (measurable_canonVer γ) measurable_id, ?_⟩
  filter_upwards [hcW, hg] with ω h1 h2
  rw [h1, canonVer_coords h2]

end FSMeas
end QuantumZipper
