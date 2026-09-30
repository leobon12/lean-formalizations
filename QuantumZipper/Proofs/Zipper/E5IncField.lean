import QuantumZipper.Proofs.Zipper.E4Meas
import QuantumZipper.Proofs.Zipper.E5LocC
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# E5-INC, part 1: the regular version of the collision free field (decision D28)

Task D28 (Theorem 1.3, node E5). The collision constant `X'(ρ₀) − X'(ϖ_τ)` reads the free field
`X'` at the **random** measure `ϖ_τ = varpiT V τ ϖ`. For an arbitrary free field this raw value
need not be measurable. Decision D28 (`DECISIONS.md`): E5 uses a *regular version* of `X'`,

  `regField ϖ ρ₀ x ν = x ρ₀ + regRead ρ₀ x ν − [ρ₀ ∈ fam] · regRead ρ₀ x ρ₀`   for `ν ∈ fam`,
  `regField ϖ ρ₀ x ν = x ν`                                                  otherwise,

where `fam = varpiFam ϖ` is the family of probability measures `varpiT V t ϖ` (continuous `V`,
`t ≥ 0`), and `regRead ρ₀ x ν = evalReg (halfShift ρ₀ x) ν` is the
regularized (circle-average) value of the field `ν ↦ (x(2ν) − ν(ℂ)·x(2ρ₀))/2`. The halved,
doubled reading only looks at measures of mass `2`, which are never in `fam`, so `regField` agrees
with `x` at every measure the reading uses.

* `isFreeGFFModConstH_of_ae_shift`: a field equal a.s., at each admissible `ν`, to
  `X ν + ν(ℂ)·c` is again a free field (modulo constants).
* `isFreeGFFModConstH_halfShift`, `isFreeGFFModConstH_regField`: the halved field and the regular
  version are free fields; `ae_regField_eq`: at every fixed measure, `regField (X ω) ν = X ω ν`
  a.s. (RC1 at `ϖ_t`, `E4Meas.ae_evalReg_varpiT`, i.e. `FrostmanReg`).

Sources: RC1 is the repository's `FrostmanReg.ae_tendsto_integral_avgReg_frostman`; the rest is
own elementary bookkeeping (modification of a process; no published source needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1

/-! ## 1. Modifications of a free field -/

theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f f' g g' : Ω → ℝ}
    (hf : f =ᵐ[P] f') (hg : g =ᵐ[P] g') : cov[f, g; P] = cov[f', g'; P] := by
  unfold covariance
  rw [integral_congr_ae hf, integral_congr_ae hg]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with ω h1 h2
  rw [h1, h2]

theorem nnreal_smul_measure_eq (a : ℝ≥0) (μ : Measure ℂ) : a • μ = (a : ℝ≥0∞) • μ := by
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

/-- **A mass-proportional random shift of a free field is a free field.** If at every admissible
`ν`, a.s. `Y ν = X ν + ν(ℂ)·c`, and `Y` has measurable coordinates, then `Y` is a free field
modulo constants (the balanced increments of `Y` and `X` agree a.s.). -/
theorem isFreeGFFModConstH_of_ae_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (c : Ω → ℝ)
    (hYm : ∀ μ, Measurable fun ω => Y ω μ)
    (hY : ∀ μ, IsAdmissibleH μ → (fun ω => Y ω μ) =ᵐ[P] fun ω => X ω μ + (μ univ).toReal * c ω) :
    IsFreeGFFModConstH Y P := by
  have hinc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH ν → μ univ = ν univ →
      (fun ω => Y ω μ - Y ω ν) =ᵐ[P] fun ω => X ω μ - X ω ν := by
    intro μ ν hμ hν hm
    filter_upwards [hY μ hμ, hY ν hν] with ω h1 h2
    rw [h1, h2, hm]; ring
  refine ⟨hYm, hX.gaussian.congr fun p => (hinc _ _ p.2.1 p.2.2.1 p.2.2.2).symm, ?_, ?_, ?_⟩
  · intro μ ν hμ hν hm
    rw [integral_congr_ae (hinc μ ν hμ hν hm)]
    exact hX.centered μ ν hμ hν hm
  · intro p q hp1 hp2 hp hq1 hq2 hq
    rw [covariance_congr_ae (hinc _ _ hp1 hp2 hp) (hinc _ _ hq1 hq2 hq)]
    exact hX.covariance_eq p q hp1 hp2 hp hq1 hq2 hq
  · intro μ ν hμ hν a b
    have hμf := hμ.1
    have hνf := hν.1
    have hab : IsAdmissibleH (a • μ + b • ν) := by
      refine isAdmissibleH_add ?_ ?_
      · rw [nnreal_smul_measure_eq]
        exact isAdmissibleH_smul hμ ENNReal.coe_lt_top
      · rw [nnreal_smul_measure_eq]
        exact isAdmissibleH_smul hν ENNReal.coe_lt_top
    have hmass : ((a • μ + b • ν) univ).toReal =
        (a : ℝ) * (μ univ).toReal + (b : ℝ) * (ν univ).toReal := by
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
        ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
        ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top μ univ))
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top ν univ)),
        ENNReal.toReal_mul, ENNReal.toReal_mul]
      simp
    filter_upwards [hY _ hab, hY μ hμ, hY ν hν, hX.linear μ ν hμ hν a b] with ω h h1 h2 h3
    rw [h, h1, h2, h3, hmass]; ring

/-! ## 2. The halved field read at mass-2 measures -/

/-- The halved field `ν ↦ (x(2ν) − ν(ℂ)·x(2ρ₀))/2`. It reads `x` only at `2ν` and `2ρ₀`. -/
def halfShift (ρ₀ : Measure ℂ) (x : FieldSample) : FieldSample := fun ν =>
  (x ((2 : ℝ≥0) • ν) - (ν univ).toReal * x ((2 : ℝ≥0) • ρ₀)) / 2

theorem measurable_halfShift_coord {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    (hXm : ∀ μ, Measurable fun ω => X ω μ) (ρ₀ ν : Measure ℂ) :
    Measurable fun ω => halfShift ρ₀ (X ω) ν :=
  (((hXm _).sub (measurable_const.mul (hXm _))).div_const 2)

theorem ae_two_smul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    (fun ω => X ω ((2 : ℝ≥0) • μ)) =ᵐ[P] fun ω => 2 * X ω μ := by
  filter_upwards [hX.linear μ μ hμ hμ 2 0] with ω h
  simpa using h

/-- At each admissible `ν`, a.s. `halfShift ρ₀ (X ω) ν = X ω ν − ν(ℂ)·X ω ρ₀`. -/
theorem ae_halfShift_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {ρ₀ : Measure ℂ} (hρ₀ : IsAdmissibleH ρ₀) {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) :
    (fun ω => halfShift ρ₀ (X ω) ν) =ᵐ[P] fun ω => X ω ν + (ν univ).toReal * (-X ω ρ₀) := by
  filter_upwards [ae_two_smul hX hν, ae_two_smul hX hρ₀] with ω h1 h2
  simp only [halfShift, h1, h2]; ring

theorem isFreeGFFModConstH_halfShift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {ρ₀ : Measure ℂ}
    (hρ₀ : IsAdmissibleH ρ₀) : IsFreeGFFModConstH (fun ω => halfShift ρ₀ (X ω)) P :=
  isFreeGFFModConstH_of_ae_shift hX (fun ω => -X ω ρ₀)
    (measurable_halfShift_coord hX.measurable_coord ρ₀) fun _ hν => ae_halfShift_eq hX hρ₀ hν

/-! ## 3. The regular version -/

/-- The family where the regular reading replaces the raw value: the probability measures of the
form `varpiT V t ϖ` (continuous `V`, `t ≥ 0`). -/
def varpiFam (ϖ : Measure ℂ) : Set (Measure ℂ) :=
  {μ | μ univ = 1 ∧ ∃ V : ℝ → ℝ, Continuous V ∧ ∃ t : ℝ, 0 ≤ t ∧ μ = varpiT V t ϖ}

/-- The regular reading of `x` at `ν`: `evalReg` of the halved field. -/
def regRead (ρ₀ : Measure ℂ) (x : FieldSample) (ν : Measure ℂ) : ℝ :=
  evalReg (halfShift ρ₀ x) ν

open Classical in
/-- **The regular version of a field** (decision D28): the raw value is replaced by the regular
reading on `varpiFam ϖ`, normalized so that the value at `ρ₀` is unchanged. -/
def regField (ϖ ρ₀ : Measure ℂ) (x : FieldSample) : FieldSample := fun ν =>
  if ν ∈ varpiFam ϖ then
    x ρ₀ + regRead ρ₀ x ν - (if ρ₀ ∈ varpiFam ϖ then regRead ρ₀ x ρ₀ else 0)
  else x ν

theorem regField_of_not_mem {ϖ ρ₀ : Measure ℂ} (x : FieldSample) {ν : Measure ℂ}
    (h : ν ∉ varpiFam ϖ) : regField ϖ ρ₀ x ν = x ν := by
  simp [regField, h]

open Classical in
theorem regField_of_mem {ϖ ρ₀ : Measure ℂ} (x : FieldSample) {ν : Measure ℂ}
    (h : ν ∈ varpiFam ϖ) : regField ϖ ρ₀ x ν =
      x ρ₀ + regRead ρ₀ x ν - (if ρ₀ ∈ varpiFam ϖ then regRead ρ₀ x ρ₀ else 0) := by
  simp [regField, h]

/-- The value at `ρ₀` is unchanged. -/
theorem regField_rho {ϖ ρ₀ : Measure ℂ} (x : FieldSample) :
    regField ϖ ρ₀ x ρ₀ = x ρ₀ := by
  by_cases h : ρ₀ ∈ varpiFam ϖ
  · rw [regField_of_mem x h]; simp only [h, ite_true]; ring
  · exact regField_of_not_mem x h

/-- Measures of mass `≠ 1` are outside the family, so `regField` keeps their raw value. -/
theorem regField_of_mass_ne {ϖ ρ₀ : Measure ℂ} (x : FieldSample) {ν : Measure ℂ}
    (h : ν univ ≠ 1) : regField ϖ ρ₀ x ν = x ν :=
  regField_of_not_mem x fun hν => h hν.1

/-- `regField` does not change the halved reading at probability measures. -/
theorem halfShift_regField {ϖ ρ₀ : Measure ℂ} (hρ₀ : ρ₀ univ = 1) (x : FieldSample)
    {ν : Measure ℂ} (hν : ν univ = 1) :
    halfShift ρ₀ (regField ϖ ρ₀ x) ν = halfShift ρ₀ x ν := by
  have h2 : ∀ μ : Measure ℂ, μ univ = 1 → ((2 : ℝ≥0) • μ) univ ≠ 1 := fun μ hμ => by
    rw [Measure.smul_apply, hμ, ENNReal.smul_def, smul_eq_mul, mul_one]
    norm_num
  simp only [halfShift, regField_of_mass_ne x (h2 ν hν), regField_of_mass_ne x (h2 ρ₀ hρ₀)]

theorem measurable_regField_coord {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    (hXm : ∀ μ, Measurable fun ω => X ω μ) (ϖ ρ₀ : Measure ℂ) (ν : Measure ℂ) :
    Measurable fun ω => regField ϖ ρ₀ (X ω) ν := by
  have hH : Measurable fun ω => halfShift ρ₀ (X ω) :=
    measurable_pi_iff.2 fun μ => measurable_halfShift_coord hXm ρ₀ μ
  have hR : ∀ μ : Measure ℂ, μ ∈ varpiFam ϖ → Measurable fun ω => regRead ρ₀ (X ω) μ := by
    intro μ hμ
    have : IsFiniteMeasure μ := ⟨by rw [hμ.1]; exact ENNReal.one_lt_top⟩
    exact (measurable_evalReg μ).comp hH
  by_cases h : ν ∈ varpiFam ϖ
  · simp only [regField_of_mem _ h]
    refine ((hXm ρ₀).add (hR ν h)).sub ?_
    by_cases h0 : ρ₀ ∈ varpiFam ϖ
    · simp only [h0, ite_true]; exact hR ρ₀ h0
    · simp only [h0, ite_false]; exact measurable_const
  · simp only [regField_of_not_mem _ h]; exact hXm ν

/-- **Faithfulness**: at every fixed measure, a.s. `regField (X ω) ν = X ω ν`. -/
theorem ae_regField_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {ϖ ρ₀ : Measure ℂ} (hϖ : IsNormalizer ϖ)
    (hρ₀ : IsAdmissibleH ρ₀) (ν : Measure ℂ) :
    (fun ω => regField ϖ ρ₀ (X ω) ν) =ᵐ[P] fun ω => X ω ν := by
  have hH := isFreeGFFModConstH_halfShift hX hρ₀
  -- RC1 at every member of the family
  have hrc : ∀ μ ∈ varpiFam ϖ, ∀ᵐ ω ∂P, regRead ρ₀ (X ω) μ = X ω μ - X ω ρ₀ := by
    rintro μ ⟨h1, V, hV, t, ht, rfl⟩
    have hadm : IsAdmissibleH (varpiT V t ϖ) := isAdmissibleH_varpiT hϖ hV ht
    filter_upwards [E4Meas.ae_evalReg_varpiT ht hH hϖ hV, ae_halfShift_eq hX hρ₀ hadm] with ω h h'
    rw [regRead, h, h', h1]; simp; ring
  by_cases h : ν ∈ varpiFam ϖ
  · simp only [regField_of_mem _ h]
    by_cases h0 : ρ₀ ∈ varpiFam ϖ
    · filter_upwards [hrc ν h, hrc ρ₀ h0] with ω h1 h2
      simp only [h0, ite_true, h1, h2]; ring
    · filter_upwards [hrc ν h] with ω h1
      simp only [h0, ite_false, h1]; ring
  · exact Eventually.of_forall fun ω => regField_of_not_mem _ h

/-- **The regular version is a free field.** -/
theorem isFreeGFFModConstH_regField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {ϖ ρ₀ : Measure ℂ} (hϖ : IsNormalizer ϖ) (hρ₀ : IsAdmissibleH ρ₀) :
    IsFreeGFFModConstH (fun ω => regField ϖ ρ₀ (X ω)) P :=
  isFreeGFFModConstH_of_ae_shift hX 0 (measurable_regField_coord hX.measurable_coord ϖ ρ₀)
    fun ν _ => (ae_regField_eq hX hϖ hρ₀ ν).mono fun ω h => by simp [h]

end E5
end QuantumZipper
