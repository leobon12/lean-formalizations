import QuantumZipper.Statements.Thm11
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.GFF.ZeroRegBoundary

/-!
# Characteristic functions for Theorem 1.1 (tasks AS-2, AS-3)

* `zg_linear`: the zero-boundary GFF on `ℍ` is a.s. linear on admissible measures (derived from
  the Gaussian/covariance structure: the defect has second moment `0`).
* `charFun_lhs_fwd` (AS-2): characteristic function of `⟨𝔥₀ + h̃, ρ⟩` for `ρ : TestFun H`.
* `fieldLaw_eq_of_charFun` (AS-3): measurable, a.s. linear pairings with equal one-dimensional
  characteristic functions give equal `fieldLaw H`.
* `linear_lhs_fwd`: linearity of the left-hand field `ofFun (h0fwd κ) + X`.
-/

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace CharFunFwd

open CharFun

/-! ## Linearity of the zero-boundary GFF -/

theorem adm_smul {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (a : ℝ≥0) : IsAdmissibleH (a • μ) := by
  rw [ENNReal.smul_def]; exact isAdmissibleH_smul hμ ENNReal.coe_lt_top

theorem adm_comb {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) (a b : ℝ≥0) :
    IsAdmissibleH (a • μ + b • ν) :=
  isAdmissibleH_add (adm_smul hμ a) (adm_smul hν b)

theorem kernelCov_greenH_comb_left {μ ν ρ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (hρ : IsAdmissibleH ρ) (a b : ℝ≥0) :
    kernelCov greenH (a • μ + b • ν) ρ = a * kernelCov greenH μ ρ + b * kernelCov greenH ν ρ := by
  have := hρ.1
  have := (adm_smul hμ a).1
  have := (adm_smul hν b).1
  have h1 := (integrable_greenH_prod (adm_smul hμ a) hρ).integral_prod_left
  have h2 := (integrable_greenH_prod (adm_smul hν b) hρ).integral_prod_left
  unfold kernelCov
  rw [integral_add_measure h1 h2, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]

theorem kernelCov_greenH_comb_right {μ ν ρ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (hρ : IsAdmissibleH ρ) (a b : ℝ≥0) :
    kernelCov greenH ρ (a • μ + b • ν) = a * kernelCov greenH ρ μ + b * kernelCov greenH ρ ν := by
  rw [ZeroReg.kernelCov_greenH_symm hρ (adm_comb hμ hν a b),
    kernelCov_greenH_comb_left hμ hν hρ, ZeroReg.kernelCov_greenH_symm hμ hρ,
    ZeroReg.kernelCov_greenH_symm hν hρ]

/-- **Linearity of the zero-boundary GFF** on admissible measures, almost surely. -/
theorem zg_linear {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    (hX : IsZeroBoundaryGFFH X P) {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (a b : ℝ≥0) :
    (fun ω => X ω (a • μ + b • ν)) =ᵐ[P] fun ω => (a : ℝ) * X ω μ + (b : ℝ) * X ω ν := by
  have hw := adm_comb hμ hν a b
  set w := a • μ + b • ν with hw_def
  have hA := ZeroReg.zg_memLp hX hw
  have hB := ZeroReg.zg_memLp hX hμ
  have hC := ZeroReg.zg_memLp hX hν
  have iAA := hA.integrable_mul hA
  have iAB := hA.integrable_mul hB
  have iAC := hA.integrable_mul hC
  have iBB := hB.integrable_mul hB
  have iBC := hB.integrable_mul hC
  have iCC := hC.integrable_mul hC
  set A : Ω → ℝ := fun ω => X ω w
  set B : Ω → ℝ := fun ω => X ω μ
  set C : Ω → ℝ := fun ω => X ω ν
  have j1 : Integrable (fun ω => (A * A) ω - 2 * a * (A * B) ω) P :=
    iAA.sub (iAB.const_mul (2 * a))
  have j2 : Integrable (fun ω => (A * A) ω - 2 * a * (A * B) ω - 2 * b * (A * C) ω) P :=
    j1.sub (iAC.const_mul (2 * b))
  have j3 : Integrable (fun ω => (A * A) ω - 2 * a * (A * B) ω - 2 * b * (A * C) ω +
      (a : ℝ) ^ 2 * (B * B) ω) P := j2.add (iBB.const_mul ((a : ℝ) ^ 2))
  have j4 : Integrable (fun ω => (A * A) ω - 2 * a * (A * B) ω - 2 * b * (A * C) ω +
      (a : ℝ) ^ 2 * (B * B) ω + 2 * a * b * (B * C) ω) P := j3.add (iBC.const_mul (2 * a * b))
  have j5 : Integrable (fun ω => (A * A) ω - 2 * a * (A * B) ω - 2 * b * (A * C) ω +
      (a : ℝ) ^ 2 * (B * B) ω + 2 * a * b * (B * C) ω + (b : ℝ) ^ 2 * (C * C) ω) P :=
    j4.add (iCC.const_mul ((b : ℝ) ^ 2))
  have hsq : (fun ω => (A ω - a * B ω - b * C ω) ^ 2) = fun ω =>
      (A * A) ω - 2 * a * (A * B) ω - 2 * b * (A * C) ω + (a : ℝ) ^ 2 * (B * B) ω +
        2 * a * b * (B * C) ω + (b : ℝ) ^ 2 * (C * C) ω := by
    funext ω; simp only [Pi.mul_apply]; ring
  have hint : Integrable (fun ω => (A ω - a * B ω - b * C ω) ^ 2) P := by
    rw [hsq]; exact j5
  have hzero : ∫ ω, (A ω - a * B ω - b * C ω) ^ 2 ∂P = 0 := by
    rw [hsq, integral_add j4 (iCC.const_mul _), integral_add j3 (iBC.const_mul _),
      integral_add j2 (iBB.const_mul _), integral_sub j1 (iAC.const_mul _),
      integral_sub iAA (iAB.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [Pi.mul_apply, A, B, C]
    rw [ZeroReg.zg_integral_mul hX hw hw, ZeroReg.zg_integral_mul hX hw hμ,
      ZeroReg.zg_integral_mul hX hw hν, ZeroReg.zg_integral_mul hX hμ hμ,
      ZeroReg.zg_integral_mul hX hμ hν, ZeroReg.zg_integral_mul hX hν hν]
    have e1 := kernelCov_greenH_comb_left hμ hν hw a b
    have e2 := kernelCov_greenH_comb_right hμ hν hμ a b
    have e3 := kernelCov_greenH_comb_right hμ hν hν a b
    have e4 := kernelCov_greenH_comb_left hμ hν hμ a b
    have e5 := kernelCov_greenH_comb_left hμ hν hν a b
    have e6 := ZeroReg.kernelCov_greenH_symm hν hμ
    rw [← hw_def] at e1 e2 e3 e4 e5
    rw [e1, e2, e3, e4, e5, e6]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 hzero
  filter_upwards [hae] with ω hω
  have : A ω - a * B ω - b * C ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hω
  simp only [A, B, C] at this
  linarith

/-! ## The Gaussian step for the zero-boundary GFF -/

theorem zg_integral_cexp_diff {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsZeroBoundaryGFFH X P) {μ ν : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    ∫ ω, cexp (I * ((X ω μ - X ω ν : ℝ) : ℂ)) ∂P =
      cexp (-(kernelCov2 greenH (μ, ν) (μ, ν) : ℂ) / 2) := by
  have := ZeroReg.isProbabilityMeasure_of_zeroGFF hX
  set Y : Ω → ℝ := fun ω => X ω μ - X ω ν with hY
  have hm : Measurable Y := (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hmap := ZeroRegBdry.zrb_map_sub_eq_gaussianReal hX hμ hν
  have hA := ZeroReg.zg_memLp hX hμ
  have hB := ZeroReg.zg_memLp hX hν
  have hcov : cov[Y, Y; P] = kernelCov2 greenH (μ, ν) (μ, ν) := by
    rw [hY, covariance_fun_sub_fun_sub hA hB hA hB, hX.covariance_eq _ _ hμ hμ,
      hX.covariance_eq _ _ hμ hν, hX.covariance_eq _ _ hν hμ, hX.covariance_eq _ _ hν hν]
    rfl
  have hvnn : 0 ≤ kernelCov2 greenH (μ, ν) (μ, ν) := by
    rw [← hcov, covariance_self hm.aemeasurable]; exact variance_nonneg _ _
  calc ∫ ω, cexp (I * ((X ω μ - X ω ν : ℝ) : ℂ)) ∂P = ∫ x, cexp (I * (x : ℂ)) ∂(P.map Y) := by
        rw [integral_map hm.aemeasurable (by fun_prop)]
    _ = charFun (P.map Y) 1 := by rw [charFun_apply_real]; simp [mul_comm]
    _ = _ := by
        rw [hmap, charFun_gaussianReal, Real.coe_toNNReal _ hvnn]
        congr 1
        push_cast
        ring

/-! ## The energy of a test function for `greenH` -/

theorem kernelCov_tdens_greenH {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hA : IsAdmissibleH (tdens a)) (hB : IsAdmissibleH (tdens b)) :
    Integrable (fun p : ℂ × ℂ => max (a p.1) 0 * max (b p.2) 0 * greenH p.1 p.2)
        (volume.prod volume) ∧
      kernelCov greenH (tdens a) (tdens b) =
        ∫ p, max (a p.1) 0 * max (b p.2) 0 * greenH p.1 p.2 ∂(volume.prod volume) := by
  have hma : Measurable fun z => ENNReal.ofReal (a z) := ENNReal.measurable_ofReal.comp ha
  have hmb : Measurable fun z => ENNReal.ofReal (b z) := ENNReal.measurable_ofReal.comp hb
  have hN := integrable_greenH_prod hA hB
  have hN2 := hN
  rw [tdens, tdens, prod_withDensity hma hmb] at hN2
  have hlt : ∀ᵐ p ∂(volume.prod volume : Measure (ℂ × ℂ)),
      ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2) < ⊤ :=
    ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hm2 : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2) :=
    (hma.comp measurable_fst).mul (hmb.comp measurable_snd)
  rw [integrable_withDensity_iff_integrable_smul' hm2 hlt] at hN2
  have heq : ∀ p : ℂ × ℂ, (ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2)).toReal •
      greenH p.1 p.2 = max (a p.1) 0 * max (b p.2) 0 * greenH p.1 p.2 := by
    intro p
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal', smul_eq_mul]
  refine ⟨hN2.congr (ae_of_all _ heq), ?_⟩
  calc kernelCov greenH (tdens a) (tdens b)
        = ∫ p, greenH p.1 p.2 ∂((tdens a).prod (tdens b)) := (integral_prod _ hN).symm
    _ = _ := by
          rw [tdens, tdens, prod_withDensity hma hmb,
            integral_withDensity_eq_integral_toReal_smul hm2 hlt]
          exact integral_congr_ae (ae_of_all _ heq)

theorem kernelCov2_tdens_greenH {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) :
    kernelCov2 greenH (tdens a, tdens fun z => -a z) (tdens a, tdens fun z => -a z) =
      ∫ x, ∫ y, a x * a y * greenH x y := by
  have hA := hd.admissible
  have hB := hd.neg.admissible
  obtain ⟨i1, e1⟩ := kernelCov_tdens_greenH hd.meas hd.meas hA hA
  obtain ⟨i2, e2⟩ := kernelCov_tdens_greenH hd.meas hd.neg.meas hA hB
  obtain ⟨i3, e3⟩ := kernelCov_tdens_greenH hd.neg.meas hd.meas hB hA
  obtain ⟨i4, e4⟩ := kernelCov_tdens_greenH hd.neg.meas hd.neg.meas hB hB
  have hpt : ∀ p : ℂ × ℂ, a p.1 * a p.2 * greenH p.1 p.2 =
      max (a p.1) 0 * max (a p.2) 0 * greenH p.1 p.2 -
      max (a p.1) 0 * max (-a p.2) 0 * greenH p.1 p.2 -
      max (-a p.1) 0 * max (a p.2) 0 * greenH p.1 p.2 +
      max (-a p.1) 0 * max (-a p.2) 0 * greenH p.1 p.2 := by
    intro p
    have h1 := max_sub_max_neg (a p.1)
    have h2 := max_sub_max_neg (a p.2)
    calc a p.1 * a p.2 * greenH p.1 p.2
        = (max (a p.1) 0 - max (-a p.1) 0) * (max (a p.2) 0 - max (-a p.2) 0) *
            greenH p.1 p.2 := by rw [h1, h2]
      _ = _ := by ring
  have hint : Integrable (fun p : ℂ × ℂ => a p.1 * a p.2 * greenH p.1 p.2)
      (volume.prod volume) :=
    (((i1.sub i2).sub i3).add i4).congr (ae_of_all _ fun p => (hpt p).symm)
  have i12 : Integrable (fun p : ℂ × ℂ =>
      max (a p.1) 0 * max (a p.2) 0 * greenH p.1 p.2 -
      max (a p.1) 0 * max (-a p.2) 0 * greenH p.1 p.2) (volume.prod volume) := i1.sub i2
  have i123 : Integrable (fun p : ℂ × ℂ =>
      max (a p.1) 0 * max (a p.2) 0 * greenH p.1 p.2 -
      max (a p.1) 0 * max (-a p.2) 0 * greenH p.1 p.2 -
      max (-a p.1) 0 * max (a p.2) 0 * greenH p.1 p.2) (volume.prod volume) := i12.sub i3
  have hprod : ∫ x, ∫ y, a x * a y * greenH x y =
      ∫ p, a p.1 * a p.2 * greenH p.1 p.2 ∂(volume.prod volume) :=
    (integral_prod _ hint).symm
  unfold kernelCov2
  simp only
  rw [e1, e2, e3, e4, hprod, integral_congr_ae (ae_of_all _ hpt), integral_add i123 i4,
    integral_sub i12 i3, integral_sub i1 i2]

/-! ## AS-2: the left-hand side -/

theorem continuousOn_h0fwd (κ : ℝ) : ContinuousOn (h0fwd κ) H := by
  unfold h0fwd
  refine continuousOn_const.mul fun z hz => (continuousAt_arg ?_).continuousWithinAt
  exact Or.inr (ne_of_gt (show 0 < z.im from hz))

/-- **AS-2.** The characteristic function of `⟨𝔥₀ + h̃, ρ⟩` for the forward coupling. -/
theorem charFun_lhs_fwd (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) (hX : IsZeroBoundaryGFFH X P) (ρ : TestFun H) :
    ∫ ω, cexp (I * (pairRaw (ofFun (h0fwd κ) + X ω) ρ.1 : ℂ)) ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) -
        ((∫ x, ∫ y, ρ.1 x * ρ.1 y * greenH x y : ℝ) : ℂ) / 2) := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  have hsplit : ∀ ω, pairRaw (ofFun (h0fwd κ) + X ω) ρ.1 =
      (∫ z, ρ.1 z * h0fwd κ z) + (X ω (tdens ρ.1) - X ω (tdens fun z => -ρ.1 z)) := by
    intro ω
    rw [← pairRaw_ofFun (continuousOn_h0fwd κ) ρ, pairRaw_eq_tdens, pairRaw_eq_tdens]
    simp only [Pi.add_apply]
    ring
  simp_rw [hsplit, ofReal_add, mul_add, Complex.exp_add]
  rw [integral_const_mul, zg_integral_cexp_diff hX hd.admissible hd.neg.admissible,
    kernelCov2_tdens_greenH hd, ← Complex.exp_add]
  congr 1
  ring

theorem measurable_pairRaw_lhs_fwd (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → FieldSample} {P : Measure Ω} (hX : IsZeroBoundaryGFFH X P) (ρ : TestFun H) :
    Measurable fun ω => pairRaw (ofFun (h0fwd κ) + X ω) ρ.1 := by
  have hm : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0fwd κ) + X ω) μ := fun μ => by
    simp only [Pi.add_apply]
    exact measurable_const.add (hX.measurable_coord μ)
  exact measurable_pairRaw_comp hm ρ.1

/-! ## Linearity of the pairings (test functions of any mass) -/

/-- A random field is (almost surely) linear in the test function `ρ : TestFun H`. -/
def LinearPairingH {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → FieldSample) (P : Measure Ω) :
    Prop :=
  ∀ (ρ₁ ρ₂ ρ₃ : TestFun H) (a : ℝ), (∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) →
    ∀ᵐ ω ∂P, pairRaw (Y ω) ρ₃.1 = a * pairRaw (Y ω) ρ₁.1 + pairRaw (Y ω) ρ₂.1

theorem ae_lin_core_zero {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    (hX : IsZeroBoundaryGFFH X P) {m3p m3m mu mv m2p m2m : Measure ℂ}
    (h3p : IsAdmissibleH m3p) (h3m : IsAdmissibleH m3m) (hmu : IsAdmissibleH mu)
    (hmv : IsAdmissibleH mv) (h2p : IsAdmissibleH m2p) (h2m : IsAdmissibleH m2m) (b : ℝ≥0)
    (hid : m3p + b • mv + m2m = m3m + b • mu + m2p) :
    ∀ᵐ ω ∂P, X ω m3p - X ω m3m = b * (X ω mu - X ω mv) + (X ω m2p - X ω m2m) := by
  have hN₁ : IsAdmissibleH (b • mv + (1 : ℝ≥0) • m2m) := adm_comb hmv h2m b 1
  have hN₂ : IsAdmissibleH (b • mu + (1 : ℝ≥0) • m2p) := adm_comb hmu h2p b 1
  have hM : (1 : ℝ≥0) • m3p + (1 : ℝ≥0) • (b • mv + (1 : ℝ≥0) • m2m) =
      (1 : ℝ≥0) • m3m + (1 : ℝ≥0) • (b • mu + (1 : ℝ≥0) • m2p) := by
    simp only [one_smul]
    rw [← add_assoc, ← add_assoc, hid]
  filter_upwards [zg_linear hX h3p hN₁ 1 1, zg_linear hX hmv h2m b 1,
    zg_linear hX h3m hN₂ 1 1, zg_linear hX hmu h2p b 1] with ω hA hB hC hD
  rw [hM] at hA
  push_cast at hA hB hC hD
  linear_combination -(hA - hC) - hB + hD

theorem ae_lin_zero {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    (hX : IsZeroBoundaryGFFH X P) (ρ₁ ρ₂ ρ₃ : TestFun H) (a : ℝ)
    (h : ∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) :
    ∀ᵐ ω ∂P, X ω ((tdens ρ₃.1).map id) - X ω ((tdens fun z => -ρ₃.1 z).map id) =
      a * (X ω ((tdens ρ₁.1).map id) - X ω ((tdens fun z => -ρ₁.1 z).map id)) +
      (X ω ((tdens ρ₂.1).map id) - X ω ((tdens fun z => -ρ₂.1 z).map id)) := by
  have hf := goodMap_id
  obtain ⟨M₁, δ₁, d₁⟩ := exists_dens ρ₁
  obtain ⟨M₂, δ₂, d₂⟩ := exists_dens ρ₂
  obtain ⟨M₃, δ₃, d₃⟩ := exists_dens ρ₃
  have hreal : ∀ z, max (ρ₃.1 z) 0 - max (-ρ₃.1 z) 0 -
      a * (max (ρ₁.1 z) 0 - max (-ρ₁.1 z) 0) - (max (ρ₂.1 z) 0 - max (-ρ₂.1 z) 0) = 0 := by
    intro z
    rw [max_sub_max_neg, max_sub_max_neg, max_sub_max_neg, h z]
    ring
  rcases le_total 0 a with ha | ha
  · have hb : ((a.toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha
    have hid := tdens_map_comb hf.meas a.toNNReal d₃.meas d₁.neg.meas d₂.meas d₁.meas
      (fun z => by rw [hb]; linear_combination hreal z)
    filter_upwards [ae_lin_core_zero hX (push_admissible hf d₃) (push_admissible hf d₃.neg)
      (push_admissible hf d₁) (push_admissible hf d₁.neg) (push_admissible hf d₂)
      (push_admissible hf d₂.neg) a.toNNReal hid] with ω hω
    rw [hω, hb]
  · have hb : (((-a).toNNReal : ℝ≥0) : ℝ) = -a := Real.coe_toNNReal (-a) (by linarith)
    have hid := tdens_map_comb hf.meas (-a).toNNReal d₃.meas d₁.meas d₂.meas d₁.neg.meas
      (fun z => by rw [hb]; linear_combination hreal z)
    filter_upwards [ae_lin_core_zero hX (push_admissible hf d₃) (push_admissible hf d₃.neg)
      (push_admissible hf d₁.neg) (push_admissible hf d₁) (push_admissible hf d₂)
      (push_admissible hf d₂.neg) (-a).toNNReal hid] with ω hω
    rw [hω, hb]
    ring

/-- **Linearity of the left-hand field** `𝔥₀ + h̃` of Theorem 1.1. -/
theorem linear_lhs_fwd (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsZeroBoundaryGFFH X P) :
    LinearPairingH (fun ω => ofFun (h0fwd κ) + X ω) P := by
  intro ρ₁ ρ₂ ρ₃ a h
  filter_upwards [ae_lin_zero hX ρ₁ ρ₂ ρ₃ a h] with ω hω
  simp only [Measure.map_id] at hω
  simp only [pairRaw_add, pairRaw_ofFun (continuousOn_h0fwd κ), pairRaw_eq_tdens (X ω)]
  rw [integral_lin (continuousOn_h0fwd κ) ρ₁ ρ₂ ρ₃ a h, hω]
  ring

/-! ## AS-3: characteristic functions determine `fieldLaw H` -/

/-- The test function `a ρ₁ + ρ₂`. -/
def tfCombH (a : ℝ) (ρ₁ ρ₂ : TestFun H) : TestFun H :=
  ⟨fun z => a * ρ₁.1 z + ρ₂.1 z, (contDiff_const.mul ρ₁.2.1).add ρ₂.2.1,
    (ρ₁.2.2.1.mul_left).add ρ₂.2.2.1, by
      have hs : Function.support (fun z => a * ρ₁.1 z + ρ₂.1 z) ⊆
          Function.support ρ₁.1 ∪ Function.support ρ₂.1 :=
        fun z hz => by
          by_contra hc
          simp only [mem_union, Function.mem_support, not_or, not_not] at hc
          simp [hc.1, hc.2] at hz
      exact (closure_mono hs).trans (by
        rw [closure_union]; exact union_subset ρ₁.2.2.2 ρ₂.2.2.2)⟩

/-- The zero test function. -/
def tfZeroH : TestFun H :=
  ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩

theorem exists_tf_sumH {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρs : ι → TestFun H) :
    ∃ ρ : TestFun H, ∀ z, ρ.1 z = ∑ i ∈ s, c i * (ρs i).1 z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨tfZeroH, fun z => by simp [tfZeroH]⟩
  | insert k s hk ih =>
    obtain ⟨ρ', hρ'⟩ := ih
    exact ⟨tfCombH (c k) (ρs k) ρ', fun z => by
      rw [Finset.sum_insert hk]; simp [tfCombH, hρ' z]⟩

theorem ae_pairRaw_sumH {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample} {P : Measure Ω}
    (hl : LinearPairingH Y P) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρs : ι → TestFun H) :
    ∀ ρ : TestFun H, (∀ z, ρ.1 z = ∑ i ∈ s, c i * (ρs i).1 z) →
      ∀ᵐ ω ∂P, pairRaw (Y ω) ρ.1 = ∑ i ∈ s, c i * pairRaw (Y ω) (ρs i).1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ρ hρ
    refine ae_of_all _ fun ω => ?_
    have h0 : ρ.1 = fun _ => 0 := funext fun z => by simpa using hρ z
    simp [pairRaw, h0]
  | insert k s hk ih =>
    intro ρ hρ
    obtain ⟨ρ', hρ'⟩ := exists_tf_sumH s c ρs
    have hlin := hl (ρs k) ρ' ρ (c k) (fun z => by rw [hρ z, Finset.sum_insert hk, hρ' z])
    filter_upwards [ih ρ' hρ', hlin] with ω h1 h2
    rw [Finset.sum_insert hk, h2, h1]

/-- **AS-3.** Two random fields with measurable, almost surely linear pairings whose pairings
with every test function have the same characteristic function have the same `fieldLaw H`
(Cramér–Wold). -/
theorem fieldLaw_eq_of_charFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y₁ Y₂ : Ω → FieldSample}
    (hm₁ : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y₁ ω) ρ.1)
    (hm₂ : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y₂ ω) ρ.1)
    (hl₁ : LinearPairingH Y₁ P) (hl₂ : LinearPairingH Y₂ P)
    (hc : ∀ ρ : TestFun H, ∫ ω, cexp (I * (pairRaw (Y₁ ω) ρ.1 : ℂ)) ∂P =
      ∫ ω, cexp (I * (pairRaw (Y₂ ω) ρ.1 : ℂ)) ∂P) :
    fieldLaw H Y₁ P = fieldLaw H Y₂ P := by
  classical
  unfold fieldLaw
  refine (map_eq_iff_forall_finset_map_restrict_eq
    (X := fun (ρ : TestFun H) ω => pairRaw (Y₁ ω) ρ.1)
    (Y := fun (ρ : TestFun H) ω => pairRaw (Y₂ ω) ρ.1)
    (measurable_pi_iff.2 hm₁).aemeasurable (measurable_pi_iff.2 hm₂).aemeasurable).2 ?_
  intro J
  have hF : ∀ {Y : Ω → FieldSample}, (∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y ω) ρ.1) →
      Measurable fun ω => J.restrict fun ρ : TestFun H => pairRaw (Y ω) ρ.1 := fun hm =>
    measurable_pi_iff.2 fun i => hm i.1
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  set c : J → ℝ := fun i => L fun j => if i = j then 1 else 0 with hc_def
  have hL : ∀ x : J → ℝ, L x = ∑ i, x i * c i := fun x => by
    rw [show L x = L.toLinearMap x from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [smul_eq_mul, hc_def]
    rfl
  obtain ⟨ρ, hρ⟩ := exists_tf_sumH (Finset.univ : Finset J) c fun i => i.1
  have key : ∀ {Y : Ω → FieldSample}, (∀ ρ : TestFun H, Measurable fun ω => pairRaw (Y ω) ρ.1) →
      LinearPairingH Y P →
      charFunDual (P.map fun ω => J.restrict fun ρ : TestFun H => pairRaw (Y ω) ρ.1) L =
        ∫ ω, cexp (I * (pairRaw (Y ω) ρ.1 : ℂ)) ∂P := by
    intro Y hm hl
    rw [charFunDual_apply, integral_map (hF hm).aemeasurable (by fun_prop)]
    refine integral_congr_ae ?_
    filter_upwards [ae_pairRaw_sumH hl Finset.univ c (fun i => i.1) ρ hρ] with ω hω
    rw [hL, hω, mul_comm I]
    congr 2
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finset.restrict, mul_comm]
  rw [key hm₁ hl₁, key hm₂ hl₂, hc ρ]

end CharFunFwd
end QuantumZipper
