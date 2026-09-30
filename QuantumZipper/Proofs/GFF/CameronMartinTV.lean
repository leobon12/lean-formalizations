import QuantumZipper.Proofs.GFF.K3.HarmonicPart
import QuantumZipper.Proofs.GFF.K3.CondCM

/-!
# Cameron–Martin total-variation bound for the free field (task CM-TV, part 1)

For a free field `X` (`IsFreeGFFModConstH X P`) and a deterministic shift `φ : ℂ → ℝ` which is
`C²`, compactly supported and even across `ℝ` (`φ ∘ conj = φ`: Neumann boundary behaviour; for
example a cut-off of a function harmonic in the reflected sense), the law of the **balanced
increments** `incr x (μ, ν) = x μ − x ν` of `X + ofFun φ` is TV-close to that of `X`:

`|E F(incr (X + ofFun φ)) − E F(incr X)| ≤ √(exp E_H(φ) − 1)` for measurable `|F| ≤ 1`
(`abs_integral_incr_shift_sub_le`), where `E_H(φ) = dirichletEnergyOn H φ = (2π)⁻¹∫_H |∇φ|²` is
the paper's Dirichlet energy; `√(exp E − 1) ≤ 2 √E` for `E ≤ 1` (`sqrt_exp_sub_one_le`), so the
bound is `≤ 2 ‖φ‖_∇`.

## Proof (Cameron–Martin with a single Gaussian coordinate)

Put `ρ = (2π)⁻¹(−Δφ)` and let `μ₀, ν₀` be the positive and negative parts of `ρ(z) dz` on `Hbar`
(`cmPos φ`, `cmNeg φ`). They are admissible (bounded compactly supported densities) and balanced
(`∫ Δφ = 0`), so `j₀ = (μ₀, ν₀)` is an index of the increment process. By the Green
representation for the Neumann kernel (`K3.integral_neumannH_mul_neg_laplacian`,
`∫ neumannH(x,·)(−Δφ) = 2π(φ x + φ x̄)`) and evenness, `∫ neumannH(x,·) d(μ₀ − ν₀) = φ x` for all
`x` (`integral_neumannH_cmPos_sub`), hence (Fubini)
`Cov(incr X j, incr X j₀) = ∫ φ dμ − ∫ φ dν` for every balanced admissible `j = (μ, ν)`
(`kernelCov2_cm`): the shift `incr (ofFun φ)` is the Cameron–Martin shift `K(·, δ_{j₀})`, and
`K(j₀, j₀) = ∫ φ ρ = (2π)⁻¹ ∫_H φ(−Δφ) = E_H(φ)` (Green's first identity,
`K3.setIntegral_H_mul_neg_laplacian`). The bound is then the finite-dimensional Cameron–Martin
estimate `K3.abs_integral_shift_sub_le` (`E|D − 1| ≤ (E(D−1)²)^{1/2} = (e^{K(σ,σ)} − 1)^{1/2}`)
for `σ = δ_{j₀}`. No approximation argument is needed: the Cameron–Martin direction is itself a
coordinate of the increment process.

Sources: Cameron–Martin theorem (Bogachev, *Gaussian Measures*, Thm 2.4.5, Cor. 2.4.3; Janson,
*Gaussian Hilbert Spaces*, Thm 14.1); for the GFF: Berestycki–Powell, *Gaussian free field and
Liouville quantum gravity*, arXiv:2004.04720, Lemma 3.12 (Cameron–Martin for the GFF, shift by a
finite-energy function) and Lemma 3.14 (TV bound by the Dirichlet energy), p. 79. The
identification of the shift through the Green representation is the argument of B–P Lemma 3.12
(`h = G(ρ)` with `ρ = −Δh/(2π)`), written for the Neumann kernel on `ℍ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Laplacian
open scoped Real ENNReal ComplexConjugate

namespace QuantumZipper
namespace CMTV

/-! ## The Cameron–Martin measures of a shift -/

/-- The signed density `(2π)⁻¹(−Δφ)`. -/
def cmDens (φ : ℂ → ℝ) (z : ℂ) : ℝ := (2 * π)⁻¹ * (-Δ φ z)

/-- Positive part of `cmDens φ (z) dz` on `Hbar`. -/
def cmPos (φ : ℂ → ℝ) : Measure ℂ :=
  (volume.restrict Hbar).withDensity fun z => ENNReal.ofReal (cmDens φ z)

/-- Negative part of `cmDens φ (z) dz` on `Hbar`. -/
def cmNeg (φ : ℂ → ℝ) : Measure ℂ :=
  (volume.restrict Hbar).withDensity fun z => ENNReal.ofReal (-cmDens φ z)

/-- The balanced increments `(μ, ν) ↦ x μ − x ν` of a field sample. -/
def incr (x : FieldSample) : K3.BalIdx → ℝ := fun j => x j.1.1 - x j.1.2

theorem incr_add_ofFun (x : FieldSample) (φ : ℂ → ℝ) (j : K3.BalIdx) :
    incr (x + ofFun φ) j = incr x j + (∫ z, φ z ∂j.1.1 - ∫ z, φ z ∂j.1.2) := by
  simp only [incr, Pi.add_apply, ofFun]; ring

section Dens

variable {φ : ℂ → ℝ}

theorem measurableSet_Hbar_cm : MeasurableSet Hbar := isClosed_Hbar.measurableSet

theorem continuous_cmDens (hφ : ContDiff ℝ 2 φ) : Continuous (cmDens φ) :=
  continuous_const.mul (K3.continuous_laplacian_K3 hφ).neg

theorem cmDens_eq_zero {z : ℂ} (hz : z ∉ tsupport φ) : cmDens φ z = 0 := by
  simp [cmDens, K3.laplacian_eq_zero_of_notMem_tsupport hz]

/-- `∫ f dμ₀ − ∫ f dν₀ = ∫_Hbar f ρ` (for measurable `f` with `f ρ` integrable). -/
theorem integral_cmPos_sub_cmNeg {f : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hfm : Measurable f)
    (hf : Integrable fun z => f z * cmDens φ z) :
    ∫ z, f z ∂cmPos φ - ∫ z, f z ∂cmNeg φ = ∫ z in Hbar, f z * cmDens φ z := by
  have hm := (continuous_cmDens hφ).measurable
  have hmn : Measurable fun z => -cmDens φ z := hm.neg
  have e1 : ∫ z, f z ∂cmPos φ = ∫ z in Hbar, f z * ((cmDens φ z).toNNReal : ℝ) := by
    change ∫ z, f z ∂((volume.restrict Hbar).withDensity
      fun z => ((cmDens φ z).toNNReal : ℝ≥0∞)) = _
    rw [integral_withDensity_eq_integral_smul hm.real_toNNReal]
    simp only [NNReal.smul_def, smul_eq_mul, mul_comm]
  have e2 : ∫ z, f z ∂cmNeg φ = ∫ z in Hbar, f z * ((-cmDens φ z).toNNReal : ℝ) := by
    change ∫ z, f z ∂((volume.restrict Hbar).withDensity
      fun z => ((-cmDens φ z).toNNReal : ℝ≥0∞)) = _
    rw [integral_withDensity_eq_integral_smul hmn.real_toNNReal]
    simp only [NNReal.smul_def, smul_eq_mul, mul_comm]
  have hi1 : Integrable (fun z => f z * ((cmDens φ z).toNNReal : ℝ)) (volume.restrict Hbar) := by
    refine (hf.norm.integrableOn (s := Hbar)).mono'
      (hfm.mul (measurable_coe_nnreal_real.comp hm.real_toNNReal)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_mul, norm_mul, Real.coe_toNNReal']
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hi2 : Integrable (fun z => f z * ((-cmDens φ z).toNNReal : ℝ)) (volume.restrict Hbar) := by
    refine (hf.norm.integrableOn (s := Hbar)).mono'
      (hfm.mul (measurable_coe_nnreal_real.comp hmn.real_toNNReal)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_mul, norm_mul, Real.coe_toNNReal']
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  rw [e1, e2, ← integral_sub hi1 hi2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Real.coe_toNNReal']
  rw [← mul_sub, max_zero_sub_eq_self]

/-- For an even integrable `g`, `∫_Hbar g = ½ ∫_ℂ g`. -/
theorem setIntegral_Hbar_eq_half {g : ℂ → ℝ} (hg : Integrable g)
    (heven : ∀ z, g (conj z) = g z) : ∫ z in Hbar, g z = (1 / 2) * ∫ z, g z := by
  rw [setIntegral_congr_set K3.Hbar_ae_eq_H, K3.integral_eq_two_mul_setIntegral_H hg heven]
  ring

theorem cmDens_conj (hφ : ContDiff ℝ 2 φ) (heven : ∀ z, φ (conj z) = φ z) (z : ℂ) :
    cmDens φ (conj z) = cmDens φ z := by
  simp only [cmDens, K3.laplacian_conj_eq hφ heven z]

theorem neumannH_conj_right_cm (x y : ℂ) : neumannH x (conj y) = neumannH x y := by
  unfold neumannH; rw [Complex.conj_conj]; ring

theorem measurable_neumannH_right_cm (x : ℂ) : Measurable fun y => neumannH x y :=
  measurable_neumannH.comp (measurable_const.prodMk measurable_id)

/-- **Green representation**: `∫ neumannH(x,·) d(μ₀ − ν₀) = φ x` for every `x`. -/
theorem integral_neumannH_cmPos_sub (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) (x : ℂ) :
    ∫ y, neumannH x y ∂cmPos φ - ∫ y, neumannH x y ∂cmNeg φ = φ x := by
  have hi0 := K3.integrable_neumannH_mul (K3.continuous_laplacian_K3 hφ).neg
    (K3.hasCompactSupport_laplacian_K3 hc).neg x
  have hi : Integrable fun y => neumannH x y * cmDens φ y :=
    (hi0.const_mul (2 * π)⁻¹).congr (ae_of_all _ fun y => by simp only [cmDens, Pi.neg_apply]; ring)
  rw [integral_cmPos_sub_cmNeg hφ (measurable_neumannH_right_cm x) hi,
    setIntegral_Hbar_eq_half hi fun y => by
      rw [neumannH_conj_right_cm, cmDens_conj hφ heven]]
  have e : ∫ y, neumannH x y * cmDens φ y = (2 * π)⁻¹ * ∫ y, neumannH x y * (-Δ φ y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [cmDens]; ring
  rw [e, K3.integral_neumannH_mul_neg_laplacian hφ hc x, heven x]
  field_simp
  ring

theorem hasCompactSupport_cmDens (hc : HasCompactSupport φ) : HasCompactSupport (cmDens φ) :=
  hc.mono' fun z hz => by
    by_contra h
    exact hz (cmDens_eq_zero h)

/-- A bounded continuous density vanishing off a compact `K`, restricted to `Hbar`, is
admissible. -/
theorem isAdmissibleH_restrict_withDensity {d : ℂ → ℝ} (hd : Continuous d)
    (hdc : HasCompactSupport d) :
    IsAdmissibleH ((volume.restrict Hbar).withDensity fun z => ENNReal.ofReal (d z)) := by
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support hdc
  rw [← withDensity_indicator measurableSet_Hbar_cm]
  refine isAdmissibleH_withDensity (M := ENNReal.ofReal C)
    (hd.measurable.ennreal_ofReal.indicator measurableSet_Hbar_cm) ENNReal.ofReal_lt_top
    (fun x => ?_) ((show IsCompact (tsupport d) from hdc).inter_right isClosed_Hbar)
    inter_subset_right (fun x hx => ?_)
  · refine Set.indicator_apply_le' (fun _ => ?_) (fun _ => bot_le)
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using hC x))
  · by_cases hxH : x ∈ Hbar
    · rw [indicator_of_mem hxH]
      have hxs : x ∉ tsupport d := fun h => hx ⟨h, hxH⟩
      simp [image_eq_zero_of_notMem_tsupport hxs]
    · exact indicator_of_notMem hxH _

theorem isAdmissibleH_cmPos (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    IsAdmissibleH (cmPos φ) :=
  isAdmissibleH_restrict_withDensity (continuous_cmDens hφ) (hasCompactSupport_cmDens hc)

theorem isAdmissibleH_cmNeg (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    IsAdmissibleH (cmNeg φ) :=
  isAdmissibleH_restrict_withDensity (continuous_cmDens hφ).neg (hasCompactSupport_cmDens hc).neg

/-- `μ₀` and `ν₀` have the same mass (`∫ Δφ = 0`). -/
theorem cmPos_univ_eq (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) : cmPos φ univ = cmNeg φ univ := by
  have := (isAdmissibleH_cmPos hφ hc).1
  have := (isAdmissibleH_cmNeg hφ hc).1
  have hi : Integrable fun z => (fun _ => (1 : ℝ)) z * cmDens φ z := by
    simp only [one_mul]
    exact (continuous_cmDens hφ).integrable_of_hasCompactSupport (hasCompactSupport_cmDens hc)
  have h := integral_cmPos_sub_cmNeg hφ measurable_const hi
  rw [setIntegral_Hbar_eq_half hi fun z => by simp only [cmDens_conj hφ heven]] at h
  have e : ∫ z, (fun _ => (1 : ℝ)) z * cmDens φ z = 0 := by
    simp only [one_mul, cmDens]
    rw [integral_const_mul, integral_neg, K3.integral_laplacian_eq_zero hφ hc]; simp
  rw [e, mul_zero, integral_const, integral_const, sub_eq_zero] at h
  simp only [smul_eq_mul, mul_one] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h

/-- The energy identity: `∫ φ dμ₀ − ∫ φ dν₀ = E_H(φ)`. -/
theorem integral_cm_self (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) :
    ∫ z, φ z ∂cmPos φ - ∫ z, φ z ∂cmNeg φ = dirichletEnergyOn H φ := by
  have hi : Integrable fun z => φ z * cmDens φ z :=
    (hφ.continuous.mul (continuous_cmDens hφ)).integrable_of_hasCompactSupport hc.mul_right
  rw [integral_cmPos_sub_cmNeg hφ hφ.continuous.measurable hi,
    setIntegral_congr_set K3.Hbar_ae_eq_H]
  have e : ∫ z in H, φ z * cmDens φ z = (2 * π)⁻¹ * ∫ z in H, φ z * (-Δ φ z) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [cmDens]; ring
  rw [e, K3.setIntegral_H_mul_neg_laplacian hφ hc heven]
  rfl

/-- `kernelCov neumannH μ μ₀ − kernelCov neumannH μ ν₀ = ∫ φ dμ` for admissible `μ`. -/
theorem kernelCov_cm_sub (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    kernelCov neumannH μ (cmPos φ) - kernelCov neumannH μ (cmNeg φ) = ∫ x, φ x ∂μ := by
  have := (isAdmissibleH_cmPos hφ hc).1
  have := (isAdmissibleH_cmNeg hφ hc).1
  unfold kernelCov
  have h1 : Integrable (fun x => ∫ y, neumannH x y ∂cmPos φ) μ :=
    (integrable_neumannH_prod hμ (isAdmissibleH_cmPos hφ hc)).integral_prod_left
  have h2 : Integrable (fun x => ∫ y, neumannH x y ∂cmNeg φ) μ :=
    (integrable_neumannH_prod hμ (isAdmissibleH_cmNeg hφ hc)).integral_prod_left
  rw [← integral_sub h1 h2]
  exact integral_congr_ae (ae_of_all _ fun x => integral_neumannH_cmPos_sub hφ hc heven x)

/-- **The shift is a Cameron–Martin direction**: `K((μ,ν), (μ₀,ν₀)) = ∫ φ dμ − ∫ φ dν`. -/
theorem kernelCov2_cm (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) (j : K3.BalIdx) :
    kernelCov2 neumannH j.1 (cmPos φ, cmNeg φ) = ∫ z, φ z ∂j.1.1 - ∫ z, φ z ∂j.1.2 := by
  unfold kernelCov2
  have a := kernelCov_cm_sub hφ hc heven j.2.1
  have b := kernelCov_cm_sub hφ hc heven j.2.2.1
  simp only at a b ⊢
  linarith

/-- The Cameron–Martin index `(μ₀, ν₀)` of the shift `φ`. -/
def cmIdx (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z) :
    K3.BalIdx :=
  ⟨(cmPos φ, cmNeg φ), isAdmissibleH_cmPos hφ hc, isAdmissibleH_cmNeg hφ hc,
    cmPos_univ_eq hφ hc heven⟩

end Dens

/-! ## The total-variation bound -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {φ : ℂ → ℝ}

/-- **Cameron–Martin TV bound for the free field** (Berestycki–Powell, arXiv:2004.04720,
Lemmas 3.12, 3.14): for `φ ∈ C²` compactly supported and even across `ℝ`, and measurable
`F` with `|F| ≤ 1` on the increments,
`|E F(incr (X + φ)) − E F(incr X)| ≤ √(exp E_H(φ) − 1)`. -/
theorem abs_integral_incr_shift_sub_le (hX : IsFreeGFFModConstH X P) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z)
    {F : (K3.BalIdx → ℝ) → ℝ} (hF : Measurable F) (hFb : ∀ x, |F x| ≤ 1) :
    |∫ ω, F (incr (X ω + ofFun φ)) ∂P - ∫ ω, F (incr (X ω)) ∂P| ≤
      Real.sqrt (Real.exp (dirichletEnergyOn H φ) - 1) := by
  set A : K3.BalIdx → Ω → ℝ := fun j ω => X ω j.1.1 - X ω j.1.2 with hAdef
  have hA : IsGaussianProcess A P := hX.gaussian
  have hmeas : ∀ j, Measurable (A j) := fun j =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hcent : ∀ j, P[A j] = 0 := fun j => hX.centered _ _ j.2.1 j.2.2.1 j.2.2.2
  set j₀ := cmIdx hφ hc heven with hj₀
  set σ : K3.BalIdx →₀ ℝ := Finsupp.single j₀ 1 with hσ
  have hshift : ∀ j, CameronMartin.covShift A P σ j = ∫ z, φ z ∂j.1.1 - ∫ z, φ z ∂j.1.2 := by
    intro j
    simp only [CameronMartin.covShift, hσ, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul, CameronMartin.covK]
    rw [hX.covariance_eq j.1 j₀.1 j.2.1 j.2.2.1 j.2.2.2 j₀.2.1 j₀.2.2.1 j₀.2.2.2]
    exact kernelCov2_cm hφ hc heven j
  have hnorm : CameronMartin.covNorm A P σ = dirichletEnergyOn H φ := by
    simp only [CameronMartin.covNorm, hσ, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
    rw [hshift]
    exact integral_cm_self hφ hc heven
  have h := K3.abs_integral_shift_sub_le hA hmeas hcent σ hF hFb
  have e : ∀ ω, incr (X ω + ofFun φ) = fun j => A j ω + CameronMartin.covShift A P σ j :=
    fun ω => funext fun j => by rw [incr_add_ofFun, hshift]; rfl
  simp only [e]
  rw [← hnorm]
  exact h

end Main

end CMTV
end QuantumZipper
