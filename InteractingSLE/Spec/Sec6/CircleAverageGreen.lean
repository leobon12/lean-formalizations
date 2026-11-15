/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.PointVariance
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Foundations.Complex.RiemannMap
import InteractingSLE.Foundations.Loewner.Capacity
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# The variance of a radial average and the conformal radius (Lemma 6.4, analytic part)

Packet PROVE-SEC6-A3 (specification §6.1, `source/spec/p145-192.md`, `#lem-6.4`, p. 157).

The proof of Lemma 6.4 uses the circle-average law [DS11, Prop. 3.2]
`h_ε(z) ∼ N(𝒞(z), −log ε + log C(z; D))`. Here the circle average is replaced by the pairing with a
fixed radial bump `b = bump_{z,δ}` (`GFF.bumpFun`), and only the difference of two variances is
needed: for an open `U ⊆ ℍ`, a conformal map `ψ : U → 𝔻` with `ψ(z) = 0`, and `B̄(z, δ) ⊆ U`,

  `Var_ℍ(b) − Var_U(b) = (∫ b)² (log C(z; ℍ) − log C(z; U))`,  `C(z; ℍ) = 2 Im z`,
  `C(z; U) = 1/|ψ'(z)|`

(`zeroGFFTestCov_sub_eq_log_confRadius`).

Proof. Both covariances are Green integrals (LQGMetric `zeroGFFTestCov_eq_green`, with `m = id` on
`ℍ` and `m = cayleyInv ∘ ψ` on `U`). Off the diagonal,
`G_ℍ(x, y) − G_U(x, y) = Q(x, y)` with the regular part
`Q(x, y) = log|x − ȳ| − log|1 − ψ(x) ψ(y)‾| + log|dslope ψ y x|` (`greenDiff`), which is symmetric and
harmonic in each variable on `U` (logarithms of moduli of non-vanishing holomorphic functions). The
mean value property against the radial bump, applied in each variable, gives
`∬ b(x) b(y) Q(x, y) = (∫ b)² Q(z, z)` and `Q(z, z) = log(2 Im z) + log|ψ'(z)|`.

## Main results

* `greenDiff`, `greenDiff_comm`, `harmonicOnNhd_greenDiff`;
* `greenH_sub_greenH_cayleyInv_eq_greenDiff`: the off-diagonal identity;
* `zeroGFFTestCov_sub_eq_log_confRadius`: the variance identity.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory TopologicalSpace
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H greenH zeroGFFTestCov)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Sec6

/-- The regular part `Q(x, y) = G_ℍ(x, y) − G_U(x, y)` of the difference of the Green functions of
`ℍ` and of `U = ψ⁻¹(𝔻)` (`ψ : U → 𝔻` conformal):
`Q(x, y) = log|x − ȳ| − log|1 − ψ(x) ψ(y)‾| + log|dslope ψ y x|`. -/
def greenDiff (ψ : ℂ → ℂ) (x y : ℂ) : ℝ :=
  Real.log ‖x - conj y‖ - Real.log ‖1 - ψ x * conj (ψ y)‖ + Real.log ‖dslope ψ y x‖

theorem greenDiff_comm (ψ : ℂ → ℂ) (x y : ℂ) : greenDiff ψ x y = greenDiff ψ y x := by
  unfold greenDiff
  have h1 : ‖x - conj y‖ = ‖y - conj x‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, ← norm_neg]
    congr 1; ring
  have h2 : ‖1 - ψ x * conj (ψ y)‖ = ‖1 - ψ y * conj (ψ x)‖ := by
    rw [← Complex.norm_conj, map_sub, map_one, map_mul, Complex.conj_conj, mul_comm]
  have h3 : dslope ψ y x = dslope ψ x y := by
    by_cases hxy : x = y
    · rw [hxy]
    · rw [dslope_of_ne _ hxy, dslope_of_ne _ (Ne.symm hxy), slope_comm]
  rw [h1, h2, h3]

/-- The value of the regular part on the diagonal at the zero of `ψ`. -/
theorem greenDiff_self {ψ : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im) (hψz : ψ z = 0) :
    greenDiff ψ z z = Real.log (2 * z.im) + Real.log ‖deriv ψ z‖ := by
  unfold greenDiff
  have e : z - conj z = ((2 * z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), Complex.norm_I,
    mul_one, hψz, zero_mul, sub_zero, norm_one, Real.log_one, sub_zero, dslope_same]

variable {U : Set ℂ} {ψ : ℂ → ℂ}

/-- The regular part is harmonic in its first variable on `U`. -/
theorem harmonicOnNhd_greenDiff (hUo : IsOpen U) (hUH : U ⊆ H)
    (hψd : DifferentiableOn ℂ ψ U) (hψi : InjOn ψ U) (hψb : MapsTo ψ U (ball 0 1))
    {y : ℂ} (hy : y ∈ U) :
    InnerProductSpace.HarmonicOnNhd (fun x => greenDiff ψ x y) U := by
  intro x hx
  have hxn : U ∈ nhds x := hUo.mem_nhds hx
  have hψa : AnalyticAt ℂ ψ x := hψd.analyticAt hxn
  -- first term
  have h1 : InnerProductSpace.HarmonicAt (fun x => Real.log ‖x - conj y‖) x := by
    refine (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm ?_
    intro h0
    simp only [Pi.sub_apply, id] at h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    have h1 : 0 < x.im := hUH hx
    have h2 : 0 < y.im := hUH hy
    linarith
  -- second term
  have h2 : InnerProductSpace.HarmonicAt (fun x => Real.log ‖1 - ψ x * conj (ψ y)‖) x := by
    refine (analyticAt_const.sub (hψa.mul analyticAt_const)).harmonicAt_log_norm ?_
    intro h0
    simp only [Pi.sub_apply, Pi.mul_apply] at h0
    have hlt : ‖ψ x * conj (ψ y)‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      have ha := mem_ball_zero_iff.1 (hψb hx)
      have hb := mem_ball_zero_iff.1 (hψb hy)
      nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ y)]
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hlt
    exact lt_irrefl _ hlt
  -- third term
  have h3 : InnerProductSpace.HarmonicAt (fun x => Real.log ‖dslope ψ y x‖) x := by
    have hd : DifferentiableOn ℂ (dslope ψ y) U :=
      (Complex.differentiableOn_dslope (hUo.mem_nhds hy)).2 hψd
    refine (hd.analyticAt hxn).harmonicAt_log_norm ?_
    by_cases hxy : x = y
    · rw [hxy, dslope_same]
      exact QuantumZipper.CA.deriv_ne_zero_of_injOn hUo hψd hψi hy
    · rw [dslope_of_ne _ hxy, slope_def_module]
      refine smul_ne_zero (inv_ne_zero (sub_ne_zero.2 hxy)) (sub_ne_zero.2 fun h => hxy ?_)
      exact hψi hx hy h
  exact (h1.sub h2).add h3

/-- Off the diagonal, `G_ℍ(x, y) − G_ℍ(C⁻¹ψ(x), C⁻¹ψ(y)) = Q(x, y)`. -/
theorem greenH_sub_greenH_cayleyInv_eq_greenDiff (hψi : InjOn ψ U)
    (hψb : MapsTo ψ U (ball 0 1)) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    greenH x y - greenH (cayleyInv (ψ x)) (cayleyInv (ψ y)) = greenDiff ψ x y := by
  have hpx := mem_ball_zero_iff.1 (hψb hx)
  have hpy := mem_ball_zero_iff.1 (hψb hy)
  have hpq : ψ x ≠ ψ y := fun h => hxy (hψi hx hy h)
  rw [GFF.greenH_cayleyInv hpx hpy hpq]
  unfold greenH greenDiff
  have hn1 : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
  have hn2 : ‖ψ x - ψ y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hpq)
  rw [dslope_of_ne _ hxy, slope_def_module, norm_smul, norm_inv,
    show ψ x - ψ y = -(ψ y - ψ x) by ring, show x - y = -(y - x) by ring, norm_neg, norm_neg]
  rw [show x - y = -(y - x) by ring, norm_neg] at hn1
  rw [show ψ x - ψ y = -(ψ y - ψ x) by ring, norm_neg] at hn2
  rw [Real.log_mul (inv_ne_zero hn1) hn2, Real.log_inv]
  ring

/-- The bump vanishes off `B̄(z, δ)`. -/
theorem mem_closedBall_of_bumpFun_ne_zero {z : ℂ} {δ : ℝ} (hδ : 0 < δ) {x : ℂ}
    (hx : GFF.bumpFun z δ x ≠ 0) : x ∈ closedBall z δ := by
  by_contra h
  rw [mem_closedBall, not_le] at h
  exact hx (GFF.bumpFun_eq_zero hδ h.le)

/-- **Variance identity** (the analytic content of Lemma 6.4). Let `U ⊆ ℍ` be open,
`ψ : U → 𝔻` a conformal bijection with `ψ(z) = 0`, and `B̄(z, δ) ⊆ U`. For the radial bump
`b = bump_{z,δ}` with mass `∫ b = δ² m`,
`Var_ℍ(b) − Var_U(b) = (δ² m)² (log(2 Im z) + log|ψ'(z)|)`, i.e. `(∫ b)² (log C(z; ℍ) − log C(z; U))`
with `C(z; ℍ) = 2 Im z` and `C(z; U) = |ψ'(z)|⁻¹`. -/
theorem zeroGFFTestCov_sub_eq_log_confRadius {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {ψ : ℂ → ℂ} (hψ : IsConformalBijection ψ U (ball 0 1)) {z : ℂ} (hψz : ψ z = 0)
    {δ : ℝ} (hδ : 0 < δ) (hB : closedBall z δ ⊆ U) :
    zeroGFFTestCov upperHalfPlaneOpens (GFF.bumpFun z δ) (GFF.bumpFun z δ) -
        zeroGFFTestCov U (GFF.bumpFun z δ) (GFF.bumpFun z δ) =
      (δ ^ 2 * GFF.bumpMass) ^ 2 * (Real.log (2 * z.im) + Real.log ‖deriv ψ z‖) := by
  set b := GFF.bumpFun z δ with hb
  set M := δ ^ 2 * GFF.bumpMass with hM
  have hzU : z ∈ (U : Set ℂ) := hB (mem_closedBall_self hδ.le)
  have hz : 0 < z.im := hUH hzU
  have hsupp : ∀ x, b x ≠ 0 → x ∈ (U : Set ℂ) := fun x hx =>
    hB (mem_closedBall_of_bumpFun_ne_zero hδ hx)
  let bU : LQGMetric.TestOn U := GFF.bumpTest z hδ hB
  let bH : LQGMetric.TestOn upperHalfPlaneOpens := GFF.bumpTest z hδ (hB.trans hUH)
  have hbU : ⇑bU = b := rfl
  have hbH : ⇑bH = b := rfl
  set m : ℂ → ℂ := cayleyInv ∘ ψ with hmdef
  have hmB : IsConformalBijection m U H :=
    isConformalBijection_comp isConformalBijection_cayleyInv hψ
  have hm : QuantumZipper.K3.IsConformalOnto m U H :=
    (isConformalBijection_iff_isConformalOnto U.isOpen).1 hmB
  have g1 := LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl
    GFF.isConformalOnto_id_H bH bH
  have g2 := LQGMetric.zeroGFFTestCov_eq_green (V := U) hUH hm bU bU
  have i1 := GFF.integrable_green_mul (V := upperHalfPlaneOpens) subset_rfl
    GFF.isConformalOnto_id_H bH (fun x => GFF.bumpFun_nonneg z δ x)
  have i2 := GFF.integrable_green_mul (V := U) hUH hm bU (fun x => GFF.bumpFun_nonneg z δ x)
  rw [hbH] at g1 i1
  rw [hbU] at g2 i2
  simp only [id] at g1 i1
  rw [g1, g2, ← integral_sub i1 i2]
  -- the integrand off the diagonal
  have hae : (fun p : ℂ × ℂ => b p.1 * b p.2 * greenH p.1 p.2 -
      b p.1 * b p.2 * greenH (m p.1) (m p.2)) =ᵐ[(volume : Measure ℂ).prod volume]
      fun p => b p.1 * b p.2 * greenDiff ψ p.1 p.2 := by
    filter_upwards [LQGMetric.ae_ne_diag] with p hp
    by_cases h1 : b p.1 = 0
    · simp [h1]
    by_cases h2 : b p.2 = 0
    · simp [h2]
    rw [← mul_sub]
    congr 1
    exact greenH_sub_greenH_cayleyInv_eq_greenDiff hψ.2.injOn hψ.2.mapsTo (hsupp _ h1)
      (hsupp _ h2) hp
  have hint := (i1.sub i2).congr hae
  rw [integral_congr_ae hae, integral_prod _ hint]
  -- the inner integral: mean value property in the second variable
  have hinner : ∀ x, ∫ y, b x * b y * greenDiff ψ x y = b x * (greenDiff ψ z x * M) := by
    intro x
    by_cases hx : b x = 0
    · simp [hx]
    have hxU := hsupp x hx
    have hmv := GFF.integral_mul_bumpFun_of_harmonic U.isOpen
      (harmonicOnNhd_greenDiff U.isOpen hUH hψ.1 hψ.2.injOn hψ.2.mapsTo hxU) hδ hB
    rw [← hmv, ← integral_const_mul]
    congr 1; funext y
    rw [greenDiff_comm ψ x y]
    ring
  simp_rw [hinner]
  -- the outer integral: mean value property in the first variable
  have hmv := GFF.integral_mul_bumpFun_of_harmonic U.isOpen
    (harmonicOnNhd_greenDiff U.isOpen hUH hψ.1 hψ.2.injOn hψ.2.mapsTo hzU) hδ hB
  have e : (fun x => b x * (greenDiff ψ z x * M)) = fun x => M * (greenDiff ψ x z * b x) := by
    funext x; rw [greenDiff_comm ψ z x]; ring
  rw [e, integral_const_mul, hmv, greenDiff_self hz hψz]
  ring

end InteractingSLE.Sec6
