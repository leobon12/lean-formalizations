import QuantumZipper.Proofs.Thm18.G2ClipNodes
import QuantumZipper.Proofs.GFF.CameronMartinTV

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2-CONST, part 2: the Gaussian bump decomposition `G2BumpDecompStmt` is proved

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66): `h = α φ + h₀` with `α` a centered
Gaussian independent of `h₀`. Source: Berestycki–Powell, *Gaussian free field and Liouville
quantum gravity*, arXiv:2004.04720, §3.3.3, Lemma 3.14 and its proof (the Cameron–Martin direction
`φ = G(ρ)`, `ρ = −Δφ/(2π)`), p. 83; uncorrelated jointly Gaussian families are independent
(mathlib `IsGaussianProcess.indepFun_of_covariance_eq_zero`).

Proof. The Cameron–Martin pair `j₀ = (μ₀, ν₀)` of `φ` (`CMTV.cmIdx`: the positive and negative
parts of `(2π)⁻¹(−Δφ) dz` on `Hbar`) is a balanced admissible pair, and by the Green
representation for the Neumann kernel (`CMTV.kernelCov2_cm`)
`Cov(X μ − X ν, β) = ∫ φ dμ − ∫ φ dν` for every balanced pair, with `β = X μ₀ − X ν₀`; in
particular `Var β = E_H(φ) > 0` (`CMTV.integral_cm_self`, `dirichletEnergyOn_H_pos_g2`). Put
`α = β / E_H(φ)`. For admissible `μ` of mass `m`, `X μ − m X(refS) = X μ − X(m • refS)` a.s.
(linearity), a balanced increment, and `∫ φ d(m • refS) = 0` (`φ` vanishes on the unit
semicircle). Hence `h₀ μ = X μ − m X(refS) − α ∫ φ dμ` is a.s. a linear combination of two
increments, jointly Gaussian with `α` and uncorrelated with it.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

/-- **Positivity of the Dirichlet energy on `ℍ`** of a nonzero, even, compactly supported `C²`
function (own elementary argument: zero energy forces `φ` constant on `ℍ`, hence `0`). -/
theorem dirichletEnergyOn_H_pos_g2 {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) (hne : ∃ z, φ z ≠ 0) : 0 < dirichletEnergyOn H φ := by
  set g : ℂ → ℝ := fun z => ‖fderiv ℝ φ z‖ ^ 2 with hg
  have hcont : Continuous g := ((hφ.continuous_fderiv (by norm_num)).norm).pow 2
  have hgc : HasCompactSupport g :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ‖L‖ ^ 2) (by simp)
  have hint : Integrable g := hcont.integrable_of_hasCompactSupport hgc
  -- some point of `ℍ` has nonzero derivative
  have hpt : ∃ z ∈ H, fderiv ℝ φ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hconv : Convex ℝ H := convex_halfSpace_gt Complex.imLm.isLinear 0
    obtain ⟨a, ha⟩ := isOpen_H.exists_is_const_of_fderiv_eq_zero hconv.isPreconnected
      (hφ.differentiable (by norm_num)).differentiableOn fun z hz => hcon z hz
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
    set z₁ : ℂ := ((|R| + 1 : ℝ) : ℂ) * Complex.I
    have hz₁H : z₁ ∈ H := by
      show 0 < z₁.im
      simp only [z₁, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
        Complex.I_re, mul_one, mul_zero, add_zero]
      positivity
    have hz₁ : φ z₁ = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR hmem
      rw [mem_closedBall, dist_zero_right] at this
      have hn : ‖z₁‖ = |R| + 1 := by
        simp only [z₁, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by positivity)
      rw [hn] at this
      linarith [le_abs_self R]
    have ha0 : a = 0 := by rw [← ha z₁ hz₁H, hz₁]
    have hH : EqOn φ 0 H := fun z hz => by rw [ha z hz, ha0]; rfl
    have hHbar : EqOn φ 0 Hbar := by
      have := hH.closure hφ.continuous continuous_const
      rwa [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0] at this
    obtain ⟨z, hz⟩ := hne
    apply hz
    rcases le_or_gt 0 z.im with h | h
    · exact hHbar h
    · have hc' : conj z ∈ Hbar := by
        show 0 ≤ (conj z).im
        rw [Complex.conj_im]; linarith
      rw [← heven z]; exact hHbar hc'
  obtain ⟨z₀, hz₀H, hz₀⟩ := hpt
  have hpos : 0 < ∫ z in H, g z := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun z => by positivity)
      hint.integrableOn]
    refine (hcont.isOpen_support.inter isOpen_H).measure_pos volume ⟨z₀, ?_, hz₀H⟩
    show g z₀ ≠ 0
    simp only [g]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz₀)
  unfold dirichletEnergyOn
  exact mul_pos (inv_pos.2 (by positivity)) hpos

/-- Covariance is unchanged by an a.e. modification of the left argument. -/
theorem covariance_congr_left_g2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f f' g : Ω → ℝ} (h : f =ᵐ[P] f') : cov[f, g; P] = cov[f', g; P] := by
  unfold covariance
  rw [integral_congr_ae h]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

/-- A bump supported in the unit disc integrates to `0` against any measure missing the disc. -/
theorem integral_bump_eq_zero_g2 {φ : ℂ → ℝ} (hsupp : tsupport φ ⊆ ball (0 : ℂ) 1)
    {ν : Measure ℂ} (hν : ν (ball (0 : ℂ) 1) = 0) : ∫ z, φ z ∂ν = 0 := by
  refine integral_eq_zero_of_ae ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun z hz => ?_) hν
  exact hsupp (subset_tsupport φ hz)

/-- **`G2BumpDecompStmt` holds** (Berestycki–Powell, arXiv:2004.04720, Lemma 3.14, p. 83;
Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 66). -/
theorem g2BumpDecompStmt_holds : G2BumpDecompStmt := by
  classical
  intro φ hφ hc hsupp heven hne
  have hX := gffBase.gff
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hev : ∀ z, φ (conj z) = φ z := heven
  set X := gffBase.X with hXdef
  set P := gffBase.P with hPdef
  set j₀ : K3.BalIdx := CMTV.cmIdx hφ2 hc hev with hj₀
  set Z : K3.BalIdx → gffBase.Ω → ℝ := fun j ω => X ω j.1.1 - X ω j.1.2 with hZdef
  have hZ : IsGaussianProcess Z P := hX.gaussian
  have hmem : ∀ j, MemLp (Z j) 2 P := fun j => (hZ.hasGaussianLaw_eval j).memLp_two
  have hcovZ : ∀ j j' : K3.BalIdx, cov[Z j, Z j'; P] = kernelCov2 neumannH j.1 j'.1 :=
    fun j j' => hX.covariance_eq _ _ j.2.1 j.2.2.1 j.2.2.2 j'.2.1 j'.2.2.1 j'.2.2.2
  have hcov0 : ∀ j : K3.BalIdx, cov[Z j, Z j₀; P] = ∫ z, φ z ∂j.1.1 - ∫ z, φ z ∂j.1.2 :=
    fun j => (hcovZ j j₀).trans (CMTV.kernelCov2_cm hφ2 hc hev j)
  set E : ℝ := dirichletEnergyOn H φ with hEdef
  have hE : 0 < E := dirichletEnergyOn_H_pos_g2 hφ2 hc hev hne
  have hvar : cov[Z j₀, Z j₀; P] = E := (hcov0 j₀).trans (CMTV.integral_cm_self hφ2 hc hev)
  -- the reference pairs `(μ, m • refS)`
  have hrefS : IsAdmissibleH refS := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
  have hsm : ∀ c : ℝ≥0, IsAdmissibleH (c • refS) := fun c =>
    isAdmissibleH_smul (c := (c : ℝ≥0∞)) hrefS ENNReal.coe_lt_top
  have hmass : ∀ μ : AdmIdx, μ.1 univ = ((μ.1 univ).toNNReal • refS) univ := fun μ => by
    have := μ.2.1
    rw [Measure.smul_apply, show refS univ = 1 from measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
      ENNReal.coe_toNNReal (measure_ne_top _ _)]
  let refIdx : AdmIdx → K3.BalIdx := fun μ =>
    ⟨(μ.1, (μ.1 univ).toNNReal • refS), μ.2, hsm _, hmass μ⟩
  have hrefφ : ∀ μ : AdmIdx, ∫ z, φ z ∂((μ.1 univ).toNNReal • refS) = 0 := fun μ =>
    integral_bump_eq_zero_g2 hsupp (by
      rw [Measure.smul_apply, show refS (ball (0 : ℂ) 1) = 0 from
        refS_ball_null (t := 0) (r := 1) (by norm_num), smul_zero])
  -- the coefficient and the bump-free field
  set α : gffBase.Ω → ℝ := fun ω => E⁻¹ * Z j₀ ω with hαdef
  set h₀ : AdmIdx → gffBase.Ω → ℝ := fun μ ω =>
    X ω μ.1 - (μ.1 univ).toReal * X ω refS - α ω * ∫ z, φ z ∂μ.1 with hh₀def
  set c : AdmIdx → ℝ := fun μ => E⁻¹ * ∫ z, φ z ∂μ.1 with hcdef
  have hae : ∀ μ : AdmIdx, h₀ μ =ᵐ[P] fun ω => Z (refIdx μ) ω - c μ * Z j₀ ω := by
    intro μ
    have hl := hX.linear refS refS hrefS hrefS (μ.1 univ).toNNReal 0
    filter_upwards [hl] with ω hω
    rw [zero_smul, add_zero] at hω
    simp only [h₀, Z, refIdx, c, α, hω, NNReal.coe_zero, zero_mul, add_zero]
    rw [show (((μ.1 univ).toNNReal : ℝ≥0) : ℝ) = (μ.1 univ).toReal from rfl]
    ring
  -- joint Gaussianity
  set W : AdmIdx ⊕ Unit → gffBase.Ω → ℝ :=
    Sum.elim (fun μ ω => Z (refIdx μ) ω - c μ * Z j₀ ω) (fun _ => α) with hWdef
  have hW : IsGaussianProcess W P := by
    refine hZ.of_isGaussianProcess fun s => ?_
    rcases s with μ | u
    · refine ⟨{refIdx μ, j₀}, ContinuousLinearMap.proj (R := ℝ) ⟨refIdx μ, by simp⟩ -
        c μ • ContinuousLinearMap.proj (R := ℝ) ⟨j₀, by simp⟩, fun ω => ?_⟩
      simp [W, Finset.restrict]
    · refine ⟨{j₀}, E⁻¹ • ContinuousLinearMap.proj (R := ℝ) ⟨j₀, by simp⟩, fun ω => ?_⟩
      simp [W, α, Finset.restrict]
  have hG : IsGaussianProcess (Sum.elim h₀ (fun (_ : Unit) => α)) P := by
    refine hW.congr fun t => ?_
    rcases t with μ | u
    · exact (hae μ).symm
    · exact ae_of_all _ fun ω => rfl
  have hmeasZ : ∀ j, Measurable (Z j) := fun j =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hαm : Measurable α := (hmeasZ j₀).const_mul _
  have hh₀m : ∀ μ, Measurable (h₀ μ) := fun μ =>
    ((hX.measurable_coord _).sub ((hX.measurable_coord _).const_mul _)).sub
      (hαm.mul_const _)
  -- zero cross-covariance
  have hcross : ∀ μ (_ : Unit), cov[h₀ μ, α; P] = 0 := by
    intro μ _
    rw [covariance_congr_left_g2 (hae μ)]
    have hα2 : MemLp α 2 P := (hmem j₀).const_mul _
    rw [covariance_fun_sub_left (hmem _) ((hmem j₀).const_mul _) hα2,
      covariance_const_mul_left, hαdef, covariance_const_mul_right, covariance_const_mul_right,
      hvar, hcov0 (refIdx μ)]
    simp only [refIdx, hrefφ μ, sub_zero, c]
    field_simp
    ring
  have hind := hG.indepFun_of_covariance_eq_zero (fun μ => (hh₀m μ).aemeasurable) (fun _ => hαm.aemeasurable) hcross
  -- the law of `α`
  have hαG : HasGaussianLaw α P := hG.hasGaussianLaw_eval (Sum.inr ())
  have hmean : ∫ ω, α ω ∂P = 0 := by
    simp only [hαdef]
    rw [integral_const_mul]
    have := hX.centered _ _ j₀.2.1 j₀.2.2.1 j₀.2.2.2
    simp only [Z] at this ⊢
    rw [this, mul_zero]
  have hVar : Var[α; P] = E⁻¹ := by
    rw [← covariance_self hαm.aemeasurable, hαdef, covariance_const_mul_left,
      covariance_const_mul_right, hvar]
    field_simp
  refine ⟨α, Var[α; P].toNNReal, ?_, hαm, ?_, ?_⟩
  · rw [hVar]; exact Real.toNNReal_pos.2 (inv_pos.2 hE)
  · rw [hαG.map_eq_gaussianReal, hmean]
  · have := (hind.symm).comp (φ := fun f : Unit → ℝ => f ()) (ψ := id)
      (show Measurable fun f : Unit → ℝ => f () from measurable_pi_apply ()) measurable_id
    exact this

end Thm18Asm
end QuantumZipper
