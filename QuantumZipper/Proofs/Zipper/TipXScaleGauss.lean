import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.Zipper.UnifGaugeNodes
import QuantumZipper.Proofs.Zipper.UnifSWGaussRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC-G: exponential moments of the pinned circle average at the origin

For a free-boundary GFF modulo constants `X` whose gauge is pinned (`RegUnif.IsNrmSample X`,
i.e. `X ω (foldedCircle 0 1) = 0`):

* `measurable_evalReg_fc_of_free`: `ω ↦ evalReg (X ω) (foldedCircle d r)` is measurable.
* `lintegral_exp_evalReg_fc0_nrm`: `E exp(θ h_{2^{-k}}(0)) = exp(θ² k log 2)`.

Proof. A regular version `G` of `X` (`WedgeTK.exists_isRegVersion`) gives a.s.
`evalReg (X ω) (fc(0,r)) = G ω (0,r) = X ω (fc(0,r))`; with the pinning this is the radial
process `A_t = h_{e^{-t}}(0) − h_1(0)` at `t = k log 2` (`WedgeTK.radialProc_ae_eq`), a centred
Gaussian of variance `2t` (`WedgeTK.isGaussianProcess_radialProc`, `integral_radialProc`,
`covariance_radialProc`: the circle-average Brownian motion of Sheffield, arXiv:1012.4797 §3,
and Duplantier–Sheffield, "Liouville quantum gravity and KPZ", Invent. Math. 2011, Prop. 3.3).
The exponential moment is the standard Gaussian mgf `E e^{θZ} = e^{θ² Var Z / 2}`
(mathlib `mgf_id_gaussianReal`, via `RegUnif.swg_lintegral_exp_gauss`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace QuantumZipper.WedgeUnzip

open WedgeTK GaussTK

theorem measurable_evalReg_fc_of_free {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (d : ℂ) (r : ℝ) :
    Measurable fun ω => evalReg (X ω) (foldedCircle d r) :=
  (measurable_evalReg (foldedCircle d r)).comp (measurable_pi_iff.mpr hX.measurable_coord)

theorem txsc_radius_eq_exp (k : ℕ) : radius k = Real.exp (-((k : ℝ) * Real.log 2)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), radius, inv_pow]

theorem lintegral_exp_evalReg_fc0_nrm {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (hN : RegUnif.IsNrmSample X) (θ : ℝ) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * evalReg (X ω) (foldedCircle 0 (radius k)))) ∂P =
      ENNReal.ofReal (Real.exp (θ ^ 2 * ((k : ℝ) * Real.log 2))) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  set t : ℝ := (k : ℝ) * Real.log 2 with ht_def
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num))
  have hrad : radius k = Real.exp (-t) := txsc_radius_eq_exp k
  have hpos : 0 < radius k := by rw [hrad]; exact Real.exp_pos _
  have hpin : ∀ ω, X ω (foldedCircle 0 1) = 0 := fun ω => by
    rw [← hN ω]; simp [B1Full.nrm, addConst, measure_univ]
  have hae : (fun ω => evalReg (X ω) (foldedCircle 0 (radius k))) =ᵐ[P] radialProc X t := by
    filter_upwards [hG.reg, hG.raw 0 zero_mem_Hbar (radius k) hpos, radialProc_ae_eq hG t]
      with ω h1 h2 h3
    rw [h1.evalReg_fc_of_mem zero_mem_Hbar hpos, h2, h3]
    simp only [fcPairVal, radIdx]
    rw [hpin ω, sub_zero, hrad]
  have hae' : (fun ω => ENNReal.ofReal (Real.exp (θ * evalReg (X ω)
      (foldedCircle 0 (radius k))))) =ᵐ[P]
      fun ω => ENNReal.ofReal (Real.exp (θ * radialProc X t ω)) := by
    filter_upwards [hae] with ω h
    rw [h]
  rw [lintegral_congr_ae hae',
    RegUnif.swg_lintegral_exp_gauss ((isGaussianProcess_radialProc hX).hasGaussianLaw_eval t)
      (integral_radialProc hX t) θ,
    ← covariance_self (measurable_radialProc hX t).aemeasurable, covariance_radialProc hX,
    max_eq_left ht, max_eq_right (neg_nonpos.2 ht), min_self, min_self]
  congr 2
  ring

end QuantumZipper.WedgeUnzip
