import QuantumZipper.Proofs.Thm11.AddendumEnergy
import QuantumZipper.Proofs.Thm11.AddendumGEnergy
import QuantumZipper.Proofs.Thm11.SmallGaps

/-!
# THM11-AD3: the `L`-harmonic function `Ψ = Φ² + g∘arg` and the energy identity

For the one-point state `x = (z, A)` of the forward centered flow, `Φ(z,A) = h0fwd κ z − χ A` is
the field and `g` the FD-8 function (`LyapunovAlgebra.lean`). The generator of `Φ²` is
`4 (Im z)²/‖z‖⁴` (`dynkinGen_fzPhi_sq`) and the generator of `g ∘ arg` is `−4 (Im z)²/‖z‖⁴`
(`dynkinGen_gFun_arg`, the `dynkinGen` form of `genL_neg_gFun_arg`), so `Ψ = Φ² + g∘arg` is
`L`-harmonic where the taming is inactive. For `κ ∈ (4,8)` the function `g` is bounded
(`exists_abs_gFun_le`), so `Ψ` stopped at the freezing time is a bounded martingale, which gives
the energy identity
`E[(𝔥^δ_T)²] = Φ(a,0)² + g(arg a) − E[g(arg Z̃_σ(a))]`.

Source: own elementary computation (chain rule along lines, `gPrime_ode_div`, and the local Dynkin
martingale `martingale_localDynkin_stopped`); no published proof is followed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Add

open FrozenMart Thm11Lyap

/-- Ψ = Φ² + g∘arg : L-harmonic on the one-point state. -/
def fzPsi (κ : ℝ) (x : ℂ × ℝ) : ℝ := fzPhi κ x ^ 2 + gFun κ (Complex.arg x.1)

/-- Linearity of the Dynkin generator. -/
theorem dynkinGen_add_ad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : E → E} {e : E}
    {F G : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G x) :
    dynkinGen b e (F + G) x = dynkinGen b e F x + dynkinGen b e G x := by
  unfold dynkinGen
  rw [fderiv_add (hF.differentiableAt (by norm_num)) (hG.differentiableAt (by norm_num)),
    iteratedFDeriv_add_apply hF hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  ring

theorem contDiffAt_gFun_arg (κ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1)) x := by
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gFun κ) (Complex.arg x.1) :=
    (contDiffOn_gFun κ).contDiffAt (isOpen_Ioo.mem_nhds (NonSwallow.arg_mem_Ioo_of_im_pos hx))
  exact hg.comp x ((contDiffAt_arg_real (mem_slitPlane_of_im_pos hx)).comp x contDiffAt_fst)

theorem contDiffAt_fzPsi (κ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fzPsi κ) x :=
  ((contDiffAt_fzPhi κ hx).pow 2).add (contDiffAt_gFun_arg κ hx)

theorem contDiffOn_fzPsi (κ : ℝ) : ContDiffOn ℝ 3 (fzPsi κ) {x : ℂ × ℝ | 0 < x.1.im} :=
  fun _ hx => ((contDiffAt_fzPsi κ hx).of_le (by exact WithTop.coe_le_coe.2 le_top)).contDiffWithinAt

theorem hasDerivAt_gFun_arg_line (κ : ℝ) (z w : ℂ) (r : ℝ) (h : 0 < (z + r * w).im) :
    HasDerivAt (fun s : ℝ => gFun κ (Complex.arg (z + s * w)))
      (gPrime κ (Complex.arg (z + r * w)) * (w / (z + r * w)).im) r := by
  have h1 := (hasDerivAt_gFun κ (NonSwallow.arg_mem_Ioo_of_im_pos h)).comp r
    (hasDerivAt_arg_line z w r (mem_slitPlane_of_im_pos h))
  exact h1

theorem gArg_line (κ : ℝ) (x v : ℂ × ℝ) (s : ℝ) :
    (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1)) (x + s • v) = gFun κ (Complex.arg (x.1 + s * v.1)) := by
  simp [Complex.real_smul]

theorem im_two_div_div (z : ℂ) :
    (2 / z / z).im = -4 * z.re * z.im / (z.re ^ 2 + z.im ^ 2) ^ 2 := by
  rw [div_div, ← pow_two]
  simp only [Complex.div_im, pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  simp
  ring

theorem im_noise_div {κ : ℝ} (z : ℂ) :
    (-(Real.sqrt κ : ℂ) / z).im = Real.sqrt κ * z.im / (z.re ^ 2 + z.im ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply]
  ring

theorem im_noise_sq {κ : ℝ} (hκ : 0 < κ) (z : ℂ) :
    ((0 - -(Real.sqrt κ : ℂ) * -(Real.sqrt κ : ℂ)) / z ^ 2).im
      = 2 * κ * z.re * z.im / (z.re ^ 2 + z.im ^ 2) ^ 2 := by
  rw [zero_sub]
  have e : -(-(Real.sqrt κ : ℂ) * -(Real.sqrt κ : ℂ)) = ((-κ : ℝ) : ℂ) := by
    have : (Real.sqrt κ : ℂ) * Real.sqrt κ = κ := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hκ.le]
    push_cast
    linear_combination (-1 : ℂ) * this
  rw [e, div_eq_mul_inv, Complex.im_ofReal_mul]
  simp only [Complex.inv_im, pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  field_simp
  ring

/-- **The generator of `g ∘ arg`** is `−4 (Im z)²/‖z‖⁴` where the taming is inactive. -/
theorem dynkinGen_gFun_arg {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) {x : ℂ × ℝ}
    (hx : c ≤ x.1.im) :
    dynkinGen (fzDrift c) (fzNoise κ) (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1)) x
      = -(4 * x.1.im ^ 2 / ‖x.1‖ ^ 4) := by
  have hz : 0 < x.1.im := hc.trans_le hx
  have hθ := NonSwallow.arg_mem_Ioo_of_im_pos hz
  have hcd : ContDiffAt ℝ 2 (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1)) x :=
    (contDiffAt_gFun_arg κ hz).of_le (by exact WithTop.coe_le_coe.2 le_top)
  -- drift line
  have hdrift : HasDerivAt (fun s : ℝ => (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1))
      (x + s • fzDrift c x)) (gPrime κ (Complex.arg x.1) * (2 / x.1 / x.1).im) 0 := by
    have h := hasDerivAt_gFun_arg_line κ x.1 (2 / x.1) 0 (by simpa using hz)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    have e : (fun s : ℝ => (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1)) (x + s • fzDrift c x))
        = fun s : ℝ => gFun κ (Complex.arg (x.1 + s * (2 / x.1))) := by
      funext s; rw [gArg_line, fzDrift_of_le hx]
    rw [e]; exact h
  -- noise line
  have him : ∀ r : ℝ, 0 < (x.1 + r * (fzNoise κ).1).im := fun r => by rw [im_add_noise]; exact hz
  have hnd : deriv (fun r : ℝ => (fun y : ℂ × ℝ => gFun κ (Complex.arg y.1)) (x + r • fzNoise κ))
      = fun r : ℝ => gPrime κ (Complex.arg (x.1 + r * (fzNoise κ).1))
          * ((fzNoise κ).1 / (x.1 + r * (fzNoise κ).1)).im := by
    funext r
    simp only [gArg_line]
    exact (hasDerivAt_gFun_arg_line κ x.1 _ r (him r)).deriv
  have hgp := hasDerivAt_gPrime κ hθ
  rw [← hgp.deriv] at hgp
  have hne : x.1 + ((0 : ℝ) : ℂ) * (fzNoise κ).1 ≠ 0 := fun h => by
    have := him 0; rw [h, Complex.zero_im] at this; exact lt_irrefl _ this
  have hd : HasDerivAt (fun r : ℝ => x.1 + (r : ℂ) * (fzNoise κ).1) (fzNoise κ).1 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (fzNoise κ).1).const_add x.1
  have hq := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) (fzNoise κ).1).div hd hne)
  have ha := hasDerivAt_arg_line x.1 (fzNoise κ).1 0 (mem_slitPlane_of_im_pos (him 0))
  have hgp0 : HasDerivAt (gPrime κ) (deriv (gPrime κ) (Complex.arg x.1))
      (Complex.arg (x.1 + ((0 : ℝ) : ℂ) * (fzNoise κ).1)) := by
    simpa using hgp
  have h1 := hgp0.comp (0 : ℝ) ha
  have h2 := h1.mul hq
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h2
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hcd.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hcd, hdrift.deriv, hnd]
  have h2' : HasDerivAt (fun r : ℝ => gPrime κ (Complex.arg (x.1 + r * (fzNoise κ).1))
      * ((fzNoise κ).1 / (x.1 + r * (fzNoise κ).1)).im)
      (deriv (gPrime κ) (Complex.arg x.1) * ((fzNoise κ).1 / x.1).im * ((fzNoise κ).1 / x.1).im
        + gPrime κ (Complex.arg x.1) * ((0 - (fzNoise κ).1 * (fzNoise κ).1) / x.1 ^ 2).im) 0 := by
    have h3 := h2.congr_deriv (g' := deriv (gPrime κ) (Complex.arg x.1) * ((fzNoise κ).1 / x.1).im
        * ((fzNoise κ).1 / x.1).im
        + gPrime κ (Complex.arg x.1) * ((0 - (fzNoise κ).1 * (fzNoise κ).1) / x.1 ^ 2).im)
      (by simp only [Function.comp_apply, Pi.div_apply, Complex.imCLM_apply, Complex.ofReal_zero, zero_mul, add_zero])
    exact h3
  rw [h2'.deriv]
  simp only [fzNoise]
  rw [im_two_div_div, im_noise_div, im_noise_sq hκ]
  -- the ODE
  have hode := gPrime_ode_div hκ.ne' hθ
  have hz0 : x.1 ≠ 0 := fun h => by simp [h] at hz
  rw [Complex.sin_arg, Complex.cos_arg hz0] at hode
  have hn : 0 < ‖x.1‖ := norm_pos_iff.2 hz0
  have hsq : ‖x.1‖ ^ 2 = x.1.re ^ 2 + x.1.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hqu : ‖x.1‖ ^ 4 = (x.1.re ^ 2 + x.1.im ^ 2) ^ 2 := by
    rw [show ‖x.1‖ ^ 4 = (‖x.1‖ ^ 2) ^ 2 by ring, hsq]
  have hode' : κ / 2 * deriv (gPrime κ) (Complex.arg x.1) * x.1.im
      + (κ - 4) * x.1.re * gPrime κ (Complex.arg x.1) = -4 * x.1.im := by
    have e : x.1.re / ‖x.1‖ / (x.1.im / ‖x.1‖) = x.1.re / x.1.im := by
      field_simp
    rw [e] at hode
    field_simp at hode
    linear_combination (1 / 2 : ℝ) * hode
  have hN : (0 : ℝ) < x.1.re ^ 2 + x.1.im ^ 2 := by positivity
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  rw [hqu]
  generalize x.1.re ^ 2 + x.1.im ^ 2 = N
  linear_combination (x.1.im / N ^ 2) * hode'
    + (1 / 2 * deriv (gPrime κ) (Complex.arg x.1) * x.1.im ^ 2 / N ^ 2) * hs

theorem dynkinGen_fzPsi {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) {x : ℂ × ℝ}
    (hx : c ≤ x.1.im) :
    dynkinGen (fzDrift c) (fzNoise κ) (fzPsi κ) x = 0 := by
  have hz : 0 < x.1.im := hc.trans_le hx
  have e : fzPsi κ = (fun y => fzPhi κ y ^ 2) + fun y : ℂ × ℝ => gFun κ (Complex.arg y.1) := rfl
  rw [e, dynkinGen_add_ad (((contDiffAt_fzPhi κ hz).pow 2))
    ((contDiffAt_gFun_arg κ hz).of_le (by exact WithTop.coe_le_coe.2 le_top)),
    dynkinGen_fzPhi_sq hκ hc hx, dynkinGen_gFun_arg hκ hc hx]
  ring

/-! ## The martingale and the energy identity -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem abs_fzPsi_le_of_mem {κ c δ : ℝ} {T : ℝ≥0} {C : ℝ}
    (hC : ∀ θ ∈ Ioo 0 Real.pi, |gFun κ θ| ≤ C) {x : ℂ × ℝ} (hx : x ∈ fzK δ c T)
    (hpos : 0 < x.1.im) : |fzPsi κ x| ≤ fzBound κ c T ^ 2 + C := by
  have h1 := abs_fzPhi_le_of_mem (κ := κ) hx
  have h2 := hC _ (NonSwallow.arg_mem_Ioo_of_im_pos hpos)
  unfold fzPsi
  refine (abs_add_le _ _).trans (add_le_add ?_ h2)
  rw [abs_pow]
  nlinarith [abs_nonneg (fzPhi κ x)]

/-- MF-1 for Ψ (κ ∈ (4,8), g bounded by `exists_abs_gFun_le`). -/
theorem fzPsi_martingale (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ}
    (hδa : δ ≤ a.im) (T : ℝ≥0) :
    Martingale (fun t ω => fzPsi κ (fzU κ c B a (min t (frozenTime κ c δ T B a ω)) ω)) 𝓕 P := by
  have hκ : 0 < κ := by linarith
  obtain ⟨C, hC⟩ := exists_abs_gFun_le hκ4 hκ8
  have hKO : fzK δ c T ⊆ {x : ℂ × ℝ | 0 < x.1.im} := fun x hx =>
    (hc.trans_le hcδ).trans_le hx.1
  exact martingale_localDynkin_stopped hB hBc 𝓕 hBad hpast (lipschitzWith_fzDrift hc)
    (norm_fzDrift_le hc) (fzU_eq hBc hc a) isOpen_fzO (isClosed_fzCl δ) (isClosed_fzK δ c T) hKO
    (contDiffOn_fzPsi κ) (fun x hx _ => dynkinGen_fzPsi hκ hc (hcδ.trans hx.1)) T
    (fun ω t htT h => fzU_mem_fzK hBc hc hδa ω htT h)
    (fun x hx => abs_fzPsi_le_of_mem hC hx (hKO hx))

/-- The energy identity at the freezing time. -/
theorem integral_frozenField_sq (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ}
    (hδa : δ ≤ a.im) (T : ℝ≥0) :
    Integrable (fun ω => gFun κ (Complex.arg (fzZ κ c B a (frozenTime κ c δ T B a ω) ω))) P ∧
    Integrable (fun ω => frozenField κ c δ T B a T ω ^ 2) P ∧
    ∫ ω, frozenField κ c δ T B a T ω ^ 2 ∂P
      = fzPhi κ (a, 0) ^ 2 + gFun κ (Complex.arg a)
        - ∫ ω, gFun κ (Complex.arg (fzZ κ c B a (frozenTime κ c δ T B a ω) ω)) ∂P := by
  have hκ : 0 < κ := by linarith
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := fzPsi_martingale hB hBc 𝓕 hBad hpast hκ4 hκ8 hc hcδ hδa T
  have hF := frozenField_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ hδa T
  have hσ : ∀ ω, min T (frozenTime κ c δ T B a ω) = frozenTime κ c δ T B a ω :=
    fun ω => min_eq_right (hittingBtwn_le ω)
  have hpt : ∀ ω, fzPsi κ (fzU κ c B a (min T (frozenTime κ c δ T B a ω)) ω)
      = frozenField κ c δ T B a T ω ^ 2
        + gFun κ (Complex.arg (fzZ κ c B a (frozenTime κ c δ T B a ω) ω)) := fun ω => by
    simp only [fzPsi, frozenField, hσ]
    rfl
  have hF2 : Integrable (fun ω => frozenField κ c δ T B a T ω ^ 2) P := by
    refine Integrable.of_bound ((hF.integrable T).aestronglyMeasurable.pow 2)
      (fzBound κ c T ^ 2) (Eventually.of_forall fun ω => ?_)
    have h1 := abs_frozenField_le hBc hc hδa T T ω (κ := κ)
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (frozenField κ c δ T B a T ω)]
  have hMT : Integrable (fun ω => fzPsi κ (fzU κ c B a (min T (frozenTime κ c δ T B a ω)) ω)) P :=
    hM.integrable T
  have hg : Integrable
      (fun ω => gFun κ (Complex.arg (fzZ κ c B a (frozenTime κ c δ T B a ω) ω))) P := by
    refine (hMT.sub hF2).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, hpt]
    ring
  refine ⟨hg, hF2, ?_⟩
  have hint : ∫ ω, fzPsi κ (fzU κ c B a (min T (frozenTime κ c δ T B a ω)) ω) ∂P
      = ∫ ω, fzPsi κ (fzU κ c B a (min 0 (frozenTime κ c δ T B a ω)) ω) ∂P := by
    have := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using this.symm
  have h0 : ∫ ω, fzPsi κ (fzU κ c B a (min 0 (frozenTime κ c δ T B a ω)) ω) ∂P
      = fzPsi κ (a, 0) := by
    have hae : (fun ω => fzPsi κ (fzU κ c B a (min 0 (frozenTime κ c δ T B a ω)) ω))
        =ᵐ[P] fun _ => fzPsi κ (a, 0) := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      rw [min_eq_left zero_le, fzU_eq hBc hc a ω 0]
      simp [hω]
    rw [integral_congr_ae hae, integral_const]
    simp
  rw [h0, funext hpt, integral_add hF2 hg] at hint
  unfold fzPsi at hint
  linarith

end Thm11Add
end QuantumZipper
