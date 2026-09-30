import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Dynkin
import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Path
import QuantumZipper.Proofs.RS.OnePointWeightedGen

/-!
# THM11 AD-2, probabilistic part: the conformal radius of a fixed point stays bounded below

Blueprint `blueprint/THM11_BLUEPRINT.md` §9, node AD-2 (κ ∈ (4,8)). Write
`L_t = fwdLogCR W t a = log Im f_t(a) − Re log f_t'(a)` (the log conformal radius of `H \ K_t`
seen from `a`, up to `log 2`). The one-point state `(Z, L)` of the forward flow is the RS one-point
state `opProc` (`OnePointState`, `OnePointWeightedGen`), with generator
`κ (Im Z)²/‖Z‖⁴ · radGen` (`dynkinGen_opDrift_angle`). With the FD-8 function `g`
(`LyapunovAlgebra.gFun`), `φ(L, θ) = L − g(θ)` is radially harmonic (`radGen_L_sub_gFun`, from
the ODE `gPrime_ode_div`), so `L − g(arg Z)` stopped at the freezing time is a martingale and

`E[L_0 − L_σ] = g(arg a) − E g(arg Z_σ) ≤ 2 ‖g‖_∞`

(`integral_logCR_drop_le`), bounded uniformly in the level since `g` is bounded for κ < 8
(`Thm11Lyap.exists_abs_gFun_le`). Fatou's lemma along the levels `δ_n = Im a / 2^{n+1}` gives:
almost surely, `L_t ≥ log Im a − M(ω)` for every `t ≤ T` before the swallowing time of `a`
(`ae_logCR_lower_bound`).

Source: the blueprint route (FD-8, "`E[C_0 − C_{τ−}] ≤ 2‖g‖`"); this is the classical
argument that for κ < 8 a fixed point is not hit (Rohde–Schramm, *Basic properties of SLE*,
Ann. Math. 161 (2005), Lemma 6.3 and Thm 6.4, pp. 25–31, where it is done with the one-point
martingale in the radial parametrization). The Lyapunov function `L − g∘arg` is our own
(FD-8); no published proof in exactly this form is followed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Area

open FrozenMart Thm11Lyap Thm11Add RS FwdClock FwdHolo

/-! ## The radial harmonicity of `L − g(θ)` -/

/-- `φ(L, θ) = L − g(θ)` is radially harmonic: `radGen κ φ = 0` on `(0, π)`. -/
theorem radGen_L_sub_gFun {κ : ℝ} (hκ : 0 < κ) (L : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    radGen κ (fun L' θ' => L' - gFun κ θ') L θ = 0 := by
  have h1 : deriv (fun L' : ℝ => L' - gFun κ θ) L = 1 := by
    have := (hasDerivAt_id L).sub_const (gFun κ θ)
    exact this.deriv
  have h2 : deriv (fun θ' => L - gFun κ θ') θ = -gPrime κ θ :=
    ((hasDerivAt_gFun κ hθ).const_sub L).deriv
  have h3 : deriv (deriv (fun θ' => L - gFun κ θ')) θ = -deriv (gPrime κ) θ := by
    have hev : deriv (fun θ' => L - gFun κ θ') =ᶠ[𝓝 θ] fun θ' => -gPrime κ θ' := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ((hasDerivAt_gFun κ hθ').const_sub L).deriv
    rw [hev.deriv_eq, deriv.fun_neg]
  have hode := gPrime_ode_div hκ.ne' hθ
  unfold radGen
  rw [h1, h2, h3]
  have hκ0 : κ ≠ 0 := hκ.ne'
  field_simp
  linear_combination (-2) * hode

/-- `F(Z, L) = L − g(arg Z)` has zero generator for the tamed one-point state where the
taming is inactive. -/
theorem dynkinGen_L_sub_gFun {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) {x : ℂ × ℝ}
    (hx : c ≤ x.1.im) :
    dynkinGen (opDrift c) (opNoise κ)
      (fun y : ℂ × ℝ => (fun L' θ' => L' - gFun κ θ') y.2 (Complex.arg y.1)) x = 0 := by
  obtain ⟨Z, L⟩ := x
  have hφ : ContDiffOn ℝ 3 (Function.uncurry fun L' θ' => L' - gFun κ θ')
      (univ ×ˢ Ioo 0 Real.pi) := by
    have hg3 : ContDiffOn ℝ 3 (gFun κ) (Ioo 0 Real.pi) :=
      (contDiffOn_gFun κ).of_le (by exact WithTop.coe_le_coe.2 le_top)
    have : (Function.uncurry fun L' θ' => L' - gFun κ θ') = fun p : ℝ × ℝ => p.1 - gFun κ p.2 := by
      funext p; rfl
    rw [this]
    exact contDiffOn_fst.sub (hg3.comp contDiffOn_snd fun p hp => hp.2)
  rw [dynkinGen_opDrift_angle hκ hc hφ hx, radGen_L_sub_gFun hκ L
    (NonSwallow.arg_mem_Ioo_of_im_pos (hc.trans_le hx)), mul_zero]

/-! ## The martingale and the expected drop of the log conformal radius -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The state region `{Im Z ≥ δ, lo ≤ L ≤ hi}`. -/
def arK (δ lo hi : ℝ) : Set (ℂ × ℝ) := {x | δ ≤ x.1.im ∧ lo ≤ x.2 ∧ x.2 ≤ hi}

theorem isClosed_arK (δ lo hi : ℝ) : IsClosed (arK δ lo hi) :=
  (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))

theorem tamedLogCR_ge {W : ℝ → ℝ} (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) {t : ℝ}
    (ht : 0 ≤ t) : Real.log a.im - 4 / c ^ 2 * t ≤ tamedLogCR W c a t := by
  rw [tamedLogCR]
  have hcont : ContinuousOn (fun s => tamedLField c (tamedZ W c a s)) (Icc 0 t) :=
    (continuous_tamedLField hc).comp_continuousOn (continuousOn_tamedZ hW hc ht a)
  have hint : IntervalIntegrable (fun s => tamedLField c (tamedZ W c a s)) volume 0 t :=
    hcont.intervalIntegrable_of_Icc ht
  have hmono := intervalIntegral.integral_mono_on ht intervalIntegrable_const hint
    (fun s _ => by
      show -(4 / c ^ 2) ≤ tamedLField c (tamedZ W c a s)
      rw [tamedLField_eq_neg_sq hc]
      have h := abs_im_two_div_proj_le hc (tamedZ W c a s)
      have h' : ((2 / proj c (tamedZ W c a s)).im) ^ 2 ≤ (2 / c) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have : (2 / c) ^ 2 = 4 / c ^ 2 := by ring
      linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  linarith

theorem tamedLogCR_le {W : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    tamedLogCR W c a t ≤ Real.log a.im := by
  rw [tamedLogCR]
  have h := intervalIntegral.integral_nonneg (μ := volume)
    (f := fun s => (2 / proj c (tamedZ W c a s)).im ^ 2) ht (fun u _ => sq_nonneg _)
  have e : (fun s => tamedLField c (tamedZ W c a s))
      = fun s => -((2 / proj c (tamedZ W c a s)).im ^ 2) :=
    funext fun s => tamedLField_eq_neg_sq hc _
  rw [e, intervalIntegral.integral_neg]
  linarith

/-- **The expected drop of the log conformal radius up to the freezing time** is at most
`2C`, where `C` bounds `|g|` (FD-8, κ ∈ (4,8)). -/
theorem integral_logCR_drop_le (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ}
    (hδa : δ ≤ a.im) (T : ℝ≥0) {C : ℝ} (hC : ∀ θ ∈ Ioo 0 Real.pi, |gFun κ θ| ≤ C) :
    Integrable (fun ω => Real.log a.im -
      (opProc κ B c a (frozenTime κ c δ T B a ω) ω).2) P ∧
    ∫ ω, (Real.log a.im - (opProc κ B c a (frozenTime κ c δ T B a ω) ω).2) ∂P ≤ 2 * C := by
  have hκ : 0 < κ := by linarith
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < δ := hc.trans_le hcδ
  set F : ℂ × ℝ → ℝ := fun y => (fun L' θ' => L' - gFun κ θ') y.2 (Complex.arg y.1) with hFdef
  set lo : ℝ := Real.log a.im - 4 / c ^ 2 * T with hlo
  have hKO : arK δ lo (Real.log a.im) ⊆ {x : ℂ × ℝ | 0 < x.1.im} := fun x hx => hδ.trans_le hx.1
  have hF : ContDiffOn ℝ 3 F {x : ℂ × ℝ | 0 < x.1.im} := fun x hx =>
    (contDiffAt_snd.sub ((contDiffAt_gFun_arg κ hx).of_le
      (by exact WithTop.coe_le_coe.2 le_top))).contDiffWithinAt
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, opProc κ B c a s ω ∉ {x : ℂ × ℝ | x.1.im ≤ δ}) →
      opProc κ B c a t ω ∈ arK δ lo (Real.log a.im) := by
    intro ω t htT h
    have hW := continuous_drive_path (κ := κ) hBc ω
    refine ⟨(fzU_mem_fzK hBc hc hδa ω htT fun s hs => h s hs).1, ?_, tamedLogCR_le hc a t.coe_nonneg⟩
    have h1 := tamedLogCR_ge hW hc a t.coe_nonneg
    have h2 : 4 / c ^ 2 * (t : ℝ) ≤ 4 / c ^ 2 * T :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast htT) (by positivity)
    show lo ≤ tamedLogCR _ c a t
    linarith
  have hFM : ∀ x ∈ arK δ lo (Real.log a.im), |F x| ≤ (|Real.log a.im| + 4 / c ^ 2 * T) + C := by
    intro x hx
    have hg := hC _ (NonSwallow.arg_mem_Ioo_of_im_pos (hδ.trans_le hx.1))
    have hx2 : |x.2| ≤ |Real.log a.im| + 4 / c ^ 2 * T := by
      have h4 : 0 ≤ 4 / c ^ 2 * (T : ℝ) := by positivity
      rw [abs_le]; constructor
      · have := neg_abs_le (Real.log a.im); linarith [hx.2.1]
      · have := le_abs_self (Real.log a.im); linarith [hx.2.2]
    show |x.2 - gFun κ (Complex.arg x.1)| ≤ _
    exact (abs_sub _ _).trans (add_le_add hx2 hg)
  have hM := martingale_localDynkin_stopped hB hBc 𝓕 hBad hpast (lipschitzWith_opDrift hc)
    (norm_opDrift_le hc) (opProc_integralEq hBc hc κ a) isOpen_fzO (isClosed_fzCl δ)
    (isClosed_arK δ lo (Real.log a.im)) hKO hF
    (fun x hx _ => dynkinGen_L_sub_gFun hκ hc (hcδ.trans hx.1)) T hUK hFM
  have hhit : ∀ ω, hittingBtwn (opProc κ B c a) {x : ℂ × ℝ | x.1.im ≤ δ} 0 T ω
      = frozenTime κ c δ T B a ω := fun ω => rfl
  simp only [hhit] at hM
  have hσ : ∀ ω, min T (frozenTime κ c δ T B a ω) = frozenTime κ c δ T B a ω :=
    fun ω => min_eq_right (hittingBtwn_le ω)
  have hg : Integrable (fun ω =>
      gFun κ (Complex.arg (opProc κ B c a (frozenTime κ c δ T B a ω) ω).1)) P :=
    (integral_frozenField_sq hB hBc 𝓕 hBad hpast hκ4 hκ8 hc hcδ hδa T).1
  have hMT := hM.integrable T
  simp only [hσ] at hMT
  have hpt : ∀ ω, Real.log a.im - (opProc κ B c a (frozenTime κ c δ T B a ω) ω).2
      = Real.log a.im - F (opProc κ B c a (frozenTime κ c δ T B a ω) ω)
        - gFun κ (Complex.arg (opProc κ B c a (frozenTime κ c δ T B a ω) ω).1) := fun ω => by
    simp only [hFdef]; ring
  have hint : Integrable (fun ω => Real.log a.im -
      (opProc κ B c a (frozenTime κ c δ T B a ω) ω).2) P := by
    simp only [hpt]
    exact ((integrable_const _).sub hMT).sub hg
  refine ⟨hint, ?_⟩
  have hsi : ∫ ω, F (opProc κ B c a (min T (frozenTime κ c δ T B a ω)) ω) ∂P
      = ∫ ω, F (opProc κ B c a (min 0 (frozenTime κ c δ T B a ω)) ω) ∂P := by
    have := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using this.symm
  have h0 : ∫ ω, F (opProc κ B c a (min 0 (frozenTime κ c δ T B a ω)) ω) ∂P
      = Real.log a.im - gFun κ (Complex.arg a) := by
    have hae : (fun ω => F (opProc κ B c a (min 0 (frozenTime κ c δ T B a ω)) ω))
        =ᵐ[P] fun _ => Real.log a.im - gFun κ (Complex.arg a) := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      rw [min_eq_left zero_le, opProc_integralEq hBc hc κ a ω 0]
      simp [hω, hFdef]
    rw [integral_congr_ae hae, integral_const]
    simp
  simp only [hσ] at hsi
  rw [h0] at hsi
  have e1 : ∫ ω, (Real.log a.im - F (opProc κ B c a (frozenTime κ c δ T B a ω) ω)
        - gFun κ (Complex.arg (opProc κ B c a (frozenTime κ c δ T B a ω) ω).1)) ∂P
      = ∫ ω, (Real.log a.im - F (opProc κ B c a (frozenTime κ c δ T B a ω) ω)) ∂P
        - ∫ ω, gFun κ (Complex.arg (opProc κ B c a (frozenTime κ c δ T B a ω) ω).1) ∂P :=
    integral_sub ((integrable_const _).sub hMT) hg
  have e2 : ∫ ω, (Real.log a.im - F (opProc κ B c a (frozenTime κ c δ T B a ω) ω)) ∂P
      = Real.log a.im - ∫ ω, F (opProc κ B c a (frozenTime κ c δ T B a ω) ω) ∂P := by
    have := integral_sub (integrable_const (Real.log a.im)) hMT
    rw [integral_const] at this
    simpa using this
  rw [funext hpt, e1, e2, hsi]
  have hga := hC _ (NonSwallow.arg_mem_Ioo_of_im_pos (hδ.trans_le hδa))
  have hlow : -C ≤ ∫ ω, gFun κ (Complex.arg (opProc κ B c a (frozenTime κ c δ T B a ω) ω).1) ∂P := by
    have h := integral_mono (integrable_const (-C)) hg fun ω => by
      have him := fzZ_im_ge hBc hc hδa (κ := κ) (T := T) ω le_rfl
      exact (abs_le.1 (hC _ (NonSwallow.arg_mem_Ioo_of_im_pos (hδ.trans_le him)))).1
    simpa using h
  have := (abs_le.1 hga).2
  linarith

end Thm11Area
end QuantumZipper
