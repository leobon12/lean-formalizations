import QuantumZipper.Proofs.LQG.BoundaryExistenceAS

/-!
# M4-P3: dyadic scaling toolkit and fractional moments of the boundary measure

Blueprint `M4_BLUEPRINT.md`, node M4-P3.

Fix a centre `t ∈ ℝ`, a scale `δ > 0` and `R` with `|t| + δ ≤ R`. For the normalized field
`Z = zField X R` we split `Z` inside `B(t, δ)` as
`Z_ρ(s) = Ω + Y_ρ(s)`, where `Ω = Z(fc(t,δ))` is the semicircle average at `(t, δ)` and
`Y = X − X(fc(t,δ))` is the *inner field*.

* (a) `innerProc X t δ` is the inner process indexed by `InnerQ` (coordinates
  `X(fc(t+δu, δr)) − X(fc(t,δ))`, `|u| + r ≤ 1`); it is independent of `Ω`
  (`indepFun_omega_innerSample`), and its law does not depend on `(t, δ)`:
  `map_innerProc_eq` (exact scaling, at the level of the Gaussian coordinates). The field
  `innerSample X t δ` rebuilt from it satisfies, almost surely, for every `k` and every `s` with
  `|s − t| + 2^{-k} < δ`, `Z_{2^{-k}}(s) = Ω + avgReg (innerSample) k s`
  (`ae_avgReg_zField_eq_inner`), hence
  `ν_{2^{-k}}(S) = e^{(γ/2)Ω} δ^{γ²/4} W_k(S)` (`ae_bdryApprox_eq_omega_mul`), where `W_k` is the
  rescaled inner mass, a function of the inner process only.
* (b) fractional moments of `ν_{2^{-k}}(S)`, `S = [t − δ/2, t + δ/2]`, for fixed `k` and with
  `sup_k` inside the expectation.
* (c) the same for the limit measure `qBoundaryMeasure` (open interval, Fatou).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace FracMom

open GaussTK TwoRadius BdryExist KernelId

/-- Index set of the inner field: `(u, r)` with `r > 0` and `|u| + r ≤ 1`. -/
abbrev InnerQ := {q : ℝ × ℝ // 0 < q.2 ∧ |q.1| + q.2 ≤ 1}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The inner process `Y_q = X(fc(t+δu, δr)) − X(fc(t,δ))`, `q = (u, r)`. -/
def innerProc (X : Ω → FieldSample) (t δ : ℝ) (ω : Ω) : InnerQ → ℝ :=
  fun q => fcPairVal X (innerIdx t δ q.1.1 q.1.2) ω

/-- The folded circle attached to the index `q` at `(t, δ)`. -/
def innerMeas (t δ : ℝ) (q : InnerQ) : Measure ℂ :=
  foldedCircle (((t + δ * q.1.1 : ℝ)) : ℂ) (δ * q.1.2)

open Classical in
/-- Rebuild a field sample from inner coordinates (junk `0` off the inner circles). -/
def innerRebuild (t δ : ℝ) (y : InnerQ → ℝ) : FieldSample := fun μ =>
  if h : ∃ q : InnerQ, innerMeas t δ q = μ then y h.choose else 0

/-- The inner field sample, a function of the inner process only. -/
def innerSample (X : Ω → FieldSample) (t δ : ℝ) (ω : Ω) : FieldSample :=
  innerRebuild t δ (innerProc X t δ ω)

/-- The semicircle average `Ω = Z(fc(t,δ))` of the normalized field. -/
def omegaAvg (X : Ω → FieldSample) (R t δ : ℝ) (ω : Ω) : ℝ :=
  fcPairVal X ((t : ℂ), δ, 0, R) ω

/-- Inner coordinate `Y_{2^{-k}}(s)`. -/
def iU (X : Ω → FieldSample) (t δ : ℝ) (k : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  avgReg (innerSample X t δ ω) k (s : ℂ)

theorem measurable_innerRebuild (t δ : ℝ) : Measurable (innerRebuild t δ) := by
  refine measurable_pi_iff.mpr fun μ => ?_
  by_cases h : ∃ q : InnerQ, innerMeas t δ q = μ
  · have e : (fun y : InnerQ → ℝ => innerRebuild t δ y μ) = fun y => y h.choose := by
      funext y; simp only [innerRebuild, dif_pos h]
    rw [e]; exact measurable_pi_apply _
  · have e : (fun y : InnerQ → ℝ => innerRebuild t δ y μ) = fun _ => 0 := by
      funext y; simp only [innerRebuild, dif_neg h]
    rw [e]; exact measurable_const

theorem measurable_innerProc (hX : IsFreeGFFModConstH X P) (t δ : ℝ) :
    Measurable (innerProc X t δ) :=
  measurable_pi_iff.mpr fun q => measurable_fcPairVal hX _

theorem measurable_innerSample (hX : IsFreeGFFModConstH X P) (t δ : ℝ) :
    Measurable (innerSample X t δ) :=
  (measurable_innerRebuild t δ).comp (measurable_innerProc hX t δ)

theorem measurable_omegaAvg (hX : IsFreeGFFModConstH X P) (R t δ : ℝ) :
    Measurable (omegaAvg X R t δ) :=
  measurable_fcPairVal hX _

theorem measurable_iU (hX : IsFreeGFFModConstH X P) (t δ : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => iU X t δ k p.1 p.2) :=
  (measurable_avgReg k).comp (((measurable_innerSample hX t δ).comp measurable_snd).prodMk
    (Complex.continuous_ofReal.measurable.comp measurable_fst))

theorem innerSample_apply (t δ : ℝ) (ω : Ω) (q : InnerQ) :
    innerSample X t δ ω (innerMeas t δ q) =
      X ω (innerMeas t δ q) - X ω (foldedCircle (t : ℂ) δ) := by
  have h : ∃ q' : InnerQ, innerMeas t δ q' = innerMeas t δ q := ⟨q, rfl⟩
  have e : innerSample X t δ ω (innerMeas t δ q) =
      fcPairVal X (innerIdx t δ h.choose.1.1 h.choose.1.2) ω := by
    simp only [innerSample, innerRebuild, dif_pos h, innerProc]
  rw [e]
  show X ω (innerMeas t δ h.choose) - X ω (foldedCircle (t : ℂ) δ) = _
  rw [h.choose_spec]

theorem dyadicRoundC_ofReal (j : ℕ) (s : ℝ) :
    dyadicRoundC j (s : ℂ) = ((dyadicRound j s : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [dyadicRoundC]
  · simp only [dyadicRoundC, Complex.ofReal_im]
    simp [dyadicRound]

/-- Pathwise: if the dyadic roundings of `X ω` converge at `s`, then the inner field's
regularized average at `s` is `avgReg (X ω) k s − X ω (fc(t,δ))`. -/
theorem avgReg_innerSample_eq {t δ s : ℝ} {k : ℕ} (hδ : 0 < δ) (hs : |s - t| + radius k < δ)
    {ω : Ω} (hlim : Tendsto (fun j => X ω (foldedCircle (dyadicRoundC j (s : ℂ)) (radius k)))
      atTop (𝓝 (avgReg (X ω) k (s : ℂ)))) :
    avgReg (innerSample X t δ ω) k (s : ℂ) =
      avgReg (X ω) k (s : ℂ) - X ω (foldedCircle (t : ℂ) δ) := by
  have hr := radius_pos k
  have hε : 0 < δ - |s - t| - radius k := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, (1 / 2 : ℝ) ^ j < δ - |s - t| - radius k :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).eventually
      (gt_mem_nhds hε)
  have heq : ∀ᶠ j : ℕ in atTop,
      X ω (foldedCircle (dyadicRoundC j (s : ℂ)) (radius k)) - X ω (foldedCircle (t : ℂ) δ) =
        innerSample X t δ ω (foldedCircle (dyadicRoundC j (s : ℂ)) (radius k)) := by
    filter_upwards [hev] with j hj
    set d := dyadicRound j s with hd
    have hds : |d - s| ≤ 1 / 2 ^ j := CircleCont.abs_dyadicRound_sub_le j s
    rw [one_div_pow] at hj
    have hdt : |d - t| ≤ |d - s| + |s - t| := by
      have := abs_add_le (d - s) (s - t); rwa [sub_add_sub_cancel] at this
    have hq : 0 < radius k / δ ∧ |(d - t) / δ| + radius k / δ ≤ 1 := by
      refine ⟨div_pos hr hδ, ?_⟩
      rw [abs_div, abs_of_pos hδ, ← add_div, div_le_one hδ]
      linarith
    let q : InnerQ := ⟨((d - t) / δ, radius k / δ), hq⟩
    have hm : innerMeas t δ q = foldedCircle (dyadicRoundC j (s : ℂ)) (radius k) := by
      simp only [innerMeas, q, dyadicRoundC_ofReal, ← hd]
      congr 1
      · congr 1; field_simp; ring
      · field_simp
    rw [← hm, innerSample_apply]
  have ht : Tendsto (fun j => innerSample X t δ ω (foldedCircle (dyadicRoundC j (s : ℂ))
      (radius k))) atTop (𝓝 (avgReg (X ω) k (s : ℂ) - X ω (foldedCircle (t : ℂ) δ))) :=
    (hlim.sub_const _).congr' heq
  exact ht.limUnder_eq

/-- Almost surely, for all `s` with `|s − t| + 2^{-k} < δ`, `Z_{2^{-k}}(s) = Ω + Y_{2^{-k}}(s)`. -/
theorem ae_avgReg_zField_eq_inner (hX : IsFreeGFFModConstH X P) (R : ℝ) {t δ : ℝ}
    (hδ : 0 < δ) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, |s - t| + radius k < δ →
      avgReg (zField X R ω) k (s : ℂ) = omegaAvg X R t δ ω + iU X t δ k s ω := by
  filter_upwards [(ae_avgReg_spec hX k).1, ae_avgReg_zField hX R k] with ω h1 h2 s hs
  rw [h2 _ (ofReal_mem_Hbar s), iU, avgReg_innerSample_eq hδ hs (h1 _ (ofReal_mem_Hbar s)),
    omegaAvg, fcPairVal]
  ring

/-- At a fixed point, `Y_{2^{-k}}(s)` is a.s. the raw pair value `X(fc(s,2^{-k})) − X(fc(t,δ))`. -/
theorem iU_ae_eq (hX : IsFreeGFFModConstH X P) {t δ : ℝ} (hδ : 0 < δ) (k : ℕ) {s : ℝ}
    (hs : |s - t| + radius k < δ) :
    iU X t δ k s =ᵐ[P] fcPairVal X ((s : ℂ), radius k, (t : ℂ), δ) := by
  filter_upwards [(ae_avgReg_spec hX k).1, (ae_avgReg_spec hX k).2 _ (ofReal_mem_Hbar s)]
    with ω h1 h2
  rw [iU, avgReg_innerSample_eq hδ hs (h1 _ (ofReal_mem_Hbar s)), h2, fcPairVal]

/-! ### Covariances -/

theorem fcPairCov_innerU_self {s t ρ δ : ℝ} (hρ : 0 < ρ) (h : |s - t| + ρ ≤ δ) :
    fcPairCov ((s : ℂ), ρ, (t : ℂ), δ) ((s : ℂ), ρ, (t : ℂ), δ) = 2 * log δ - 2 * log ρ := by
  have hδ : 0 < δ := by linarith [abs_nonneg (s - t)]
  have h' : |s - t| + ρ ≤ δ := h
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hρ hρ, kernelCov_fc_real_nested' hρ h',
    kernelCov_fc_real_nested hρ h', kernelCov_fc_real_sameCenter hδ hδ, max_self, max_self]
  ring

theorem fcPairCov_incr_innerU_same {s t ρ δ : ℝ} (hρ : 0 < ρ) (h : |s - t| + ρ ≤ δ) :
    fcPairCov ((s : ℂ), ρ / 2, (s : ℂ), ρ) ((s : ℂ), ρ, (t : ℂ), δ) = 0 := by
  have hρ2 : 0 < ρ / 2 := by positivity
  have h2 : |s - t| + ρ / 2 ≤ δ := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hρ2 hρ, kernelCov_fc_real_nested' hρ2 h2,
    kernelCov_fc_real_sameCenter hρ hρ, kernelCov_fc_real_nested' hρ h,
    max_eq_right (by linarith : ρ / 2 ≤ ρ), max_self]
  ring

theorem fcPairCov_incr_innerU_far {s u t ρ δ : ℝ} (hρ : 0 < ρ) (hs : |s - t| + ρ ≤ δ)
    (hsu : 2 * ρ ≤ |s - u|) :
    fcPairCov ((s : ℂ), ρ / 2, (s : ℂ), ρ) ((u : ℂ), ρ, (t : ℂ), δ) = 0 := by
  have hρ2 : 0 < ρ / 2 := by positivity
  have h2 : |s - t| + ρ / 2 ≤ δ := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_separated hρ2 hρ (by linarith), kernelCov_fc_real_nested' hρ2 h2,
    kernelCov_fc_real_separated hρ hρ (by linarith), kernelCov_fc_real_nested' hρ hs]
  ring

/-! ### The two-radius hypotheses for the inner field -/

/-- Variance of `Y_{2^{-k}}(s)`. -/
def vI (δ : ℝ) (k : ℕ) : ℝ≥0 := (2 * log δ - 2 * log (radius k)).toNNReal

theorem radius_succ_lt (k : ℕ) : radius (k + 1) < radius k := by
  rw [radius_succ]; linarith [radius_pos k]

/-- **`TRLHyp` for the inner field** at the radii `2^{-k}` (coarse) and `2^{-k-1}` (fine), with
`L = log (δ / 2^{-k})` and `K = 0`. -/
theorem trlHyp_inner (hX : IsFreeGFFModConstH X P) {t δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (k : ℕ) (hS : ∀ s ∈ S, |s - t| + radius k < δ) :
    TRLHyp P S (2 * radius k) 0 (2 * log 2) (fun _ => log (δ / radius k))
      (fun _ => vI δ k) (fun _ => (2 * log 2).toNNReal) (iU X t δ k)
      (fun s ω => iU X t δ (k + 1) s ω - iU X t δ k s ω) := by
  have hr := radius_pos k
  have hlog2 : (0 : ℝ) ≤ 2 * log 2 := mul_nonneg zero_le_two (log_nonneg one_le_two)
  have hS1 : ∀ s ∈ S, |s - t| + radius (k + 1) < δ := fun s hs =>
    lt_of_le_of_lt (by linarith [radius_succ_lt k]) (hS s hs)
  have hΔe : ∀ s ∈ S, (fun ω => iU X t δ (k + 1) s ω - iU X t δ k s ω) =ᵐ[P]
      fcPairVal X ((s : ℂ), radius k / 2, (s : ℂ), radius k) := by
    intro s hs
    filter_upwards [iU_ae_eq hX hδ (k + 1) (hS1 s hs), iU_ae_eq hX hδ k (hS s hs)] with ω h1 h2
    simp only [h1, h2, fcPairVal, radius_succ]
    ring
  refine
    { measU := measurable_iU hX t δ k
      measΔ := (measurable_iU hX t δ (k + 1)).sub (measurable_iU hX t δ k)
      measL := measurable_const
      measw := measurable_const
      lawU := ?_, lawΔ := ?_, varU := ?_, varΔ := ?_, indep := ?_, decor := ?_ }
  · intro s hs
    have := (hasLaw_fcPairVal hX (good_real (s := s) (t := t) hr hδ)).congr
      (iU_ae_eq hX hδ k (hS s hs))
    rwa [fcPairCov_innerU_self hr (hS s hs).le] at this
  · intro s hs
    have := (hasLaw_fcPairVal hX (good_real (s := s) (t := s) (by positivity) hr)).congr
      (hΔe s hs)
    rwa [fcPairCov_incr_self hr] at this
  · intro s hs
    have hrδ : radius k < δ := lt_of_le_of_lt (by linarith [abs_nonneg (s - t)]) (hS s hs)
    show ((2 * log δ - 2 * log (radius k)).toNNReal : ℝ) ≤ 2 * log (δ / radius k) + 0
    rw [Real.coe_toNNReal _ (by linarith [log_le_log hr hrδ.le]), log_div hδ.ne' hr.ne']
    linarith
  · intro s _
    exact (Real.coe_toNNReal _ hlog2).le
  · intro s hs
    have hI := indepFun_fcPair hX
      (fun _ : Unit => (⟨((s : ℂ), radius k / 2, (s : ℂ), radius k),
        good_real (by positivity) hr⟩ : {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨((s : ℂ), radius k, (t : ℂ), δ),
        good_real hr hδ⟩ : {p : FcIdx // p.Good}))
      (fun _ _ => fcPairCov_incr_innerU_same hr (hS s hs).le)
    have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
    exact hI2.congr (hΔe s hs).symm (iU_ae_eq hX hδ k (hS s hs)).symm
  · intro s hs u hu hsu
    have hg : ∀ i : Fin 3, FcIdx.Good
        (![((s : ℂ), radius k, (t : ℂ), δ), ((u : ℂ), radius k, (t : ℂ), δ),
          ((u : ℂ), radius k / 2, (u : ℂ), radius k)] i) := by
      intro i; fin_cases i
      · exact good_real hr hδ
      · exact good_real hr hδ
      · exact good_real (by positivity) hr
    have hI := indepFun_fcPair hX
      (fun _ : Unit => (⟨((s : ℂ), radius k / 2, (s : ℂ), radius k),
        good_real (by positivity) hr⟩ : {p : FcIdx // p.Good}))
      (fun i : Fin 3 => (⟨_, hg i⟩ : {p : FcIdx // p.Good})) (by
        intro _ i
        fin_cases i
        · exact fcPairCov_incr_innerU_same hr (hS s hs).le
        · exact fcPairCov_incr_innerU_far hr (hS s hs).le hsu
        · exact fcPairCov_incr_incr_far (by positivity) (by linarith) (by positivity)
            (by linarith) (by linarith))
    have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    have hI2 := hI.comp (measurable_pi_apply ()) hφ
    refine hI2.congr (hΔe s hs).symm ?_
    filter_upwards [iU_ae_eq hX hδ k (hS s hs), iU_ae_eq hX hδ k (hS u hu), hΔe u hu]
      with ω h1 h2 h3
    simp [h1, h2, ← h3]

/-! ### Multiplicative decomposition `ν_{2^{-k}}(S) = e^{(γ/2)Ω} δ^{γ²/4} W_k` -/

/-- The window `S = [t − δ/2, t + δ/2]`. -/
def bI (t δ : ℝ) : Set ℝ := Set.Icc (t - δ / 2) (t + δ / 2)

theorem mem_bI_bound {t δ s : ℝ} {k : ℕ} (hs : s ∈ bI t δ) (hk : 2 * radius k < δ) :
    |s - t| + radius k < δ := by
  have : |s - t| ≤ δ / 2 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  linarith

theorem measurableSet_bI (t δ : ℝ) : MeasurableSet (bI t δ) := measurableSet_Icc

theorem volume_bI {t δ : ℝ} (hδ : 0 ≤ δ) : volume (bI t δ) = ENNReal.ofReal δ := by
  rw [bI, Real.volume_Icc]; congr 1; ring

/-- Rescaled density `(2^{-k}/δ)^{γ²/4} e^{(γ/2) avgReg x k s}` of a field sample `x`. -/
def wDens (γ δ : ℝ) (k : ℕ) (x : FieldSample) (s : ℝ) : ℝ :=
  (radius k / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg x k (s : ℂ))

/-- The rescaled mass `W_k(x) = ∫_S wDens` (as an extended real). -/
def massFun (γ t δ : ℝ) (k : ℕ) (x : FieldSample) : ℝ≥0∞ :=
  ∫⁻ s in bI t δ, ENNReal.ofReal (wDens γ δ k x s)

/-- The rescaled inner mass `W_k = massFun (innerSample)`: a function of the inner process. -/
def innerMass (γ : ℝ) (X : Ω → FieldSample) (t δ : ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  massFun γ t δ k (innerSample X t δ ω)

theorem measurable_wDens₂ (γ δ : ℝ) (k : ℕ) :
    Measurable (fun p : FieldSample × ℝ => wDens γ δ k p.1 p.2) :=
  measurable_const.mul (((measurable_avgReg k).comp (measurable_fst.prodMk
    (Complex.continuous_ofReal.measurable.comp measurable_snd))).const_mul _).exp

theorem measurable_massFun (γ t δ : ℝ) (k : ℕ) : Measurable (massFun γ t δ k) :=
  (ENNReal.measurable_ofReal.comp (measurable_wDens₂ γ δ k)).lintegral_prod_right'

theorem measurable_innerMass (hX : IsFreeGFFModConstH X P) (γ t δ : ℝ) (k : ℕ) :
    Measurable (innerMass γ X t δ k) :=
  (measurable_massFun γ t δ k).comp (measurable_innerSample hX t δ)

/-- Deterministic decomposition: if `avgReg x k = c + avgReg y k` on `S`, then
`ν_{2^{-k}}(x)(S) = e^{(γ/2)c} δ^{γ²/4} W_k(y)`. -/
theorem bdryApprox_bI_eq_of (γ : ℝ) {t δ : ℝ} (hδ : 0 < δ) (k : ℕ) (x y : FieldSample) (c : ℝ)
    (hxy : ∀ s ∈ bI t δ, avgReg x k (s : ℂ) = c + avgReg y k (s : ℂ)) :
    bdryApprox γ x k (bI t δ) =
      ENNReal.ofReal (exp (γ / 2 * c) * δ ^ (γ ^ 2 / 4)) * massFun γ t δ k y := by
  have hU : Measurable (fun s : ℝ => avgReg y k (s : ℂ)) :=
    (measurable_avgReg k).comp (measurable_const.prodMk Complex.continuous_ofReal.measurable)
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (wDens γ δ k y s)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hU.const_mul _).exp)
  rw [bdryApprox, withDensity_apply _ (measurableSet_bI t δ), massFun,
    ← lintegral_const_mul _ hm]
  refine setLIntegral_congr_fun (measurableSet_bI t δ) fun s hs => ?_
  have hδa : 0 < δ ^ (γ ^ 2 / 4) := rpow_pos_of_pos hδ _
  have e : radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg x k (s : ℂ)) =
      (exp (γ / 2 * c) * δ ^ (γ ^ 2 / 4)) * wDens γ δ k y s := by
    rw [hxy s hs, wDens, div_rpow (radius_pos k).le hδ.le, mul_add, exp_add]
    field_simp
  show ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg x k (s : ℂ))) = _
  rw [e, ENNReal.ofReal_mul (mul_pos (exp_pos _) hδa).le]

/-- **Decomposition (a), at the level of masses.** Almost surely, for every `k` with
`2·2^{-k} < δ`, `ν_{2^{-k}}(S) = e^{(γ/2)Ω} δ^{γ²/4} W_k`. -/
theorem ae_bdryApprox_eq_omega_mul (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {t δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, 2 * radius k < δ →
      bdryApprox γ (zField X R ω) k (bI t δ) =
        ENNReal.ofReal (exp (γ / 2 * omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 4)) *
          innerMass γ X t δ k ω := by
  have h : ∀ k, ∀ᵐ ω ∂P, ∀ s : ℝ, |s - t| + radius k < δ →
      avgReg (zField X R ω) k (s : ℂ) = omegaAvg X R t δ ω + iU X t δ k s ω :=
    fun k => ae_avgReg_zField_eq_inner hX R hδ k
  rw [← ae_all_iff] at h
  filter_upwards [h] with ω hω k hk
  exact bdryApprox_bI_eq_of γ hδ k _ _ _ fun s hs => hω k s (mem_bI_bound hs hk)

/-! ### Moments -/

theorem hasLaw_iU (hX : IsFreeGFFModConstH X P) {t δ : ℝ} (hδ : 0 < δ) (k : ℕ) {s : ℝ}
    (hs : |s - t| + radius k < δ) :
    HasLaw (iU X t δ k s) (gaussianReal 0 (vI δ k)) P := by
  have := (hasLaw_fcPairVal hX (good_real (s := s) (t := t) (radius_pos k) hδ)).congr
    (iU_ae_eq hX hδ k hs)
  rwa [fcPairCov_innerU_self (radius_pos k) hs.le] at this

theorem integrable_wDens_inner (hX : IsFreeGFFModConstH X P) (γ : ℝ) {t δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) {s : ℝ} (hs : |s - t| + radius k < δ) :
    Integrable (fun ω => wDens γ δ k (innerSample X t δ ω) s) P := by
  have hL := hasLaw_iU hX hδ k hs
  have hi : Integrable (fun ω => exp (0 + γ / 2 * iU X t δ k s ω)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (γ / 2) 0)
  simp only [zero_add] at hi
  exact hi.const_mul _

/-- `E[wDens] = 1` exactly (`Var Y_{2^{-k}}(s) = 2 log (δ/2^{-k})`). -/
theorem integral_wDens_inner (hX : IsFreeGFFModConstH X P) (γ : ℝ) {t δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) {s : ℝ} (hs : |s - t| + radius k < δ) :
    ∫ ω, wDens γ δ k (innerSample X t δ ω) s ∂P = 1 := by
  have hL := hasLaw_iU hX hδ k hs
  have hr := radius_pos k
  have hrδ : radius k < δ := lt_of_le_of_lt (by linarith [abs_nonneg (s - t)]) hs
  have h2 := integral_exp_mul_add_gaussianReal (vI δ k) (γ / 2) 0
  simp only [zero_add] at h2
  have h3 : ∫ ω, exp (γ / 2 * iU X t δ k s ω) ∂P = exp (vI δ k * (γ / 2) ^ 2 / 2) := by
    rw [← h2]; exact hL.integral_comp (f := fun x => exp (γ / 2 * x)) (by fun_prop)
  simp only [wDens]
  rw [integral_const_mul]
  change (radius k / δ) ^ (γ ^ 2 / 4) * ∫ ω, exp (γ / 2 * iU X t δ k s ω) ∂P = 1
  rw [h3, vI, Real.coe_toNNReal _ (by linarith [log_le_log hr hrδ.le]),
    rpow_def_of_pos (div_pos hr hδ), ← exp_add, log_div hr.ne' hδ.ne']
  rw [← exp_zero]; congr 1; ring

/-- `E W_k = |S| = δ`. -/
theorem lintegral_innerMass [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {t δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 2 * radius k < δ) :
    ∫⁻ ω, innerMass γ X t δ k ω ∂P = ENNReal.ofReal δ := by
  have hU : Measurable (fun q : Ω × ℝ => avgReg (innerSample X t δ q.1) k (q.2 : ℂ)) :=
    (measurable_avgReg k).comp (((measurable_innerSample hX t δ).comp measurable_fst).prodMk
      (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hmeas : Measurable (fun q : Ω × ℝ =>
      ENNReal.ofReal (wDens γ δ k (innerSample X t δ q.1) q.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hU.const_mul _).exp)
  simp only [innerMass, massFun]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  rw [setLIntegral_congr_fun (g := fun _ => 1) (measurableSet_bI t δ) fun s hs => ?_]
  · rw [setLIntegral_const, one_mul, volume_bI hδ.le]
  · simp only
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_wDens_inner hX γ hδ k (mem_bI_bound hs hk))
      (ae_of_all _ fun ω => mul_nonneg (rpow_nonneg (div_nonneg (radius_pos k).le hδ.le) _)
        (exp_pos _).le),
      integral_wDens_inner hX γ hδ k (mem_bI_bound hs hk), ENNReal.ofReal_one]

/-- Jensen for `x ↦ x^p`, `p ∈ (0,1]`, on a probability space. -/
theorem lintegral_rpow_le_rpow_lintegral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫⁻ ω, f ω ^ p ∂μ ≤ (∫⁻ ω, f ω ∂μ) ^ p := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le hp0 hp1 μ hf.aestronglyMeasurable
  simp only [eLpNorm', enorm_eq_self, ENNReal.rpow_one, div_one] at h
  calc ∫⁻ ω, f ω ^ p ∂μ = ((∫⁻ ω, f ω ^ p ∂μ) ^ (1 / p)) ^ p := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow h hp0.le

theorem hasLaw_omegaAvg (hX : IsFreeGFFModConstH X P) {R t δ : ℝ} (hδ : 0 < δ)
    (hR : |t| + δ ≤ R) :
    HasLaw (omegaAvg X R t δ) (gaussianReal 0 (2 * log R - 2 * log δ).toNNReal) P := by
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  have := hasLaw_fcPairVal hX (good_Z (ofReal_mem_Hbar t) hδ hR0)
  rwa [fcPairCov_Zself hδ hR] at this

/-- `E[(e^{(γ/2)Ω} δ^{γ²/4})^p] = δ^{pγ²/4} e^{Var Ω · (pγ/2)²/2}`. -/
theorem lintegral_omega_factor_rpow (hX : IsFreeGFFModConstH X P) (γ : ℝ) {R t δ p : ℝ}
    (hδ : 0 < δ) (hR : |t| + δ ≤ R) (hp0 : 0 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (exp (γ / 2 * omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 4)) ^ p ∂P =
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) := by
  have hL := hasLaw_omegaAvg hX hδ hR
  set v := (2 * log R - 2 * log δ).toNNReal
  have hpt : ∀ ω, ENNReal.ofReal (exp (γ / 2 * omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 4)) ^ p =
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) * exp (p * γ / 2 * omegaAvg X R t δ ω)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0, mul_rpow (exp_pos _).le
      (rpow_pos_of_pos hδ _).le, ← exp_mul, ← rpow_mul hδ.le, mul_comm]
    congr 3 <;> ring
  simp_rw [hpt]
  have hi : Integrable (fun ω => exp (0 + p * γ / 2 * omegaAvg X R t δ ω)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (p * γ / 2) 0)
  simp only [zero_add] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
    (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; positivity), integral_const_mul]
  have h2 := integral_exp_mul_add_gaussianReal v (p * γ / 2) 0
  simp only [zero_add] at h2
  rw [← h2]
  congr 2
  exact hL.integral_comp (f := fun x => exp (p * γ / 2 * x)) (by fun_prop)

theorem indepFun_omega_innerSample (hX : IsFreeGFFModConstH X P) {R t δ : ℝ} (hδ : 0 < δ)
    (hR : |t| + δ ≤ R) : IndepFun (omegaAvg X R t δ) (innerSample X t δ) P :=
  (indepFun_inner hX (P := P) hδ hR).symm.comp (measurable_pi_apply ())
    (measurable_innerRebuild t δ)

/-! ### Increments of the inner masses (two-radius lemma) and the `sup` bound -/

theorem radius_add_le (k m : ℕ) : radius (k + m) ≤ radius k := by
  induction m with
  | zero => simp
  | succ m ih => exact (radius_succ_lt (k + m)).le.trans ih

theorem wDens_nonneg (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (x : FieldSample) (s : ℝ) :
    0 ≤ wDens γ δ k x s :=
  mul_nonneg (rpow_nonneg (div_nonneg (radius_pos k).le hδ.le) _) (exp_pos _).le

theorem measurable_wDens_slice (γ δ : ℝ) (k : ℕ) (x : FieldSample) :
    Measurable (fun s : ℝ => wDens γ δ k x s) := by
  have hU : Measurable (fun s : ℝ => avgReg x k (s : ℂ)) :=
    (measurable_avgReg k).comp (measurable_const.prodMk Complex.continuous_ofReal.measurable)
  exact measurable_const.mul (hU.const_mul _).exp

theorem integrable_innerMass_toReal [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {t δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 2 * radius k < δ) :
    Integrable (fun ω => (innerMass γ X t δ k ω).toReal) P :=
  integrable_toReal_of_lintegral_ne_top (measurable_innerMass hX γ t δ k).aemeasurable
    (by rw [lintegral_innerMass hX γ hδ hk]; exact ENNReal.ofReal_ne_top)

theorem ae_innerMass_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {t δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 2 * radius k < δ) :
    ∀ᵐ ω ∂P, innerMass γ X t δ k ω < ⊤ :=
  ae_lt_top (measurable_innerMass hX γ t δ k)
    (by rw [lintegral_innerMass hX γ hδ hk]; exact ENNReal.ofReal_ne_top)

/-- For a sample with finite mass, `W_k` is the (Bochner) integral of the density. -/
theorem integrableOn_wDens_of_massFun_lt_top (γ : ℝ) {t δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    {x : FieldSample} (hx : massFun γ t δ k x < ⊤) :
    IntegrableOn (fun s => wDens γ δ k x s) (bI t δ) ∧
      ∫ s in bI t δ, wDens γ δ k x s = (massFun γ t δ k x).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (bI t δ)] fun s => wDens γ δ k x s :=
    ae_of_all _ fun s => wDens_nonneg γ hδ k x s
  have hm := (measurable_wDens_slice γ δ k x).aestronglyMeasurable
    (μ := volume.restrict (bI t δ))
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 hx⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm]
  rfl

/-- The constant of the increment bound. -/
def cInc (γ : ℝ) : ℝ := 2 * √(1 + exp (γ ^ 2 / 4 * (2 * log 2))) + 2

theorem cInc_nonneg (γ : ℝ) : 0 ≤ cInc γ := by unfold cInc; positivity

/-- **Increment bound (via the two-radius lemma, scaled down by the inner-field
decomposition).** `E|W_k − W_{k+1}| ≤ cInc · δ · (δ/2^{-k})^{-β}`, `β = bdryRate γ`. -/
theorem integral_abs_innerMass_step_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {t δ : ℝ} (hδ : 0 < δ) {k : ℕ}
    (hk : 2 * radius k < δ) :
    ∫ ω, |(innerMass γ X t δ k ω).toReal - (innerMass γ X t δ (k + 1) ω).toReal| ∂P ≤
      cInc γ * δ * exp (-bdryRate γ * log (δ / radius k)) := by
  have hr := radius_pos k
  have hrδ : radius k < δ := by linarith
  have hk1 : 2 * radius (k + 1) < δ := lt_of_le_of_lt (by linarith [radius_succ_lt k]) hk
  have hlog2 : (0 : ℝ) ≤ 2 * log 2 := mul_nonneg zero_le_two (log_nonneg one_le_two)
  set L := log (δ / radius k) with hL
  have hL0 : 0 ≤ L := log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have h := trlHyp_inner hX (P := P) hδ (S := bI t δ) k fun s hs => mem_bI_bound hs hk
  have hb := trl_bound hγ hγ2 (f := fun _ => 1) (M := 1) (Lmin := L) (Lmax := L)
    (by positivity) (measurableSet_bI t δ) (by rw [volume_bI hδ.le]; exact ENNReal.ofReal_lt_top)
    measurable_const (fun _ => by simp) h (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have hpt : ∀ s ω, trlD γ (fun _ => (1 : ℝ)) (fun _ => L) (fun _ => (2 * log 2).toNNReal)
      (iU X t δ k) (fun s ω => iU X t δ (k + 1) s ω - iU X t δ k s ω) s ω =
      wDens γ δ k (innerSample X t δ ω) s - wDens γ δ (k + 1) (innerSample X t δ ω) s := by
    intro s ω
    simp only [trlD, tiltY, wDens, iU, one_mul]
    rw [Real.coe_toNNReal _ hlog2, radius_succ, rpow_def_of_pos (div_pos hr hδ),
      rpow_def_of_pos (div_pos (div_pos hr two_pos) hδ), log_div (div_pos hr two_pos).ne' hδ.ne',
      log_div hr.ne' two_ne_zero, log_div hr.ne' hδ.ne', hL, log_div hδ.ne' hr.ne',
      mul_sub, mul_one, ← exp_add, ← exp_add, ← exp_add]
    congr 1 <;> congr 1 <;> ring
  have hae : ∀ᵐ ω ∂P, ∫ s in bI t δ, trlD γ (fun _ => (1 : ℝ)) (fun _ => L)
      (fun _ => (2 * log 2).toNNReal) (iU X t δ k)
      (fun s ω => iU X t δ (k + 1) s ω - iU X t δ k s ω) s ω =
      (innerMass γ X t δ k ω).toReal - (innerMass γ X t δ (k + 1) ω).toReal := by
    filter_upwards [ae_innerMass_lt_top hX γ hδ hk, ae_innerMass_lt_top hX γ hδ hk1]
      with ω h1 h2
    obtain ⟨i1, e1⟩ := integrableOn_wDens_of_massFun_lt_top γ hδ k h1
    obtain ⟨i2, e2⟩ := integrableOn_wDens_of_massFun_lt_top γ hδ (k + 1) h2
    simp_rw [hpt]
    rw [integral_sub i1 i2, e1, e2]
    rfl
  have hEq : (fun ω => |(innerMass γ X t δ k ω).toReal - (innerMass γ X t δ (k + 1) ω).toReal|)
      =ᵐ[P] fun ω => |∫ s in bI t δ, trlD γ (fun _ => (1 : ℝ)) (fun _ => L)
        (fun _ => (2 * log 2).toNNReal) (iU X t δ k)
        (fun s ω => iU X t δ (k + 1) s ω - iU X t δ k s ω) s ω| :=
    hae.mono fun ω hω => by dsimp only; rw [hω]
  refine (le_of_eq (integral_congr_ae hEq)).trans (hb.trans ?_)
  -- algebra
  set β := bdryRate γ with hβ
  set θ := max 0 ((3 * γ - 2) / 4) with hθ
  set E := 1 + exp (γ ^ 2 / 4 * (2 * log 2)) with hE
  have hβ1 : β ≤ (1 - γ ^ 2 / 2 + θ ^ 2) / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 16 := min_le_right _ _
  have hvol : volume.real (bI t δ) = δ := by
    rw [measureReal_def, volume_bI hδ.le, ENNReal.toReal_ofReal hδ.le]
  have hrad : radius k = δ * exp (-L) := by
    rw [exp_neg, hL, exp_log (div_pos hδ hr)]; field_simp
  rw [hvol, hrad]
  have hE0 : 0 ≤ E := by positivity
  have hin : (1 : ℝ) ^ 2 * (E * (exp ((γ - θ) ^ 2 * 0 / 2) * exp ((γ ^ 2 / 2 - θ ^ 2) * L))) *
      (2 * (2 * (δ * exp (-L))) * δ) ≤ (2 * √E * δ * exp (-β * L)) ^ 2 := by
    have e1 : exp ((γ ^ 2 / 2 - θ ^ 2) * L) * exp (-L) ≤ exp (-β * L) ^ 2 := by
      rw [← exp_add, ← exp_nat_mul]; apply exp_le_exp.2; push_cast; nlinarith
    have hsq : √E ^ 2 = E := sq_sqrt hE0
    calc (1 : ℝ) ^ 2 * (E * (exp ((γ - θ) ^ 2 * 0 / 2) * exp ((γ ^ 2 / 2 - θ ^ 2) * L))) *
          (2 * (2 * (δ * exp (-L))) * δ)
        = 4 * E * δ ^ 2 * (exp ((γ ^ 2 / 2 - θ ^ 2) * L) * exp (-L)) := by
          simp only [mul_zero, zero_div, exp_zero]; ring
      _ ≤ 4 * E * δ ^ 2 * exp (-β * L) ^ 2 :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = (2 * √E * δ * exp (-β * L)) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, hsq]; ring
  have ht1 := Real.sqrt_le_sqrt hin
  rw [Real.sqrt_sq (by positivity)] at ht1
  have ht2 : (1 : ℝ) * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * 0 / 2) *
      exp (-((2 - γ) ^ 2 / 16) * L))) * δ ≤ 2 * δ * exp (-β * L) := by
    have : exp (-((2 - γ) ^ 2 / 16) * L) ≤ exp (-β * L) := exp_le_exp.2 (by nlinarith)
    simp only [mul_zero, zero_div, exp_zero, one_mul]
    nlinarith [exp_pos (-((2 - γ) ^ 2 / 16) * L)]
  calc _ ≤ 2 * √E * δ * exp (-β * L) + 2 * δ * exp (-β * L) := add_le_add ht1 ht2
    _ = cInc γ * δ * exp (-β * L) := by rw [cInc, ← hE]; ring

/-- Telescoping in `ℝ≥0∞`: `sup_m a_m ≤ a_0 + Σ |a_i − a_{i+1}|` for finite `a`. -/
theorem iSup_le_add_tsum_abs_sub {a : ℕ → ℝ≥0∞} (ha : ∀ m, a m ≠ ⊤) :
    ⨆ m, a m ≤ a 0 + ∑' i, ENNReal.ofReal |(a i).toReal - (a (i + 1)).toReal| := by
  refine iSup_le fun m => ?_
  have key : ∀ m, (a m).toReal ≤
      (a 0).toReal + ∑ i ∈ Finset.range m, |(a i).toReal - (a (i + 1)).toReal| := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have := le_abs_self ((a (m + 1)).toReal - (a m).toReal)
      rw [abs_sub_comm] at this
      linarith
  calc a m = ENNReal.ofReal (a m).toReal := (ENNReal.ofReal_toReal (ha m)).symm
    _ ≤ ENNReal.ofReal ((a 0).toReal +
          ∑ i ∈ Finset.range m, |(a i).toReal - (a (i + 1)).toReal|) :=
        ENNReal.ofReal_le_ofReal (key m)
    _ = a 0 + ∑ i ∈ Finset.range m, ENNReal.ofReal |(a i).toReal - (a (i + 1)).toReal| := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
          (Finset.sum_nonneg fun _ _ => abs_nonneg _), ENNReal.ofReal_toReal (ha 0),
          ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]
    _ ≤ _ := add_le_add le_rfl (ENNReal.sum_le_tsum _)

/-- Subadditivity of `x ↦ x^p` (`p ∈ (0,1]`) over countable sums in `ℝ≥0∞`. -/
theorem rpow_tsum_le_tsum_rpow (D : ℕ → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, D i) ^ p ≤ ∑' i, D i ^ p := by
  have hfin : ∀ n, (∑ i ∈ Finset.range n, D i) ^ p ≤ ∑ i ∈ Finset.range n, D i ^ p := by
    intro n
    induction n with
    | zero => simp [ENNReal.zero_rpow_of_pos hp0]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add ih le_rfl)
  have ht : Tendsto (fun n => (∑ i ∈ Finset.range n, D i) ^ p) atTop
      (𝓝 ((∑' i, D i) ^ p)) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.tendsto_nat_tsum D)
  exact le_of_tendsto' ht fun n => (hfin n).trans (ENNReal.sum_le_tsum _)

/-- The `sup` of the rescaled inner masses: `E (sup_m W_{k+m})^p ≤ δ^p (1 + C_p)`. -/
theorem lintegral_iSup_innerMass_rpow_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {t δ p : ℝ} (hδ : 0 < δ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {k : ℕ} (hk : 2 * radius k < δ) :
    ∫⁻ ω, (⨆ m, innerMass γ X t δ (k + m) ω) ^ p ∂P ≤
      ENNReal.ofReal δ ^ p + ENNReal.ofReal ((cInc γ * δ) ^ p) *
        (1 - ENNReal.ofReal (exp (-(p * bdryRate γ) * log 2)))⁻¹ := by
  have hkm : ∀ m, 2 * radius (k + m) < δ := fun m =>
    lt_of_le_of_lt (by linarith [radius_add_le k m]) hk
  set W : ℕ → Ω → ℝ≥0∞ := fun m ω => innerMass γ X t δ (k + m) ω with hW
  set D : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ENNReal.ofReal |(W i ω).toReal - (W (i + 1) ω).toReal| with hD
  have hWm : ∀ m, Measurable (W m) := fun m => measurable_innerMass hX γ t δ (k + m)
  have hDm : ∀ i, Measurable (D i) := fun i =>
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((hWm i).ennreal_toReal.sub (hWm (i + 1)).ennreal_toReal))
  set q := exp (-(bdryRate γ) * log 2) with hq
  -- pathwise bound
  have hpath : ∀ᵐ ω ∂P, (⨆ m, W m ω) ^ p ≤ W 0 ω ^ p + ∑' i, D i ω ^ p := by
    have hall : ∀ᵐ ω ∂P, ∀ m, W m ω < ⊤ :=
      ae_all_iff.2 fun m => ae_innerMass_lt_top hX γ hδ (hkm m)
    filter_upwards [hall] with ω hω
    calc (⨆ m, W m ω) ^ p ≤ (W 0 ω + ∑' i, D i ω) ^ p :=
          ENNReal.rpow_le_rpow (iSup_le_add_tsum_abs_sub fun m => (hω m).ne) hp0.le
      _ ≤ W 0 ω ^ p + (∑' i, D i ω) ^ p := ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1
      _ ≤ W 0 ω ^ p + ∑' i, D i ω ^ p := add_le_add le_rfl (rpow_tsum_le_tsum_rpow _ hp0 hp1)
  -- increments
  have hinc : ∀ i, ∫⁻ ω, D i ω ∂P ≤ ENNReal.ofReal (cInc γ * δ * q ^ i) := by
    intro i
    have hint : Integrable (fun ω => |(W i ω).toReal - (W (i + 1) ω).toReal|) P :=
      ((integrable_innerMass_toReal hX γ hδ (hkm i)).sub
        (integrable_innerMass_toReal hX γ hδ (hkm (i + 1)))).abs
    rw [hD, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := integral_abs_innerMass_step_le hX (P := P) (t := t) hγ hγ2 hδ (hkm i)
    simp only [hW, ← add_assoc] at hb ⊢
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (cInc_nonneg γ) hδ.le))
    have hLi : (i : ℝ) * log 2 ≤ log (δ / radius (k + i)) := by
      have h1 : radius (k + i) = radius k * (2 : ℝ)⁻¹ ^ i := by
        simp only [radius, pow_add]
      have hr := radius_pos k
      rw [h1, ← div_div, log_div (div_pos hδ hr).ne' (by positivity), log_pow, log_inv]
      have : 0 ≤ log (δ / radius k) := log_nonneg (by rw [le_div_iff₀ hr]; linarith)
      linarith
    rw [hq, ← exp_nat_mul]
    apply exp_le_exp.2
    have := (bdryRate_pos hγ hγ2).le
    nlinarith
  have hq0 : 0 ≤ q := (exp_pos _).le
  -- integrate
  calc ∫⁻ ω, (⨆ m, W m ω) ^ p ∂P
      ≤ ∫⁻ ω, (W 0 ω ^ p + ∑' i, D i ω ^ p) ∂P := lintegral_mono_ae hpath
    _ = ∫⁻ ω, W 0 ω ^ p ∂P + ∑' i, ∫⁻ ω, D i ω ^ p ∂P := by
        rw [lintegral_add_left ((hWm 0).pow_const p),
          lintegral_tsum fun i => ((hDm i).pow_const p).aemeasurable]
    _ ≤ (∫⁻ ω, W 0 ω ∂P) ^ p + ∑' i, (∫⁻ ω, D i ω ∂P) ^ p :=
        add_le_add (lintegral_rpow_le_rpow_lintegral (hWm 0).aemeasurable hp0 hp1)
          (ENNReal.tsum_le_tsum fun i =>
            lintegral_rpow_le_rpow_lintegral (hDm i).aemeasurable hp0 hp1)
    _ ≤ ENNReal.ofReal δ ^ p + ∑' i, ENNReal.ofReal ((cInc γ * δ) ^ p) *
          ENNReal.ofReal (exp (-(p * bdryRate γ) * log 2)) ^ i := by
        refine add_le_add (le_of_eq ?_) (ENNReal.tsum_le_tsum fun i => ?_)
        · simp only [hW, add_zero]; rw [lintegral_innerMass hX γ hδ hk]
        · refine (ENNReal.rpow_le_rpow (hinc i) hp0.le).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_rpow_of_nonneg (by have := cInc_nonneg γ; positivity) hp0.le,
            ← ENNReal.ofReal_pow (exp_pos _).le, ← ENNReal.ofReal_mul (by
              have := cInc_nonneg γ; positivity),
            mul_rpow (by have := cInc_nonneg γ; positivity) (by positivity)]
          congr 2
          rw [hq, ← exp_nat_mul, ← exp_nat_mul, ← exp_mul]
          congr 1; ring
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **Fractional moment with `sup_{k' ≥ k}` inside (b).** For `p ∈ (0,1]`,
`S = [t − δ/2, t + δ/2]`, `|t| + δ ≤ R`, `2·2^{-k} < δ`:
`E (sup_m ν_{2^{-(k+m)}}(S))^p ≤ δ^{pγ²/4} e^{(2 log R − 2 log δ)(pγ/2)²/2} · δ^p (1 + C)`,
with `C = cInc^p (1 − 2^{-pβ})^{-1}`. -/
theorem lintegral_iSup_bdryApprox_rpow_le [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R t δ p : ℝ}
    (hδ : 0 < δ) (hR : |t| + δ ≤ R) (hp0 : 0 < p) (hp1 : p ≤ 1) {k : ℕ}
    (hk : 2 * radius k < δ) :
    ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (k + m) (bI t δ)) ^ p ∂P ≤
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) *
      (ENNReal.ofReal δ ^ p + ENNReal.ofReal ((cInc γ * δ) ^ p) *
        (1 - ENNReal.ofReal (exp (-(p * bdryRate γ) * log 2)))⁻¹) := by
  have hkm : ∀ m, 2 * radius (k + m) < δ := fun m =>
    lt_of_le_of_lt (by linarith [radius_add_le k m]) hk
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ / 2 * omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 4)) ^ p with hA
  set W : Ω → ℝ≥0∞ := fun ω => (⨆ m, innerMass γ X t δ (k + m) ω) ^ p with hW
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (γ / 2 * x) * δ ^ (γ ^ 2 / 4)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p
  have hψ : Measurable (fun x : FieldSample => (⨆ m, massFun γ t δ (k + m) x) ^ p) :=
    (Measurable.iSup fun m => measurable_massFun γ t δ (k + m)).pow_const p
  have hind : IndepFun A W P := (indepFun_omega_innerSample hX hδ hR).comp hφ hψ
  have hAm : Measurable A := hφ.comp (measurable_omegaAvg hX R t δ)
  have hWm : Measurable W := hψ.comp (measurable_innerSample hX t δ)
  calc ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (k + m) (bI t δ)) ^ p ∂P
      = ∫⁻ ω, (A * W) ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_bdryApprox_eq_omega_mul hX γ R (P := P) (t := t) hδ] with ω hω
        simp_rw [hω _ (hkm _)]
        rw [← ENNReal.mul_iSup, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rfl
    _ = (∫⁻ ω, A ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ _ := by
        rw [hA, lintegral_omega_factor_rpow hX γ hδ hR hp0.le]
        gcongr
        exact lintegral_iSup_innerMass_rpow_le hX hγ hγ2 hδ hp0 hp1 hk

/-! ### (c) The limit measure -/

/-- Piecewise-linear test functions increasing to `1_{(a,b)}`. -/
def trap (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ := max 0 (min 1 (n * min (x - a) (b - x)))

theorem continuous_trap (a b : ℝ) (n : ℕ) : Continuous (trap a b n) :=
  continuous_const.max (continuous_const.min (continuous_const.mul
    ((continuous_id.sub continuous_const).min (continuous_const.sub continuous_id))))

theorem trap_eq_zero {a b : ℝ} (n : ℕ) {x : ℝ} (hx : x ∉ Set.Ioo a b) : trap a b n x = 0 := by
  have hm : min (x - a) (b - x) ≤ 0 := by
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have : (n : ℝ) * min (x - a) (b - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos n.cast_nonneg hm
  unfold trap
  exact max_eq_left ((min_le_right _ _).trans this)

theorem trap_nonneg (a b : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ trap a b n x := le_max_left _ _

theorem trap_le_one (a b : ℝ) (n : ℕ) (x : ℝ) : trap a b n x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem hasCompactSupport_trap (a b : ℝ) (n : ℕ) : HasCompactSupport (trap a b n) :=
  HasCompactSupport.intro isCompact_Icc fun x hx =>
    trap_eq_zero n fun h => hx (Set.Ioo_subset_Icc_self h)

theorem trap_mono (a b : ℝ) (x : ℝ) : Monotone fun n : ℕ => trap a b n x := by
  intro n n' hnn'
  by_cases hx : x ∈ Set.Ioo a b
  · have hm : 0 ≤ min (x - a) (b - x) := le_min (by linarith [hx.1]) (by linarith [hx.2])
    show trap a b n x ≤ trap a b n' x
    unfold trap
    exact max_le_max le_rfl (min_le_min le_rfl
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hnn') hm))
  · simp only [trap_eq_zero _ hx, le_refl]

theorem indicator_le_iSup_trap (a b : ℝ) (x : ℝ) :
    (Set.Ioo a b).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ ⨆ n : ℕ, ENNReal.ofReal (trap a b n x) := by
  by_cases hx : x ∈ Set.Ioo a b
  · rw [Set.indicator_of_mem hx]
    have hm : 0 < min (x - a) (b - x) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / min (x - a) (b - x))
    refine le_trans (le_of_eq ?_) (le_iSup _ n)
    have h1 : 1 ≤ (n : ℝ) * min (x - a) (b - x) := by
      rw [div_le_iff₀ hm] at hn; linarith
    unfold trap
    rw [min_eq_left h1, max_eq_right zero_le_one, ENNReal.ofReal_one]
  · rw [Set.indicator_of_notMem hx]; exact bot_le

/-- Lower semicontinuity on open intervals along a vague limit: if the masses of `[a,b]` are
bounded by `M` from index `k` on, then the limit gives `(a,b)` mass at most `M`. -/
theorem measure_Ioo_le_of_isVagueLimitR {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitR νs ν) {a b : ℝ} {M : ℝ≥0∞} {k : ℕ}
    (hM : ∀ m, νs (k + m) (Set.Icc a b) ≤ M) : ν (Set.Ioo a b) ≤ M := by
  rcases eq_or_ne M ⊤ with hMt | hMt
  · rw [hMt]; exact le_top
  have hloc := h.1
  have hn : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (trap a b n x) ∂ν ≤ M := by
    intro n
    have hint : Integrable (trap a b n) ν :=
      (continuous_trap a b n).integrable_of_hasCompactSupport (hasCompactSupport_trap a b n)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (trap_nonneg a b n)),
      ← ENNReal.ofReal_toReal hMt]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_of_tendsto (h.2 _ (continuous_trap a b n) (hasCompactSupport_trap a b n))
      (eventually_atTop.2 ⟨k, fun j hj => ?_⟩)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    have hfin : νs (k + m) (Set.Icc a b) < ⊤ := (hM m).trans_lt hMt.lt_top
    have hg : Integrable ((Set.Icc a b).indicator fun _ => (1 : ℝ)) (νs (k + m)) :=
      (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const hfin.ne)
    calc ∫ x, trap a b n x ∂(νs (k + m))
        ≤ ∫ x, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) x ∂(νs (k + m)) := by
          refine integral_mono_of_nonneg (ae_of_all _ (trap_nonneg a b n)) hg
            (ae_of_all _ fun x => ?_)
          by_cases hx : x ∈ Set.Icc a b
          · rw [Set.indicator_of_mem hx]; exact trap_le_one a b n x
          · rw [Set.indicator_of_notMem hx]
            exact (trap_eq_zero n fun h' => hx (Set.Ioo_subset_Icc_self h')).le
      _ = (νs (k + m)).real (Set.Icc a b) := integral_indicator_one measurableSet_Icc
      _ ≤ M.toReal := ENNReal.toReal_mono hMt (hM m)
  calc ν (Set.Ioo a b) = ∫⁻ x, (Set.Ioo a b).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
        rw [lintegral_indicator_const measurableSet_Ioo, one_mul]
    _ ≤ ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (trap a b n x) ∂ν :=
        lintegral_mono fun x => indicator_le_iSup_trap a b x
    _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (trap a b n x) ∂ν := by
        refine lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp
          (continuous_trap a b n).measurable) fun n n' hnn' x => ?_
        exact ENNReal.ofReal_le_ofReal (trap_mono a b x hnn')
    _ ≤ M := iSup_le hn

/-- **Fractional moment of the limit measure (c).** Under the hypotheses of
`lintegral_iSup_bdryApprox_rpow_le`, the same bound holds for
`E ν((t − δ/2, t + δ/2))^p`, `ν = qBoundaryMeasure γ Z`. -/
theorem lintegral_qBoundaryMeasure_rpow_le [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R t δ p : ℝ}
    (hδ : 0 < δ) (hR : |t| + δ ≤ R) (hp0 : 0 < p) (hp1 : p ≤ 1) {k : ℕ}
    (hk : 2 * radius k < δ) :
    ∫⁻ ω, qBoundaryMeasure γ (zField X R ω) (Set.Ioo (t - δ / 2) (t + δ / 2)) ^ p ∂P ≤
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) *
      (ENNReal.ofReal δ ^ p + ENNReal.ofReal ((cInc γ * δ) ^ p) *
        (1 - ENNReal.ofReal (exp (-(p * bdryRate γ) * log 2)))⁻¹) := by
  refine le_trans (lintegral_mono_ae ?_) (lintegral_iSup_bdryApprox_rpow_le hX hγ hγ2 hδ hR hp0
    hp1 hk)
  filter_upwards [ae_isVagueLimitR_qBoundaryMeasure_zField hX (P := P) hγ hγ2 R] with ω hω
  exact ENNReal.rpow_le_rpow (measure_Ioo_le_of_isVagueLimitR hω (k := k)
    fun m => le_iSup (fun m => bdryApprox γ (zField X R ω) (k + m) (bI t δ)) m) hp0.le

/-! ### Dyadic form of (b), (c) -/

theorem dyadic_real_le {γ p R : ℝ} (hp0 : 0 < p) {n : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hδR : 4 * radius n ≤ R) :
    (4 * radius n) ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log (4 * radius n)).toNNReal * (p * γ / 2) ^ 2 / 2) *
        ((4 * radius n) ^ p * (1 + K))
      ≤ (4 ^ (p * (1 + γ ^ 2 / 4)) * R ^ (p ^ 2 * γ ^ 2 / 4) * (1 + K)) *
        2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4)) := by
  have hr := radius_pos n
  set δ := 4 * radius n with hδdef
  have hδ : 0 < δ := by positivity
  have hR : 0 < R := hδ.trans_le hδR
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  have hlogδ : log δ = 2 * log 2 - n * log 2 := by
    have := log_one_div_radius n
    rw [one_div, log_inv] at this
    rw [hδdef, log_mul (by norm_num) hr.ne', h4]
    linarith
  have hv : ((2 * log R - 2 * log δ).toNNReal : ℝ) = 2 * log R - 2 * log δ :=
    Real.coe_toNNReal _ (by linarith [log_le_log hδ hδR])
  rw [hv, rpow_def_of_pos hδ, rpow_def_of_pos hδ, rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
    rpow_def_of_pos hR, rpow_def_of_pos two_pos, hlogδ, h4]
  have key : ∀ a b c d e f : ℝ, a + b + c ≤ d + e + f →
      exp a * exp b * (exp c * (1 + K)) ≤ exp d * exp e * (1 + K) * exp f := by
    intro a b c d e f h
    rw [show exp a * exp b * (exp c * (1 + K)) = (1 + K) * exp (a + b + c) by
        rw [exp_add, exp_add]; ring,
      show exp d * exp e * (1 + K) * exp f = (1 + K) * exp (d + e + f) by
        rw [exp_add, exp_add]; ring]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 h) (by linarith)
  apply key
  have := mul_nonneg (mul_nonneg (sq_nonneg p) (sq_nonneg γ)) (log_nonneg one_le_two)
  nlinarith [this]

/-- **(b) and (c) in dyadic form.** For `p ∈ (0,1]` and `R > 0` there is `C` such that for every
`n` and every `t` with `|t| + 4·2^{-n} ≤ R`, with `S_n = [t − 2·2^{-n}, t + 2·2^{-n}]`:
`E (sup_{k ≥ n} ν_{2^{-k}}(S_n))^p ≤ C 2^{-np(1+γ²/4) + nγ²p²/4}` and
`E ν((t − 2·2^{-n}, t + 2·2^{-n}))^p ≤ C 2^{-np(1+γ²/4) + nγ²p²/4}` for the limit `ν`. -/
theorem fracMoment_dyadic [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R p : ℝ} (hR : 0 < R) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), |t| + 4 * radius n ≤ R →
      ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (n + m) (bI t (4 * radius n))) ^ p ∂P ≤
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) ∧
      ∫⁻ ω, qBoundaryMeasure γ (zField X R ω)
          (Set.Ioo (t - 4 * radius n / 2) (t + 4 * radius n / 2)) ^ p ∂P ≤
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
  set q := exp (-(p * bdryRate γ) * log 2) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, exp_lt_one_iff]
    have := bdryRate_pos hγ hγ2
    have := log_pos one_lt_two
    have : 0 < p * bdryRate γ := by positivity
    nlinarith
  set K := cInc γ ^ p * (1 - q)⁻¹ with hK
  have hK0 : 0 ≤ K := mul_nonneg (rpow_nonneg (cInc_nonneg γ) _) (inv_nonneg.2 (by linarith))
  refine ⟨4 ^ (p * (1 + γ ^ 2 / 4)) * R ^ (p ^ 2 * γ ^ 2 / 4) * (1 + K), ?_, fun n t ht => ?_⟩
  · have hRpos : 0 ≤ R ^ (p ^ 2 * γ ^ 2 / 4) := rpow_nonneg hR.le _
    positivity
  have hr := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have hk : 2 * radius n < 4 * radius n := by linarith
  have hδR : 4 * radius n ≤ R := by linarith [abs_nonneg t]
  have hG : ENNReal.ofReal ((4 * radius n) ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log (4 * radius n)).toNNReal * (p * γ / 2) ^ 2 / 2)) *
      (ENNReal.ofReal (4 * radius n) ^ p + ENNReal.ofReal ((cInc γ * (4 * radius n)) ^ p) *
        (1 - ENNReal.ofReal q)⁻¹) ≤
      ENNReal.ofReal ((4 ^ (p * (1 + γ ^ 2 / 4)) * R ^ (p ^ 2 * γ ^ 2 / 4) * (1 + K)) *
        2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
    have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
      rw [ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
    have hc0 : 0 ≤ (cInc γ * (4 * radius n)) ^ p :=
      rpow_nonneg (mul_nonneg (cInc_nonneg γ) hδ.le) _
    have hi0 : (0 : ℝ) ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
    have hA0 : 0 ≤ (4 * radius n) ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log (4 * radius n)).toNNReal * (p * γ / 2) ^ 2 / 2) :=
      mul_nonneg (rpow_nonneg hδ.le _) (exp_pos _).le
    rw [e1, ← ENNReal.ofReal_inv_of_pos (by linarith),
      ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le, ← ENNReal.ofReal_mul hc0,
      ← ENNReal.ofReal_add (rpow_nonneg hδ.le _) (mul_nonneg hc0 hi0), ← ENNReal.ofReal_mul hA0]
    refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (dyadic_real_le hp0 hK0 hδR))
    rw [mul_rpow (cInc_nonneg γ) hδ.le, hK]
    ring
  exact ⟨(lintegral_iSup_bdryApprox_rpow_le hX hγ hγ2 hδ ht hp0 hp1 hk).trans hG,
    (lintegral_qBoundaryMeasure_rpow_le hX hγ hγ2 hδ ht hp0 hp1 hk).trans hG⟩

/-! ### (a) Exact scaling of the inner process (finite-dimensional laws) -/

theorem good_innerIdx {t δ : ℝ} (hδ : 0 < δ) (q : InnerQ) :
    FcIdx.Good (innerIdx t δ q.1.1 q.1.2) :=
  good_real (s := t + δ * q.1.1) (mul_pos hδ q.2.1) hδ

/-- The inner process is a centered Gaussian process. -/
theorem isGaussianProcess_innerProc (hX : IsFreeGFFModConstH X P) {t δ : ℝ} (hδ : 0 < δ) :
    IsGaussianProcess (fun (q : InnerQ) (ω : Ω) => innerProc X t δ ω q) P :=
  (isGaussianProcess_fcPair hX).comp_right
    (fun q : InnerQ => (⟨innerIdx t δ q.1.1 q.1.2, good_innerIdx hδ q⟩ : {p : FcIdx // p.Good}))

end FracMom
end QuantumZipper
