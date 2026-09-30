import QuantumZipper.Proofs.Zipper.D3PlusN2TmZStmt
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.GFF.K3.HarmonicPart

/-!
# N2-zero, heart, sub-node RAD: the radial part of the local field is a Brownian motion

Task N2-TMZERO. The radial process of the local field `Z = markovZ X 0 r` on the half-disc,
`zRadB X r t = (√2)⁻¹ · (semicircle average of Z at radius r e^{−t})` (`D3PlusN2TmZStmt.lean`),
is a standard Brownian motion: `isBrownianReal_zRadB`.

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7 (p. 77: "`h_{e^{−t}}(0)`
for `t > 0` evolves as `B_{2t}`"); Sheffield arXiv:1012.4797 p. 25 (`A'_t = B_t + (α − Q)t`).

Route (following the sources; the Lean steps are own elementary arguments on top of the project's
toolkits):
* `Z(fc(0,ρ)) = X(fc(0,ρ)) − X(fc(0,r))` a.s. for `0 < ρ < r` (Markov decomposition
  `K3.markov_decomposition`, mean value property of the harmonic part `K3.harmH`, which vanishes at
  `0`, and `halfDiscPoisson 0 r 0 = fc(0,r)`);
* along the regular version `G` of `X` (`WedgeTK.exists_isRegVersion`),
  `radAvgReg Z ρ = G(0,ρ) − G(0,r)` for all `0 < ρ < r` and `radAvgReg Z r = 0` (the dyadic
  approximating circles lie outside the half-disc);
* the pair process `t ↦ (√2)⁻¹ (X(fc(0,r e^{−t})) − X(fc(0,r)))` is centered Gaussian with
  covariance `min s t` (`kernelCov_fc0`), as in `WedgeTK.isBrownianReal_radialBMpos`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK GaussTK

theorem halfDiscPoisson_zero_zero {r : ℝ} (hr : 0 < r) :
    K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ) = foldedCircle 0 r := by
  unfold K3.halfDiscPoisson foldedCircle
  simp only [Complex.ofReal_zero]
  congr 1
  have h : (fun w : ℂ => ENNReal.ofReal ((r ^ 2 - ‖(0 : ℂ) - 0‖ ^ 2) / ‖w - 0‖ ^ 2)) =ᵐ[circleUnif 0 r]
      fun _ => 1 := by
    filter_upwards [K3.ae_mem_sphere_circleUnif_k3 (0 : ℂ) hr] with w hw
    rw [mem_sphere_zero_iff_norm] at hw
    rw [sub_self, sub_zero, norm_zero, hw, zero_pow two_ne_zero, sub_zero,
      div_self (pow_ne_zero 2 hr.ne'), ENNReal.ofReal_one]
  rw [withDensity_congr_ae h]
  exact withDensity_one

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
theorem ae_harmH_zero (hX : IsFreeGFFModConstH X P) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hr'r : r' < r) : ∀ᵐ ω ∂P, K3.harmH X 0 r r' ω 0 = 0 := by
  have h := (K3.kolY_harmIncr_spec (P := P) (t := 0) hX hr hr' hr'r).2 0 zero_mem_Hbar
  have hf : foldH 0 = 0 := by simp [foldH]
  filter_upwards [h] with ω hω
  simp only [K3.harmH, hf]
  rw [hω]
  simp [K3.harmIncr, K3.retr, hf]

theorem isLocalH_fc0 {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    K3.IsLocalH 0 r (foldedCircle 0 ρ) := by
  have h := foldedCircle_compl_closedBall (d := 0) hρ
  rw [norm_zero, zero_add] at h
  exact ⟨isAdmissibleH_foldedCircle' 0 hρ, ρ, hρr, h⟩

theorem ae_markovZ_fc0 (hX : IsFreeGFFModConstH X P) {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    ∀ᵐ ω ∂P, K3.markovZ X 0 r ω (foldedCircle 0 ρ) =
      X ω (foldedCircle 0 ρ) - X ω (foldedCircle 0 r) := by
  set r' := (ρ + r) / 2 with hr'def
  have hr : 0 < r := hρ.trans hρr
  have hr' : 0 < r' := by positivity
  have hr'r : r' < r := by rw [hr'def]; linarith
  have hρr' : ρ < r' := by rw [hr'def]; linarith
  have hsupp : foldedCircle 0 ρ (closedBall ((0 : ℝ) : ℂ) r')ᶜ = 0 := by
    have h := foldedCircle_compl_closedBall (d := 0) hρ
    rw [norm_zero, zero_add] at h
    exact measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall hρr'.le)) h
  filter_upwards [K3.markov_decomposition (t := 0) hX hr hr' hr'r
    (isAdmissibleH_foldedCircle' 0 hρ) hsupp, K3.ae_harmonicOnNhd_harmH (t := 0) hX hr hr' hr'r,
    ae_harmH_zero hX hr hr' hr'r] with ω h1 h2 h3
  have hfold : (fun z => K3.harmH X 0 r r' ω (foldH z)) = K3.harmH X 0 r r' ω := by
    funext z
    simp only [K3.harmH, CircleFubini.foldH_of_mem' (CircleFubini.foldH_mem_Hbar' z)]
  rw [Complex.ofReal_zero] at h2
  have hmv := integral_foldedCircle_of_harm (g := K3.harmH X 0 r r' ω) (r := r')
    (by rw [hfold]; exact h2) (d := 0) hρ (by rw [norm_zero, zero_add]; exact hρr')
  have hf0 : foldH 0 = 0 := by simp [foldH]
  rw [hmv.2, hf0, h3, halfDiscPoisson_zero_zero hr, measure_univ, ENNReal.toReal_one,
    one_mul] at h1
  linarith

theorem ae_locZField_fc0 (hX : IsFreeGFFModConstH X P) (r : ℝ) :
    ∀ᵐ ω ∂P, ∀ n m : ℕ, dyRad n m < r →
      locZField X r ω (foldedCircle 0 (dyRad n m)) =
        X ω (foldedCircle 0 (dyRad n m)) - X ω (foldedCircle 0 r) := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro m
  by_cases h : dyRad n m < r
  · filter_upwards [ae_markovZ_fc0 hX (dyRad_pos n m) h] with ω hω _
    rw [locZField_apply_of_local X ω (isLocalH_fc0 (dyRad_pos n m) h)]
    exact hω
  · exact Eventually.of_forall fun ω hlt => absurd hlt h

end Prob

theorem not_isLocalH_fc0 {r ρ : ℝ} (hr : 0 < r) (hρ : r < ρ) :
    ¬ K3.IsLocalH 0 r (foldedCircle 0 ρ) := by
  rintro ⟨-, r', hr'r, h0⟩
  have hρ0 : 0 < ρ := hr.trans hρ
  have hin : foldedCircle 0 ρ (closedBall ((0 : ℝ) : ℂ) r') = 0 := by
    rw [foldedCircle, Measure.map_apply measurable_foldH measurableSet_closedBall]
    refine measure_mono_null ?_ (ae_iff.1 (K3.ae_mem_sphere_circleUnif_k3 (0 : ℂ) hρ0))
    intro w hw hs
    rw [mem_sphere_zero_iff_norm] at hs
    have hw' : ‖foldH w‖ ≤ r' := by simpa using hw
    rw [CircleFubini.norm_foldH', hs] at hw'
    linarith
  have htot := measure_add_measure_compl (μ := foldedCircle 0 ρ)
    (measurableSet_closedBall (x := ((0 : ℝ) : ℂ)) (ε := r'))
  rw [hin, h0, measure_univ] at htot
  simp at htot

theorem lt_dyadicRound_add_radius (n : ℕ) (r : ℝ) : r < dyadicRound n r + radius n := by
  have h1 : (2 : ℝ) ^ n * r - 1 < ⌊(2 : ℝ) ^ n * r⌋ := Int.sub_one_lt_floor _
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have e : dyadicRound n r + radius n = ((⌊(2 : ℝ) ^ n * r⌋ : ℝ) + 1) / 2 ^ n := by
    rw [dyadicRound, radius, inv_pow]; field_simp
  rw [e, lt_div_iff₀ h2]
  linarith

theorem radAvgReg_locZField_self {Ω : Type*} (X : Ω → FieldSample) {r : ℝ} (hr : 0 < r)
    (ω : Ω) : radAvgReg (locZField X r ω) r = 0 := by
  have e : (fun n => locZField X r ω (foldedCircle 0 (dyadicRound n r + radius n))) =
      fun _ => 0 := by
    funext n
    simp only [locZField, extLoc]
    rw [dif_neg (not_isLocalH_fc0 hr (lt_dyadicRound_add_radius n r))]
  unfold radAvgReg
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

/-- On a good sample, the semicircle averages of the local field are the regular version's
increments from radius `r`. -/
theorem radAvgReg_locZField_eq {Ω : Type*} {X : Ω → FieldSample} {r : ℝ} {ω : Ω}
    {F : ℂ × ℝ → ℝ} (hg : GoodRad (X ω) F)
    (hZ : ∀ n m : ℕ, dyRad n m < r → locZField X r ω (foldedCircle 0 (dyRad n m)) =
      X ω (foldedCircle 0 (dyRad n m)) - X ω (foldedCircle 0 r))
    (hXr : X ω (foldedCircle 0 r) = F (0, r)) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    radAvgReg (locZField X r ω) ρ = F (0, ρ) - F (0, r) := by
  have hs : ∀ n : ℕ, dyadicRound n ρ + radius n = dyRad n (⌊(2 : ℝ) ^ n * ρ⌋.toNat) := by
    intro n
    rw [CoordsFull.radAvg_radius_eq_div, dyRad]
    have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * ρ⌋ := Int.floor_nonneg.2 (by positivity)
    have : ((⌊(2 : ℝ) ^ n * ρ⌋.toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * ρ⌋ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]; push_cast; ring
  have hlim : Tendsto (fun n : ℕ => dyadicRound n ρ + radius n) atTop (𝓝 ρ) := by
    have h1 : Tendsto (fun n : ℕ => dyadicRound n ρ) atTop (𝓝 ρ) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le n ρ)
        tendsto_one_div_two_pow
    have h2 : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) :=
      tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT
    simpa using h1.add h2
  have hmem : ∀ n : ℕ, ((0 : ℂ), dyadicRound n ρ + radius n) ∈ Hbar ×ˢ Ioi (0 : ℝ) := fun n =>
    ⟨zero_mem_Hbar, by rw [hs n]; exact dyRad_pos _ _⟩
  have ht : Tendsto (fun n : ℕ => ((0 : ℂ), dyadicRound n ρ + radius n)) atTop
      (𝓝[Hbar ×ˢ Ioi 0] ((0 : ℂ), ρ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hlim, Eventually.of_forall hmem⟩
  have hc := (hg.1.1 ((0 : ℂ), ρ) ⟨zero_mem_Hbar, hρ⟩).tendsto.comp ht
  have hev : ∀ᶠ n in atTop, F ((0 : ℂ), dyadicRound n ρ + radius n) - F (0, r) =
      locZField X r ω (foldedCircle 0 (dyadicRound n ρ + radius n)) := by
    filter_upwards [hlim.eventually (gt_mem_nhds hρr)] with n hn
    rw [hs n] at hn ⊢
    rw [hZ n _ hn, hg.2 n _, hXr]
  unfold radAvgReg
  exact ((hc.sub_const (F (0, r))).congr' hev).limUnder_eq

/-! ## The Brownian motion -/

/-- The pair index `(fc(0, r e^{−t}), fc(0, r))`. -/
def zIdx {r : ℝ} (hr : 0 < r) (t : ℝ≥0) : {p : FcIdx // p.Good} :=
  ⟨((0 : ℂ), r * Real.exp (-(t : ℝ)), (0 : ℂ), r),
    zero_mem_Hbar, mul_pos hr (Real.exp_pos _), zero_mem_Hbar, hr⟩

theorem fcPairCov_zIdx {r : ℝ} (hr : 0 < r) {s t : ℝ≥0} (hst : s ≤ t) :
    fcPairCov (zIdx hr s).1 (zIdx hr t).1 = 2 * s := by
  have hs : (0 : ℝ) ≤ s := s.2
  have hst' : (s : ℝ) ≤ t := hst
  have ha := mul_pos hr (Real.exp_pos (-(s : ℝ)))
  have hb := mul_pos hr (Real.exp_pos (-(t : ℝ)))
  simp only [zIdx, fcPairCov, kernelCov2]
  rw [kernelCov_fc0 ha hb, kernelCov_fc0 ha hr, kernelCov_fc0 hr hb, kernelCov_fc0 hr hr,
    max_self]
  have e1 : max (r * Real.exp (-(s : ℝ))) (r * Real.exp (-(t : ℝ))) = r * Real.exp (-(s : ℝ)) :=
    max_eq_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hst')) hr.le)
  have hle : ∀ u : ℝ, 0 ≤ u → r * Real.exp (-u) ≤ r := fun u hu =>
    mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.2 (neg_nonpos.2 hu))
  have e2 : max (r * Real.exp (-(s : ℝ))) r = r := max_eq_right (hle _ hs)
  have e3 : max r (r * Real.exp (-(t : ℝ))) = r := max_eq_left (hle _ t.2)
  rw [e1, e2, e3, Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- The clean pair process `(√2)⁻¹ (X(fc(0, r e^{−t})) − X(fc(0, r)))`. -/
def zPairBM (X : Ω → FieldSample) {r : ℝ} (hr : 0 < r) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (√2)⁻¹ * fcPairVal X (zIdx hr t).1 ω

omit [IsProbabilityMeasure P] in
theorem isPreBrownianReal_zPairBM (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) :
    IsPreBrownianReal (zPairBM X hr) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ ?_ ?_
  · have h := ((isGaussianProcess_fcPair hX).comp_right (zIdx hr)).smul (fun _ => (√2)⁻¹)
    exact h
  · intro t
    show ∫ ω, (√2)⁻¹ * fcPairVal X (zIdx hr t).1 ω ∂P = 0
    rw [integral_const_mul, integral_fcPairVal hX (zIdx hr t).2, mul_zero]
  · intro s t hst
    show cov[fun ω => (√2)⁻¹ * fcPairVal X (zIdx hr s).1 ω,
      fun ω => (√2)⁻¹ * fcPairVal X (zIdx hr t).1 ω; P] = s
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_fcPairVal hX (zIdx hr s).2 (zIdx hr t).2, fcPairCov_zIdx hr hst, ← mul_assoc,
      inv_sqrt_two_mul_self]
    ring

/-- On the good event, `zRadB` is the regular version's radial increment, for every `t`. -/
theorem ae_zRadB_eq (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) {G : Ω → ℂ × ℝ → ℝ}
    (hG : IsRegVersion X P G) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, zRadB X r t ω =
      (√2)⁻¹ * (G ω ((0 : ℂ), r * Real.exp (-(t : ℝ))) - G ω (0, r)) := by
  filter_upwards [hG.ae_good, ae_locZField_fc0 hX r, hG.raw 0 zero_mem_Hbar r hr]
    with ω hg hZ hXr
  intro t
  simp only [zRadB]
  rcases eq_or_lt_of_le (t.2 : (0 : ℝ) ≤ t) with h0 | hpos
  · have ht0 : t = 0 := NNReal.coe_eq_zero.1 h0.symm
    subst ht0
    simp only [NNReal.coe_zero, neg_zero, Real.exp_zero, mul_one, radAvgReg_locZField_self X hr,
      sub_self]
  · have hlt : r * Real.exp (-(t : ℝ)) < r :=
      mul_lt_of_lt_one_right hr (Real.exp_lt_one_iff.2 (neg_lt_zero.2 hpos))
    rw [radAvgReg_locZField_eq hg hZ hXr.symm (mul_pos hr (Real.exp_pos _)) hlt]

/-- **The radial part of the local field is a standard Brownian motion.** -/
theorem isBrownianReal_zRadB (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) :
    IsBrownianReal (zRadB X r) P where
  toIsPreBrownianReal := by
    obtain ⟨G, hG⟩ := exists_isRegVersion hX
    refine (isPreBrownianReal_zPairBM hX hr).congr fun t => ?_
    filter_upwards [ae_zRadB_eq hX hr hG, hG.raw 0 zero_mem_Hbar _ (mul_pos hr (Real.exp_pos _)),
      hG.raw 0 zero_mem_Hbar r hr] with ω h h1 h2
    rw [h t]
    simp only [zPairBM, fcPairVal, zIdx]
    rw [← h1, ← h2]
  cont := by
    obtain ⟨G, hG⟩ := exists_isRegVersion hX
    filter_upwards [ae_zRadB_eq hX hr hG] with ω h
    have e : (fun t : ℝ≥0 => zRadB X r t ω) =
        fun t : ℝ≥0 => (√2)⁻¹ * (G ω ((0 : ℂ), r * Real.exp (-(t : ℝ))) - G ω (0, r)) :=
      funext h
    rw [e]
    refine continuous_const.mul (Continuous.sub ?_ continuous_const)
    exact (hG.cont ω).comp_continuous
      (continuous_const.prodMk (continuous_const.mul
        (Real.continuous_exp.comp (NNReal.continuous_coe.neg))))
      fun t => ⟨zero_mem_Hbar, mul_pos hr (Real.exp_pos _)⟩

end Prob

end D3Plus
end QuantumZipper
