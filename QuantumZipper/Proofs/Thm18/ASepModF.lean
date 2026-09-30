import QuantumZipper.Proofs.Thm18.ASepModE
import QuantumZipper.Proofs.Thm18.ASepHopf
import QuantumZipper.Proofs.Thm18.ASepModB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod F): PUSH0 for the A-sep family — `|E(muA0 p ρ − muA0 p 0)| ≤ M₀ ρ^{1/4}`

`push0_muA0`: uniformly over `p = (τ, a) ∈ [0,T] × [a₀,a₁]` and `ρ ∈ (0,1]`. This is the D33 /
XFLOW PUSH0 argument (`RegUnif.push0_unif`, `F1.push0_flow`: `RegUnif.abs_energy_push_le_explicit`,
Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 transported through the Loewner map) with the
base `α = σ.map (w ↦ f_τ(a w))`, whose hypotheses are supplied uniformly by

* support and `Im` comparison: `norm_fwdMap_scaled_le`, `ASep.im_fwdMap_ge_of_lower`
  (`κ = a₀ e^{−2T/m²}`);
* Frostman: `isFrostman_alphaA` (through the inverse-map bound (C3));
* strip bound and `|log Im|`: `stripBound_map_scaled`, `integral_log_im_map_scaled_le`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif B2

/-- The pointwise facts for the base `α`. -/
theorem alphaA_facts {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    {r a₀ a₁ T m M : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M)
    {τ a : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (ha : a ∈ Icc a₀ a₁) :
    ∀ᵐ x ∂foldedCircle d r, x ∈ H ∧
      a₀ * Real.exp (-2 * T / m ^ 2) * x.im ≤ (gA W d r τ a x).im ∧
      ‖gA W d r τ a x‖ ≤ a₁ * (‖d‖ + r) + M + 2 * T / m + 1 := by
  filter_upwards [ae_mem_foldSph d hr.le, TwoPoint.foldedCircle_ae_mem_H d hr] with x hx hxH
  rw [gA_of_mem hx]
  have hxc := mul_mem_compl_fwdHull hW ha₀ hm hgood0 hlow hτ ha hx hxH
  have him := im_fwdMap_ge_of_lower hW hxc.1 hm (hgood0 a ha x hx)
    (hlow _ (mem_scaledSph ha hx)) hτ
  have e : ((a : ℂ) * x).im = a * x.im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [e] at him
  have hx0 : 0 < x.im := hxH
  have hE := Real.exp_pos (-2 * T / m ^ 2)
  refine ⟨hxH, ?_, ?_⟩
  · have : a₀ * x.im ≤ a * x.im := mul_le_mul_of_nonneg_right ha.1 hx0.le
    nlinarith
  · have := norm_fwdMap_scaled_le hm ha₀ hgood0 hlow hM hτ ha hx
    linarith

/-- **PUSH0 for the A-sep family.** -/
theorem push0_muA0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    {r a₀ a₁ T m M : ℝ} (hT : 0 ≤ T) (hr : 0 < r) (ha₀ : 0 < a₀) (ha₀₁ : a₀ ≤ a₁) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ p : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T → p 1 ∈ Icc a₀ a₁ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p 0) (muA0 W d r p ρ, muA0 W d r p 0)| ≤
        M₀ * ρ ^ (1 / 4 : ℝ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  set R : ℝ := a₁ * (‖d‖ + r) + M + 2 * T / m + 1 with hRdef
  have hR1 : 1 ≤ R := by
    have : 0 ≤ a₁ * (‖d‖ + r) := mul_nonneg (ha₀.le.trans ha₀₁) (by positivity)
    have : 0 ≤ 2 * T / m := by positivity
    linarith
  set κ : ℝ := a₀ * Real.exp (-2 * T / m ^ 2) with hκdef
  have hκ : 0 < κ := by positivity
  set σ := foldedCircle d r with hσ
  have hlσ : Integrable (fun z : ℂ => |Real.log z.im|) σ :=
    (TwoPoint.integrable_log_im_foldedCircle d hr).abs
  set Iσ : ℝ := ∫ z, |Real.log z.im| ∂σ with hIσ
  have hIσ0 : 0 ≤ Iσ := integral_nonneg fun _ => abs_nonneg _
  set cS : ℝ := (1 + |Real.log κ| + Real.log R) * (200 / Real.sqrt r + (1 + Iσ)) /
    κ ^ (1 / 4 : ℝ) with hcS
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hcS0 : 0 ≤ cS := by rw [hcS]; positivity
  set CF : ℝ := 6 / r * (2 * (Real.exp (8 * T / m ^ 2) / a₀)) ^ (1 : ℝ) +
    (2 / (m / 2 * Real.exp (-(8 * T / m ^ 2)))) ^ (1 : ℝ) with hCF
  have hCF0 : 0 ≤ CF := by rw [hCF]; positivity
  set Lb : ℝ := Iσ + (|Real.log κ| + Real.log R) with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  set Bf := RegCont.revBound (2 * M) T (R + 1) with hBf
  set Mx := Real.sqrt ((R + 1) ^ 2 + 4 * T) with hMx
  set Bx := max (2 * Bf) (2 * (R + 1)) with hBx
  set K := |Real.log Mx| + 2 * |Real.log Bx| with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨C₀, hC₀, hLA⟩ := CoordReg.integral_abs_log_im_fc_le (R + 1)
  set M₁ := 2 * (K * 1 + 3 * (C₀ * 1 + Lb)) + 3 * 1 * (C₀ + 2) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  refine ⟨2 * CF + 2 * M₁ * cS, by positivity, fun p hp0 hp1 ρ hρ hρ1 => ?_⟩
  set τ := p 0 with hτdef
  set a := p 1 with hadef
  set g := gA W d r τ a with hgdef
  have hgm : Measurable g := measurable_gA hW hW0 hm hgood0 hlow hp0 hp1
  set α := σ.map g with hαdef
  have hαP : IsProbabilityMeasure α := inferInstance
  have hfacts := alphaA_facts hW hW0 hr ha₀ hm hgood0 hlow hM hp0 hp1
  have hfacts' : ∀ᵐ x ∂σ, x ∈ H ∧ κ * x.im ≤ (g x).im ∧ ‖g x‖ ≤ R := hfacts
  have hgH : ∀ᵐ x ∂σ, g x ∈ H := hfacts'.mono fun x hx =>
    show 0 < (g x).im from (mul_pos hκ hx.1).trans_le hx.2.1
  have hSm := measurableSet_closedBall_inter_Hbar R
  have hsuppae : ∀ᵐ x ∂α, x ∈ closedBall 0 R ∩ Hbar := by
    refine (ae_map_iff hgm.aemeasurable hSm).2 ((hfacts'.and hgH).mono fun z hz => ?_)
    exact ⟨mem_closedBall_zero_iff.2 hz.1.2.2, show (0 : ℝ) ≤ _ from le_of_lt hz.2⟩
  have hsupp : α (closedBall 0 R ∩ Hbar)ᶜ = 0 := ae_iff.1 hsuppae
  have hαH : ∀ᵐ x ∂α, x ∈ H :=
    (ae_map_iff hgm.aemeasurable isOpen_H.measurableSet).2 hgH
  have hF : QuantumZipper.IsFrostman α 1 CF :=
    isFrostman_alphaA hW hW0 hr ha₀ hm hgood0 hlow hp0 hp1
  have hlα := integrable_log_im_map_scaled hgm hκ hR1 hfacts' hlσ
  have hLα : ∫ x, |Real.log x.im| ∂α ≤ Lb := integral_log_im_map_scaled_le hgm hκ hR1 hfacts' hlσ
  have hS : CoordReg.StripBound α cS (1 / 4) :=
    stripBound_map_scaled hgm hκ hR1 hfacts' hlσ (by positivity) (by norm_num)
      (CoordRegComp.stripBound_foldedCircle d hr)
  have hVu : Continuous (vrev W τ) := continuous_vrev hW τ
  have hKb := abs_hK_le_explicit hVu hp0.1 (R := R + 1) (Bf := Bf) (M := Mx) (B := Bx)
    (fun z _ hz => (RegCont.norm_revMap_le_revBound hVu hp0.1
      (fun s _ => abs_vrev_le hM hp0 s) _ hz).trans (RegCont.revBound_mono hp0.2))
    (Real.sqrt_le_sqrt (by linarith [hp0.2])) (le_max_left _ _) (le_max_right _ _)
    (by linarith)
  have key := abs_energy_push_le_explicit hVu hp0.1 (K := K) hK0 hKb hC₀ hLA hsupp hαH hF
    one_pos hlα hS hρ hρ1
  have hαR : ∀ᵐ z ∂α, ‖z‖ ≤ R := hsuppae.mono fun z hz => mem_closedBall_zero_iff.1 hz.1
  have hmuα : (σ.map fun w => fwdMap W τ ((a : ℂ) * w)) = α :=
    Measure.map_congr ((ae_mem_foldSph d hr.le).mono fun x hx => (gA_of_mem hx).symm)
  have hmuρ : muA0 W d r p ρ = (α.bind fun z => foldedCircle z ρ).map (revMap (vrev W τ) τ) := by
    unfold muA0
    rw [hmuα]
    refine Measure.map_congr ?_
    filter_upwards [CoordReg.bind_fc_mem_H_norm α hρ hαR] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hp0.1 hx.1
  have hmu0 : muA0 W d r p 0 = α.map (revMap (vrev W τ) τ) := by
    unfold muA0
    rw [hmuα, bindFc_zero_of_ae_H hαH]
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hp0.1 hx
  rw [hmuρ, hmu0]
  refine key.trans ?_
  have h1 : (α Set.univ).toReal = 1 := by simp
  have h2 : α.real univ = 1 := probReal_univ
  rw [h1, h2]
  have hpow : ρ ^ (1 : ℝ) ≤ ρ ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hρ.le hρ1 (by norm_num) (by norm_num)
  have hp4 : 0 ≤ ρ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hρ.le _
  have hM1le : 2 * (K * 1 + 3 * (C₀ * 1 + ∫ z, |Real.log z.im| ∂α)) + 3 * 1 * (C₀ + 2) ≤ M₁ := by
    rw [hM₁]; linarith
  have e1 : 2 * (CF * ρ ^ (1 : ℝ) / 1) * 1 = 2 * CF * ρ ^ (1 : ℝ) := by ring
  rw [e1]
  have t1 : 2 * CF * ρ ^ (1 : ℝ) ≤ 2 * CF * ρ ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have t2 : 2 * (2 * (K * 1 + 3 * (C₀ * 1 + ∫ z, |Real.log z.im| ∂α)) + 3 * 1 * (C₀ + 2)) *
      (cS * ρ ^ (1 / 4 : ℝ)) ≤ 2 * M₁ * (cS * ρ ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  nlinarith [t1, t2]

end ASep
end QuantumZipper
