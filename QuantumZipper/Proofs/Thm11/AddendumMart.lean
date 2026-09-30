import QuantumZipper.Proofs.Thm11.AddendumMartX

/-!
# Theorem 1.1 addendum, AD-4 + MF-5: `ExtIntStmt` and `ExtMartStmt` from `ExtMeasStmt`

Blueprint `blueprint/THM11_BLUEPRINT.md` §9 (AD-4), the addendum analogue of MF-6
(`MainMart.main_mart`).  Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797),
Theorem 1.1 addendum (p. 12), for `κ ∈ (4,8)`.

Proof of `ExtMartStmt` (following `MainMart.main_mart`): MF-5
(`FieldMart.integral_exp_fieldX_fieldV`) holds for every level `δ_n = δ₀/(n+2)`.  As `n → ∞`,
* `V^{δ_n}_T → ∬ ρρ V_T` for every path (`tendsto_fieldV_ext`, monotone limit);
* `X^{δ_n}_T → (𝔥^ext_T, ρ)` in `L¹(P)` (`tendsto_lintegral_rho_ext`: R19 left limits, uniform
  L² bound from the AD-3 energy identity, Vitali), hence in probability, hence a.s. along a
  subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`);
then dominated convergence along the subsequence (the integrands are bounded by
`exp(½∬|ρ||ρ|G)`).  `ExtIntStmt` is the second half of `tendsto_lintegral_rho_ext`.
Both use the joint measurability node `ExtMeasStmt` as a hypothesis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm11Asm

open FwdHolo FwdClock FrozenMart FieldMart NonSwallow MainMart Thm11Add Thm11Lyap

/-- **AD-4, integrability part**, from the measurability node. -/
theorem extIntStmt_of_meas (hMeas : ExtMeasStmt) : ExtIntStmt := by
  intro κ T hκ4 hκ8 hT Ω _ P B hB ρ
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB' : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  obtain ⟨hρsm, hρs, -⟩ := ρ.2
  obtain ⟨δ₀, hδ₀, hρδ₀⟩ := exists_im_pos_of_testFun ρ
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have h := (tendsto_lintegral_rho_ext (δn := fun n : ℕ => δ₀ / ((n : ℝ) + 2)) hB hB'm hB'c hB'
    hMeas hκ4 hκ8 hdrive hρsm.continuous hρs hδ₀ hρδ₀ (fun n => by positivity)
    (fun n => div_le_self hδ₀.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
    (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    T.toNNReal (by rw [hTT]; exact hT)).2
  filter_upwards [h, hdrive] with ω h hd
  rw [hTT, hd] at h
  exact h

/-- **AD-4 + MF-5** (`ExtMartStmt`), from the measurability node. -/
theorem extMartStmt_of_meas (hMeas : ExtMeasStmt) : ExtMartStmt := by
  intro κ T hκ4 hκ8 hT Ω _ P B hB ρ
  have hκ : 0 < κ := by linarith
  have hBpre := hB.toIsPreBrownianReal
  have hP : IsProbabilityMeasure P := hBpre.isGaussianProcess.isProbabilityMeasure
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB' : IsPreBrownianReal B' P :=
    hBpre.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  obtain ⟨hρsm, hρs, -⟩ := ρ.2
  have hρc : Continuous ρ.1 := hρsm.continuous
  obtain ⟨δ₀, hδ₀, hρδ₀⟩ := exists_im_pos_of_testFun ρ
  set Tn : ℝ≥0 := T.toNNReal with hTn
  have hTT : (Tn : ℝ) = T := Real.coe_toNNReal _ hT.le
  have hT' : 0 < (Tn : ℝ) := by rw [hTT]; exact hT
  set δn : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 2) with hδn
  have hδpos : ∀ n, 0 < δn n := fun n => by positivity
  have hδle : ∀ n, δn n ≤ δ₀ := fun n =>
    div_le_self hδ₀.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hδlim : Tendsto δn atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hδanti : StrictAnti δn := fun m n hmn => by
    simp only [hδn]
    exact div_lt_div_of_pos_left hδ₀ (by positivity) (by exact_mod_cast (by omega : m + 2 < n + 2))
  have hρδ : ∀ n, ∀ a : ℂ, a.im < δn n → ρ.1 a = 0 := fun n a h =>
    hρδ₀ a (h.trans_le (hδle n))
  have hc : ∀ n, 0 < δn n / 2 := fun n => by linarith [hδpos n]
  have hcδ : ∀ n, δn n / 2 ≤ δn n := fun n => by linarith [hδpos n]
  set 𝓕 := bmFilt hB'm with h𝓕
  set G0 : ℝ := ∫ p, ρ.1 p.1 * ρ.1 p.2 * greenH p.1 p.2 ∂((volume : Measure ℂ).prod
    (volume : Measure ℂ)) with hG0
  set Xn : ℕ → Ω → ℝ := fun n ω => fieldX κ (δn n / 2) (δn n) Tn B' ρ.1 Tn ω with hXn
  set Vn : ℕ → Ω → ℝ := fun n ω => fieldV κ (δn n / 2) (δn n) Tn B' ρ.1 Tn ω with hVn
  set X : Ω → ℝ := fun ω => ∫ z, ρ.1 z * hTfwdExt κ (drive κ B' ω) Tn z with hX
  set V : Ω → ℝ := fun ω => ∫ a, ∫ b, ρ.1 a * ρ.1 b * K3.VT (drive κ B' ω) Tn a b with hV
  set F : ℕ → Ω → ℂ := fun n ω => cexp (I * (Xn n ω : ℂ) - (Vn n ω : ℂ) / 2) with hF
  have hF5 : ∀ n, ∫ ω, F n ω ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) - (G0 : ℂ) / 2) := fun n =>
    integral_exp_fieldX_fieldV hB' hB'c 𝓕 (bmFilt_adapted hB'm) (bmFilt_le_past hB'm) hκ
      (hc n) (hcδ n) hρc hρs (hρδ n) Tn
  obtain ⟨hL1, hint⟩ := tendsto_lintegral_rho_ext hB hB'm hB'c hB' hMeas hκ4 hκ8 hdrive hρc hρs
    hδ₀ hρδ₀ hδpos hδle hδlim Tn hT'
  -- measurability
  have hXm : ∀ n, Measurable (Xn n) := fun n =>
    measurable_integral_mul_joint hρc.measurable
      (measurable_frozenField_amb (κ := κ) (δ := δn n) hB'c 𝓕 (bmFilt_adapted hB'm) (hc n) Tn Tn)
  have hVm : ∀ n, Measurable (Vn n) := fun n =>
    measurable_integral_mul_joint (μ := (volume : Measure ℂ).prod (volume : Measure ℂ))
      (ρ := fun p : ℂ × ℂ => ρ.1 p.1 * ρ.1 p.2)
      ((hρc.measurable.comp measurable_fst).mul (hρc.measurable.comp measurable_snd))
      (measurable_frozenKernel_amb (κ := κ) (δ := δn n) hB'c 𝓕 (bmFilt_adapted hB'm) (hc n)
        Tn Tn)
  have hXlim : Measurable X := by
    have h1 := (hMeas κ Tn hκ4 hκ8 hT' B' hB'm hB'c).comp measurable_swap
    simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] at h1
    exact measurable_integral_mul_joint hρc.measurable h1
  -- L¹ convergence of the fields
  have hbd : ∀ n, ∀ᵐ ω ∂P, ‖Xn n ω - X ω‖ₑ ≤ ∫⁻ a, ‖ρ.1 a‖ₑ *
      ‖frozenField κ (δn n / 2) (δn n) Tn B' a Tn ω - hTfwdExt κ (drive κ B' ω) Tn a‖ₑ := by
    intro n
    filter_upwards [hint] with ω hω
    have hin : Integrable fun a => ρ.1 a * frozenField κ (δn n / 2) (δn n) Tn B' a Tn ω := by
      refine Integrable.mono' ((hρc.integrable_of_hasCompactSupport hρs).abs.mul_const
        (fzBound κ (δn n / 2) Tn))
        ((hρc.measurable.mul ((measurable_frozenField_amb (κ := κ) (δ := δn n) hB'c 𝓕
          (bmFilt_adapted hB'm) (hc n) Tn Tn).comp
            (measurable_id.prodMk measurable_const))).aestronglyMeasurable) ?_
      refine ae_of_all _ fun a => ?_
      by_cases h0 : ρ.1 a = 0
      · simp [h0]
      have ha : δn n ≤ a.im := (hδle n).trans (not_lt.1 fun h => h0 (hρδ₀ a h))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_frozenField_le hB'c (hc n) ha Tn Tn ω)
        (abs_nonneg _)
    have e : Xn n ω - X ω = ∫ a, ρ.1 a *
        (frozenField κ (δn n / 2) (δn n) Tn B' a Tn ω - hTfwdExt κ (drive κ B' ω) Tn a) := by
      simp only [hXn, hX, fieldX, mul_sub]
      exact (integral_sub hin hω).symm
    rw [e]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp only [enorm_mul]
  have hXL1 : Tendsto (fun n => eLpNorm (Xn n - X) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1
      (fun n => bot_le) (fun n => ?_)
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_mono_ae (hbd n)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n => (hXm n).aestronglyMeasurable) hXlim.aestronglyMeasurable hXL1).exists_seq_tendsto_ae
  set Lim : Ω → ℂ := fun ω => cexp (I * (X ω : ℂ) - (V ω : ℂ) / 2) with hLim
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => F (ns k) ω) atTop (𝓝 (Lim ω)) := by
    filter_upwards [hae] with ω hXω
    have hVω := (tendsto_fieldV_ext hB'm hB'c (κ := κ) hρc hρs hδ₀ hρδ₀ hδpos hδle hδanti
      hδlim Tn ω).comp hns.tendsto_atTop
    exact (Complex.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hXω)).sub
        (((Complex.continuous_ofReal.tendsto _).comp hVω).div_const 2))
  set E : ℝ := ∫ p, |ρ.1 p.1| * |ρ.1 p.2| * greenH p.1 p.2 ∂((volume : Measure ℂ).prod
    (volume : Measure ℂ)) with hE
  have hFm : ∀ k, AEStronglyMeasurable (F (ns k)) P := fun k =>
    (Complex.measurable_exp.comp ((measurable_const.mul
      (Complex.measurable_ofReal.comp (hXm (ns k)))).sub
        ((Complex.measurable_ofReal.comp (hVm (ns k))).div_const 2))).aestronglyMeasurable
  have hFb : ∀ k, ∀ᵐ ω ∂P, ‖F (ns k) ω‖ ≤ Real.exp (E / 2) := fun k => ae_of_all _ fun ω => by
    have hv := abs_fieldV_le (κ := κ) hB'c (hc (ns k)) (hcδ (ns k)) hρc hρs (hρδ (ns k)) Tn Tn ω
    simp only [hF, Complex.norm_exp, re_I_mul_sub_div_two]
    rw [Real.exp_le_exp]
    linarith [(abs_le.1 hv).1]
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => Real.exp (E / 2)) hFm
    (integrable_const _) hFb hlim
  have hconst : ∫ ω, Lim ω ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) - (G0 : ℂ) / 2) :=
    tendsto_nhds_unique hDCT (by simp only [hF5]; exact tendsto_const_nhds)
  have hint2 : Integrable (fun p : ℂ × ℂ => ρ.1 p.1 * ρ.1 p.2 * greenH p.1 p.2)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    integrable_rho_rho_mul hρc hρs hδ₀ hρδ₀ (C := 0) measurable_greenH.aestronglyMeasurable
      (fun p hne ha hb => by
        rw [zero_add, abs_of_nonneg (greenH_nonneg (show 0 ≤ p.1.im by linarith)
          (show 0 ≤ p.2.im by linarith) hne)])
  have hE0 : G0 = ∫ x, ∫ y, ρ.1 x * ρ.1 y * greenH x y :=
    integral_prod (fun p : ℂ × ℂ => ρ.1 p.1 * ρ.1 p.2 * greenH p.1 p.2) hint2
  rw [← hE0, ← hconst]
  refine integral_congr_ae ?_
  filter_upwards [hdrive] with ω hω
  simp only [hLim, hX, hV, hω, hTT]

end Thm11Asm
end QuantumZipper
