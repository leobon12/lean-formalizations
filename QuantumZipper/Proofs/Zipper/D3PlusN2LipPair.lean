import QuantumZipper.Proofs.Zipper.D3PlusN2LipCore
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-LIPDET (a): passing to the limit of vanishing circle smoothing

For a regular witness `F` (continuous on `Hbar × (0,∞)`, recovered from itself by vanishing
circle smoothing locally uniformly: clause (ii) of `IsRegularWith`), a `C¹` test function `φ`
vanishing off a compact `K` with `cthickening r K ⊆ H`, and a first-mode bound `C₀/√τ` for the
`s`-smoothed field on circles centred in `K` (`s < τ < τ₀`), the pairings satisfy

`|∫ (F(u,t) − F(u,t')) φ(u) du| ≤ |K| · L · max C₀ 0 · 2√t`   for `0 < t' ≤ t < min r τ₀`

(`n2Lip_pair_smooth`). Proof: replace `F(·,τ)` by its smoothing at a small radius `ρ < t'`
(uniformly close on `K × [t', t]`) and apply `n2Lip_core_bound` to `g = F(foldH ·, ρ)`.
Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped Real Topology

namespace QuantumZipper
namespace D3Plus

/-- If `X ≤ B + D ε` for all small `ε > 0`, then `X ≤ B`. -/
theorem n2Lip_le_of_small {X B D r : ℝ} (hr : 0 < r)
    (h : ∀ ε, 0 < ε → ε ≤ r → X ≤ B + D * ε) : X ≤ B := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  set ε := min r (η / (|D| + 1)) with hε
  have hε0 : 0 < ε := lt_min hr (by positivity)
  have h1 := h ε hε0 (min_le_left _ _)
  have h2 : D * ε ≤ |D| * (η / (|D| + 1)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self D) hε0.le).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg D))
  have h3 : |D| * (η / (|D| + 1)) < η := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg D]
  linarith

/-- Integrability of a function continuous on a compact set and vanishing off it. -/
theorem n2Lip_intK {h : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K) (hh : ContinuousOn h K)
    (h0 : ∀ z ∉ K, h z = 0) : Integrable h :=
  (hh.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero h0

/-- **Smooth test functions**: the pairing increment bound. -/
theorem n2Lip_pair_smooth {F : ℂ × ℝ → ℝ} (hcont : ContinuousOn F (Hbar ×ˢ Ioi 0))
    (hlim : TendstoLocallyUniformlyOn
      (fun (ρ : ℝ) (p : ℂ × ℝ) => ∫ u, F (u, ρ) ∂foldedCircle p.1 p.2) F (𝓝[>] 0)
      (Hbar ×ˢ Ioi 0))
    {K : Set ℂ} (hK : IsCompact K) {r : ℝ} (hrK : Metric.cthickening r K ⊆ H) {C₀ τ₀ : ℝ}
    (hmode : ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
      ‖∫ θ in (0 : ℝ)..(2 * π),
          ((F (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), s) : ℝ) : ℂ) *
            Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C₀ / Real.sqrt τ)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφK : ∀ z ∉ K, φ z = 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u, ‖fderiv ℝ φ u‖ ≤ L) {t' t : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (htr : t < r)
    (ht0 : t < τ₀) :
    |∫ u, (F (u, t) - F (u, t')) * φ u| ≤ volume.real K * L * max C₀ 0 * (2 * Real.sqrt t) := by
  set M := max C₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hr0 : 0 < r := ht'.trans_le htt |>.trans htr
  have hKH : K ⊆ H := (Metric.self_subset_cthickening K).trans hrK
  have hKHb : K ⊆ Hbar := hKH.trans H_subset_Hbar
  obtain ⟨Bφ, hBφ⟩ := (n2Lip_hcs hK hφK).exists_bound_of_continuous hφ.continuous
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0)
  have hFt : ∀ τ, 0 < τ → ContinuousOn (fun u => F (u, τ)) Hbar := fun τ hτ =>
    hcont.comp (continuousOn_id.prodMk continuousOn_const) fun z hz => ⟨hz, hτ⟩
  -- uniform convergence on the compact set `K × [t', t]`
  have hS : IsCompact (K ×ˢ Icc t' t) := hK.prod isCompact_Icc
  have hSsub : K ×ˢ Icc t' t ⊆ Hbar ×ˢ Ioi 0 := fun p hp =>
    ⟨hKHb hp.1, show 0 < p.2 from ht'.trans_le hp.2.1⟩
  have hU := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).1
    (hlim.mono hSsub)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  refine n2Lip_le_of_small (D := 2 * Bφ * volume.real K) zero_lt_one fun ε hε _ => ?_
  obtain ⟨ρ, hρU, hρ⟩ := ((hU ε hε).and (Ioo_mem_nhdsGT ht')).exists
  have hρ0 : 0 < ρ := hρ.1
  set g : ℂ → ℝ := fun z => F (foldH z, ρ) with hg
  have hgc : Continuous g := RegClosure.continuous_comp_foldH (hFt ρ hρ0)
  set Φ : ℂ → ℝ → ℝ := fun u τ => ∫ v, F (v, ρ) ∂foldedCircle u τ with hΦ
  have hΦeq : ∀ u τ, Φ u τ = (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), g (u + (τ : ℂ) * n2LipE θ) := by
    intro u τ
    simp only [hΦ]
    rw [RegClosure.integral_fc_eq (hFt ρ hρ0), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity)]
    rfl
  set I : ℝ → ℂ → ℝ := fun τ u => ∫ θ in Icc 0 (2 * π), g (u + (τ : ℂ) * n2LipE θ) with hI
  have hIc : ∀ τ : ℝ, Continuous (I τ) := fun τ =>
    continuous_parametric_integral_of_continuous
      (f := fun (u : ℂ) (θ : ℝ) => g (u + (τ : ℂ) * n2LipE θ))
      (by have := continuous_n2LipE; fun_prop) isCompact_Icc
  have hΦc : ∀ τ : ℝ, Continuous fun u => Φ u τ := fun τ => by
    simp_rw [hΦeq]; exact continuous_const.mul (hIc τ)
  -- the three pieces
  have hFK : ∀ τ, 0 < τ → ContinuousOn (fun u => F (u, τ)) K := fun τ hτ => (hFt τ hτ).mono hKHb
  have hpt : ∀ u, (F (u, t) - F (u, t')) * φ u =
      ((F (u, t) - Φ u t) * φ u - (F (u, t') - Φ u t') * φ u) + (Φ u t - Φ u t') * φ u := by
    intro u; ring
  have hint1 : ∀ τ, 0 < τ → Integrable fun u => (F (u, τ) - Φ u τ) * φ u := fun τ hτ =>
    n2Lip_intK hK (((hFK τ hτ).sub (hΦc τ).continuousOn).mul hφ.continuous.continuousOn)
      (fun z hz => by simp [hφK z hz])
  have hint2 : Integrable fun u => (Φ u t - Φ u t') * φ u :=
    n2Lip_intK hK ((((hΦc t).sub (hΦc t')).mul hφ.continuous).continuousOn)
      (fun z hz => by simp [hφK z hz])
  simp_rw [hpt]
  rw [integral_add (f := fun u => (F (u, t) - Φ u t) * φ u - (F (u, t') - Φ u t') * φ u)
      ((hint1 t (ht'.trans_le htt)).sub (hint1 t' ht')) hint2,
    integral_sub (hint1 t (ht'.trans_le htt)) (hint1 t' ht')]
  -- smoothing errors
  have herr : ∀ τ ∈ Icc t' t, |∫ u, (F (u, τ) - Φ u τ) * φ u| ≤ ε * Bφ * volume.real K := by
    intro τ hτ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun z hz => by simp [hφK z hz]), ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun u hu => ?_)
    have h1 := (hρU (u, τ) ⟨hu, hτ⟩).le
    rw [Real.dist_eq] at h1
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul h1 (hBφ u) (norm_nonneg _) hε.le
  -- main term
  have hmain : |∫ u, (Φ u t - Φ u t') * φ u| ≤ volume.real K * L * M * (2 * Real.sqrt t) := by
    have hcs : ∀ τ : ℝ, Integrable fun u => φ u * I τ u := fun τ =>
      (hφ.continuous.mul (hIc τ)).integrable_of_hasCompactSupport (n2Lip_hcs hK hφK).mul_right
    have heq : ∫ u, (Φ u t - Φ u t') * φ u =
        (2 * π)⁻¹ * ((∫ u, φ u * I t u) - ∫ u, φ u * I t' u) := by
      rw [← integral_sub (hcs t) (hcs t'), ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [hΦeq, hI]
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    have hb := n2Lip_core_bound hgc hφ hK hφK hL0 hL hM ht' htt (fun u hu τ hτ => ?_)
    · have h2π : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
      have h0 : 0 ≤ volume.real K * L * M * (2 * Real.sqrt t) := by positivity
      calc (2 * π)⁻¹ * |(∫ u, φ u * I t u) - ∫ u, φ u * I t' u|
          ≤ 1 * (volume.real K * L * M * (2 * Real.sqrt t)) :=
            mul_le_mul h2π hb (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have hτ0 : 0 < τ := ht'.trans_le hτ.1
      refine le_trans (le_of_eq ?_) ((hmode u hu τ ⟨hτ0, hτ.2.trans_lt ht0⟩ ρ
        ⟨hρ0, hρ.2.trans_le hτ.1⟩).trans
          (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
      congr 1
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hmem : u + (τ : ℂ) * n2LipE θ ∈ Hbar := by
        refine H_subset_Hbar (hrK (Metric.mem_cthickening_of_dist_le _ u r K hu ?_))
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_n2LipE, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hτ0, mul_one]
        exact hτ.2.trans htr.le
      simp only [hg, CircleFubini.foldH_of_mem' hmem]
      rfl
  have h1 := herr t ⟨htt, le_rfl⟩
  have h2 := herr t' ⟨le_rfl, htt⟩
  calc |(∫ u, (F (u, t) - Φ u t) * φ u) - (∫ u, (F (u, t') - Φ u t') * φ u) +
        ∫ u, (Φ u t - Φ u t') * φ u|
      ≤ |∫ u, (F (u, t) - Φ u t) * φ u| + |∫ u, (F (u, t') - Φ u t') * φ u| +
          |∫ u, (Φ u t - Φ u t') * φ u| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by nlinarith

end D3Plus
end QuantumZipper
