import HigherDimLQGMetric.Thm16.MedianSym
import HigherDimLQGMetric.Thm16.FullPointTail
import HigherDimLQGMetric.Thm16.CenteredPointTail
import HigherDimLQGMetric.Thm16.HalfIntersect
import HigherDimLQGMetric.LfppTight.MedianBridge

/-! A median comparison from Gaussian half spaces and two tight point laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ WN)

private theorem full_norm_point_eq {d : ℕ} (κ : Rd d → ℝ) (ξ ε : ℝ)
    (H : DistRd d) (hH : Continuous (convMollify κ ε H)) :
    (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε H)) (0, e₁ d) =
      (Real.exp (ξ * l6a_convSphereMean κ ε H) *
        DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d)) / aEps κ ξ ε := by
  have hD : Continuous (lfppDist κ ξ ε H) := by
    have heq : lfppDist κ ξ ε H = fieldLfpp ξ (convMollify κ ε H) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn hH p).symm
    rw [heq]
    exact continuous_fieldLfpp hH
  rw [toCMapRd_apply_of_continuous (hD.const_smul _)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [l6a_lfppDist_sphereMean_split, DGZ.lfppMetric]
  ring

theorem l9c_aEps_aHat_compare {d : ℕ} (hd : 3 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε)) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 < M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        m * DGZ.aHat P G ξ ε ≤ aEps κ ξ ε ∧
          aEps κ ξ ε ≤ M * DGZ.aHat P G ξ ε := by
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  obtain ⟨u, T, hu, hT, hfull⟩ :=
    l9c_full_point_tails hd hκ hξ hsub hB2 hL6a
  obtain ⟨m, M, ε₀, hm, hM, hε₀, hcenter⟩ :=
    l9c_centered_point_tails hd hκ hξ hsub hB2 P W hW G hG
  let m' : ℝ := m / T
  let M' : ℝ := max 1 M / u
  have hm' : 0 < m' := div_pos hm hT
  have hM' : 0 < M' := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hu
  let ε₀' : ℝ := min ε₀ (1 / 2)
  have hε₀' : 0 < ε₀' := lt_min hε₀ (by norm_num)
  refine ⟨m', M', ε₀', hm', hM', hε₀', ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  have hεcenter : ε ∈ Ioo (0 : ℝ) ε₀ :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  let Y : DistRd d → ℝ := fun H =>
    (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε H)) (0, e₁ d)
  let C : DistRd d → ℝ := fun H =>
    DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d)
  let A : DistRd d → ℝ := fun H => Real.exp (ξ * l6a_convSphereMean κ ε H)
  let BF : Set (DistRd d) := {H | Y H ≤ u ∨ T ≤ Y H}
  let BC : Set (DistRd d) :=
    {H | C H < m * DGZ.aHat P G ξ ε ∨ M * DGZ.aHat P G ξ ε < C H}
  let N : Set (DistRd d) := {H | ¬ Continuous (convMollify κ ε H)}
  have hBF : (normLGFLaw d) BF ≤ (8⁻¹ : ℝ≥0∞) := hfull ε hε1
  have hBC : (normLGFLaw d) BC ≤ (8⁻¹ : ℝ≥0∞) := hcenter ε hεcenter
  have hN : (normLGFLaw d) N = 0 := by
    have hc := l10a_ae_continuous_convMollify hd2 κ hκ
      (normLGFLaw d) id hn hε.1
    simpa only [N, Function.id_def, compl_ofPred] using (ae_iff.mp hc)
  have hhalf := l9c_sphereMean_half_sides hd2 hκ (normLGFLaw d) id hn hε.1
  have ha : 0 < aEps κ ξ ε := l6a_aEps_pos hd2 κ hκ ξ hε.1
  have hhat : 0 < DGZ.aHat P G ξ ε :=
    DGZ.aHat_pos (by omega : 0 < d) hW (hG ε hε1) ξ
  have hUpper : aEps κ ξ ε ≤ M' * DGZ.aHat P G ξ ε := by
    obtain ⟨H, hmean, hnoF, hnoC, hnoN⟩ :=
      l9c_exists_half_good (normLGFLaw d) hhalf.1 hBF hBC hN
    have hcont : Continuous (convMollify κ ε H) := by
      change H ∉ {H | ¬ Continuous (convMollify κ ε H)} at hnoN
      simpa only [mem_ofPred_eq, not_not] using hnoN
    have hYlo : u < Y H := lt_of_not_ge (fun h => hnoF (Or.inl h))
    have hClo : m * DGZ.aHat P G ξ ε ≤ C H :=
      le_of_not_gt (fun h => hnoC (Or.inl h))
    have hChi : C H ≤ M * DGZ.aHat P G ξ ε :=
      le_of_not_gt (fun h => hnoC (Or.inr h))
    have hmean' : l6a_convSphereMean κ ε H ≤ 0 := hmean
    have hAle : A H ≤ 1 := by
      have hh : ξ * l6a_convSphereMean κ ε H ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hξ.le hmean'
      simpa only [A, Real.exp_zero] using (Real.exp_le_exp.mpr hh)
    have hCnonneg : 0 ≤ C H := (mul_pos hm hhat).le.trans hClo
    have hYeq : Y H = A H * C H / aEps κ ξ ε :=
      full_norm_point_eq κ ξ ε H hcont
    rw [hYeq] at hYlo
    have hprod : u * aEps κ ξ ε < A H * C H :=
      (lt_div_iff₀ ha).mp hYlo
    have hAChi : A H * C H ≤ C H := by
      nlinarith [mul_le_mul_of_nonneg_right hAle hCnonneg]
    have hnum : u * aEps κ ξ ε ≤ max 1 M * DGZ.aHat P G ξ ε := by
      calc
        u * aEps κ ξ ε ≤ A H * C H := hprod.le
        _ ≤ C H := hAChi
        _ ≤ M * DGZ.aHat P G ξ ε := hChi
        _ ≤ max 1 M * DGZ.aHat P G ξ ε :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hhat.le
    dsimp [M']
    calc
      aEps κ ξ ε ≤ (max 1 M * DGZ.aHat P G ξ ε) / u :=
        (le_div_iff₀ hu).2 (by nlinarith [hnum])
      _ = max 1 M / u * DGZ.aHat P G ξ ε := by ring
  have hLower : m' * DGZ.aHat P G ξ ε ≤ aEps κ ξ ε := by
    obtain ⟨H, hmean, hnoF, hnoC, hnoN⟩ :=
      l9c_exists_half_good (normLGFLaw d) hhalf.2 hBF hBC hN
    have hcont : Continuous (convMollify κ ε H) := by
      change H ∉ {H | ¬ Continuous (convMollify κ ε H)} at hnoN
      simpa only [mem_ofPred_eq, not_not] using hnoN
    have hYhi : Y H < T := lt_of_not_ge (fun h => hnoF (Or.inr h))
    have hClo : m * DGZ.aHat P G ξ ε ≤ C H :=
      le_of_not_gt (fun h => hnoC (Or.inl h))
    have hmean' : 0 ≤ l6a_convSphereMean κ ε H := hmean
    have hAge : 1 ≤ A H := by
      have hh : 0 ≤ ξ * l6a_convSphereMean κ ε H :=
        mul_nonneg hξ.le hmean'
      simpa only [A, Real.exp_zero] using (Real.exp_le_exp.mpr hh)
    have hCnonneg : 0 ≤ C H := (mul_pos hm hhat).le.trans hClo
    have hYeq : Y H = A H * C H / aEps κ ξ ε :=
      full_norm_point_eq κ ξ ε H hcont
    rw [hYeq] at hYhi
    have hprod : A H * C H < T * aEps κ ξ ε :=
      (div_lt_iff₀ ha).mp hYhi
    have hCA : C H ≤ A H * C H := by
      nlinarith [mul_le_mul_of_nonneg_right hAge hCnonneg]
    have hnum : m * DGZ.aHat P G ξ ε ≤ T * aEps κ ξ ε :=
      hClo.trans (hCA.trans hprod.le)
    dsimp [m']
    calc
      m / T * DGZ.aHat P G ξ ε =
          (m * DGZ.aHat P G ξ ε) / T := by ring
      _ ≤ aEps κ ξ ε := (div_le_iff₀ hT).2 (by nlinarith [hnum])
  exact ⟨hLower, hUpper⟩

end HigherDimLQGMetric
