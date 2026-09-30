import QuantumZipper.Proofs.Thm18.G1SSR2Par
import QuantumZipper.Proofs.Thm18.G1ProfileConv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (5): the profile part along pushed circles is jointly continuous up to `σ = 0`

Theorem 1.8, G1 zoom, toward `G1SidePushUCRepStmt`. For a radial profile `rp g` with
`|g t| ≤ C (1 - log t)` near `0` (the wedge profile of a good sample, `G1RC.bd_wg`) and a selected
side map `ψ` (`G1RC.PsiGood`), the function
`(d, r, σ) ↦ ∫ smoothFun (rp g) (S ψ z) (S σ) dfc(d, r)(z)` is continuous on
`{r > 0, σ ∈ [0, 1/S]}` (`continuousOn_profPush`): the integrand is jointly continuous on
`[0, 1/S] × ℍ` (`continuousOn_smoothFun_rp`, the smoothing tends to the profile off `0`) and has the
uniform majorant `B + 8C |log ‖S ψ‖| ≤ A + K |log Im|` (`G1RC.abs_smoothFun_rp_le`, Koebe
distortion `G1RC.logBd_log_norm`), so `continuousOn_integral_fc_param` applies. Own elementary
assembly of the estimates used for `G1ProfileStmt`.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1SSR2

open F1.RC3Two G1RC CA.Koebe

variable {g : ℝ → ℝ} {C : ℝ}

theorem smoothFun_rp_zero (g : ℝ → ℝ) (c : ℂ) : GoodSample.smoothFun (rp g) c 0 = rp g c := by
  unfold GoodSample.smoothFun
  rw [RegSample.fc_zero, integral_dirac]
  simp [rp, norm_foldH']

/-- `rp g` has a logarithmic bound in `Im` on bounded parts of `ℍ`. -/
theorem logBd_rp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) : LogBd (rp g) C := by
  have hC := nonneg_of_bd hbd
  refine ⟨hgm.comp measurable_norm, fun z hz => ?_, hC, fun R => ?_⟩
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 (ne_zero_of_mem_H' hz)
    exact ((hgc.continuousAt (Ioi_mem_nhds hpos)).comp
      continuous_norm.continuousAt).continuousWithinAt
  · obtain ⟨B, -, hB⟩ := abs_le_log_of_bd hgc hbd (|R| + 1)
    refine ⟨B + C * (|Real.log (|R| + 1)|), fun u hu huR => ?_⟩
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 (ne_zero_of_mem_H' hu)
    have h1 := hB ‖u‖ hpos (by linarith [le_abs_self R])
    have him : 0 < u.im := hu
    have hle : u.im ≤ ‖u‖ := Complex.im_le_norm u
    have h2 : |Real.log ‖u‖| ≤ |Real.log u.im| + |Real.log (|R| + 1)| := by
      rcases le_total ‖u‖ 1 with h | h
      · rw [abs_of_nonpos (Real.log_nonpos hpos.le h),
          abs_of_nonpos (Real.log_nonpos him.le (hle.trans h))]
        have := Real.log_le_log him hle
        linarith [abs_nonneg (Real.log (|R| + 1))]
      · rw [abs_of_nonneg (Real.log_nonneg h)]
        have := Real.log_le_log hpos (show ‖u‖ ≤ |R| + 1 by linarith [le_abs_self R])
        linarith [abs_nonneg (Real.log u.im), le_abs_self (Real.log (|R| + 1))]
    show |g ‖u‖| ≤ _
    nlinarith

/-- **Joint continuity of the smoothed profile on `ℍ × [0, ∞)`.** -/
theorem continuousOn_smoothFun_rp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) :
    ContinuousOn (fun q : ℂ × ℝ => GoodSample.smoothFun (rp g) q.1 q.2) (H ×ˢ Ici 0) := by
  have hL := logBd_rp hgm hgc hbd
  rintro ⟨c₀, ρ₀⟩ ⟨hc₀, hρ₀⟩
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ ρ₀ from hρ₀) with hpos | hzero
  · exact (hL.continuousOn.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (show (0 : ℝ) < (c₀, ρ₀).2 from hpos))).continuousWithinAt
  · subst hzero
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hne : c₀ ≠ 0 := ne_zero_of_mem_H' hc₀
    have hcont : ContinuousAt (rp g) c₀ :=
      (hgc.continuousAt (Ioi_mem_nhds (norm_pos_iff.2 hne))).comp continuous_norm.continuousAt
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
    refine ⟨δ / 2, by positivity, fun q hq hqd => ?_⟩
    obtain ⟨hqH, hq0⟩ := hq
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq] at hqd
    have hq0' : (0 : ℝ) ≤ q.2 := hq0
    have hsupp : ∀ᵐ u ∂foldedCircle q.1 q.2, |rp g u - rp g c₀| ≤ ε / 2 := by
      filter_upwards [foldedCircle_ae_dist_le' (H_subset_Hbar hqH) hq0'] with u hu
      have : dist u c₀ < δ := by
        have := dist_triangle u q.1 c₀
        rw [abs_lt] at hqd
        simp only [sub_zero] at hqd
        linarith [hqd.1, hqd.2.2]
      exact (hδε this).le
    have hint : Integrable (rp g) (foldedCircle q.1 q.2) := by
      refine (integrable_const (|rp g c₀| + ε / 2)).mono'
        (hgm.comp measurable_norm).aestronglyMeasurable ?_
      filter_upwards [hsupp] with u hu
      rw [Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (rp g u) (rp g c₀)
      linarith
    have e : GoodSample.smoothFun (rp g) q.1 q.2 - GoodSample.smoothFun (rp g) c₀ 0 =
        ∫ u, (rp g u - rp g c₀) ∂foldedCircle q.1 q.2 := by
      rw [smoothFun_rp_zero, integral_sub hint (integrable_const _)]
      simp [GoodSample.smoothFun]
    rw [Real.dist_eq, e, ← Real.norm_eq_abs]
    refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ε / 2) ?_) ?_
    · filter_upwards [hsupp] with u hu
      rwa [Real.norm_eq_abs]
    · simp only [probReal_univ, mul_one]
      linarith

/-- The pushed profile integrand. -/
def profInt (g : ℝ → ℝ) (ψ : ℂ → ℂ) (S σ : ℝ) (u : ℂ) : ℝ :=
  GoodSample.smoothFun (rp g) ((S : ℂ) * ψ u) (S * σ)

/-- **Joint continuity of the pushed profile part up to `σ = 0`.** -/
theorem continuousOn_profPush {ψ : ℂ → ℂ} (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S)
    (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) :
    ContinuousOn (fun p : ℂ × ℝ × ℝ => ∫ u, profInt g ψ S p.2.2 u ∂foldedCircle p.1 p.2.1)
      {p | 0 < p.2.1 ∧ p.2.2 ∈ Icc 0 (1 / S)} := by
  have hC := nonneg_of_bd hbd
  have hLn := logBd_log_norm hψ hS
  obtain ⟨-, -, hK₁, hLb⟩ := hLn
  set K := 8 * C * (1 + koebeDistExp) with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hC) hK₁
  -- measurability of the slices
  have hGm : ∀ σ ∈ Icc (0 : ℝ) (1 / S), Measurable (fun u => profInt g ψ S σ u / (K + 1)) := by
    intro σ hσ
    refine Measurable.div_const ?_ _
    rcases lt_or_eq_of_le hσ.1 with hpos | hzero
    · exact (continuous_smoothFun_rp hgm hgc hbd (mul_pos hS hpos)).measurable.comp
        (measurable_const.mul hψ.1)
    · subst hzero
      have e : (fun u => profInt g ψ S 0 u) = fun u => rp g ((S : ℂ) * ψ u) := by
        funext u; simp [profInt, smoothFun_rp_zero]
      rw [show profInt g ψ S 0 = fun u => rp g ((S : ℂ) * ψ u) from e]
      exact (hgm.comp measurable_norm).comp (measurable_const.mul hψ.1)
  -- joint continuity on `[0, 1/S] × ℍ`
  have hψc : ContinuousOn ψ H := hψ.2.1.continuousOn
  have hGc : ContinuousOn (fun q : ℝ × ℂ => profInt g ψ S q.1 q.2 / (K + 1))
      (Icc 0 (1 / S) ×ˢ H) := by
    refine ContinuousOn.div_const ?_ _
    refine (continuousOn_smoothFun_rp hgm hgc hbd).comp
      ((continuousOn_const.mul (hψc.comp continuousOn_snd fun q hq => hq.2)).prodMk
        (continuousOn_const.mul continuousOn_fst)) fun q hq =>
          ⟨mul_psi_mem_H hψ hS hq.2, show (0 : ℝ) ≤ S * q.1 from mul_nonneg hS.le hq.1.1⟩
  -- uniform bound
  have hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ σ ∈ Icc (0 : ℝ) (1 / S), ∀ u ∈ H, ‖u‖ ≤ R →
      |profInt g ψ S σ u / (K + 1)| ≤ A + |Real.log u.im| := by
    intro R
    obtain ⟨M, hM⟩ := norm_mul_psi_le hψ hS R
    obtain ⟨B, hB⟩ := abs_smoothFun_rp_le hgm hgc hbd M
    obtain ⟨B₀, -, hB₀⟩ := abs_le_log_of_bd hgc hbd (|M| + 1)
    obtain ⟨A₁, hA₁⟩ := hLb R
    refine ⟨(|B| + |B₀| + 8 * C * |A₁|) / (K + 1), by positivity, fun σ hσ u hu huR => ?_⟩
    have hc := mul_psi_mem_H hψ hS hu
    have hc0 : (S : ℂ) * ψ u ≠ 0 := ne_zero_of_mem_H' hc
    have hcM := hM u hu huR
    have hlog : |Real.log ‖(S : ℂ) * ψ u‖| ≤ A₁ + (1 + koebeDistExp) * |Real.log u.im| :=
      hA₁ u hu huR
    have hmain : |profInt g ψ S σ u| ≤ |B| + |B₀| + 8 * C * (|A₁| +
        (1 + koebeDistExp) * |Real.log u.im|) := by
      have hl2 : |Real.log ‖(S : ℂ) * ψ u‖| ≤ |A₁| + (1 + koebeDistExp) * |Real.log u.im| := by
        linarith [le_abs_self A₁]
      rcases lt_or_eq_of_le hσ.1 with hpos | hzero
      · have hS1 : S * σ ≤ 1 := by
          have := hσ.2
          rw [le_div_iff₀ hS] at this
          linarith
        have := hB _ hcM hc0 (S * σ) (mul_pos hS hpos) hS1
        have h8 := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ 8 * C)
        unfold profInt
        linarith [le_abs_self B, abs_nonneg B₀]
      · subst hzero
        have hpos : 0 < ‖(S : ℂ) * ψ u‖ := norm_pos_iff.2 hc0
        have := hB₀ _ hpos (by linarith [le_abs_self M])
        have h1 := mul_le_mul_of_nonneg_left hl2 hC
        have h8 : C * (|A₁| + (1 + koebeDistExp) * |Real.log u.im|) ≤
            8 * C * (|A₁| + (1 + koebeDistExp) * |Real.log u.im|) := by
          have : 0 ≤ C * (|A₁| + (1 + koebeDistExp) * |Real.log u.im|) :=
            mul_nonneg hC (add_nonneg (abs_nonneg _) (mul_nonneg hK₁ (abs_nonneg _)))
          linarith
        simp only [profInt, mul_zero, smoothFun_rp_zero]
        show |g ‖(S : ℂ) * ψ u‖| ≤ _
        linarith [le_abs_self B₀, abs_nonneg B]
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < K + 1), div_le_iff₀ (by linarith)]
    have hl0 := abs_nonneg (Real.log u.im)
    have : (|B| + |B₀| + 8 * C * |A₁|) / (K + 1) * (K + 1) = |B| + |B₀| + 8 * C * |A₁| := by
      field_simp
    rw [add_mul, this, hK]
    nlinarith
  have hpar := continuousOn_integral_fc_param hGm hGc hGb
  refine ((continuousOn_const (c := K + 1)).mul hpar).congr fun p _ => ?_
  show ∫ u, profInt g ψ S p.2.2 u ∂foldedCircle p.1 p.2.1 =
    (K + 1) * ∫ u, profInt g ψ S p.2.2 u / (K + 1) ∂foldedCircle p.1 p.2.1
  rw [integral_div]
  field_simp

end G1SSR2
end Thm18Asm
end QuantumZipper
