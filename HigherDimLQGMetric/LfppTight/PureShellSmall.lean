import HigherDimLQGMetric.LfppTight.ShellScalar
import HigherDimLQGMetric.LfppTight.SmallTight

/-! Uniform lower shell tails for the normalized LGF at small cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

theorem l6a_pure_shell_tail_small (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (c : Rd d) {r₁ r₂ θ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) (hθ : 0 < θ) :
    ∃ m ε₀ : ℝ, 0 < m ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m} ≤
          ENNReal.ofReal θ := by
  have hgap : 0 < ξ * (Q - Real.sqrt (2 * d)) :=
    mul_pos hDGZ.xi_pos (by linarith [hDGZ.subcritical])
  let β := ξ * (Q - Real.sqrt (2 * d)) / 2
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ : β < ξ * (Q - Real.sqrt (2 * d)) := by dsimp [β]; linarith
  obtain ⟨_, hExists⟩ := HigherDimLFPP.field_exists_impl d
    (by have := hDGZ.dim; omega : 1 ≤ d)
  obtain ⟨Ω', _, P', W, G, hP', hW, hG⟩ := hExists κ hDGZ.kernel
  letI : IsProbabilityMeasure P' := hP'
  obtain ⟨_, M, εm, _, hM, hεm, hmed⟩ :=
    l6a_median_comparison_small_final hL1e hDGZ hAdapter hβ0 hβ
      P h hh P' W hW G hG
  have hq : 0 < θ / 2 := by positivity
  obtain ⟨C, hC0, hVar⟩ := l6a_uniform_sphereMean_variance
    hDGZ.dim κ hDGZ.kernel P h hh
  obtain ⟨L, hL, hXtail⟩ := l6a_uniform_sphereMean_tail_of_variance
    hDGZ.dim κ hDGZ.kernel P h hh hC0 hVar hq
  obtain ⟨m₀, εs, hm₀, hεs, hshell⟩ :=
    l6a_centered_shell_tail hL1e hDGZ hAdapter hβ0 hβ
      P h hh P' W hW G hG c hr₂ hr hq
  let M' : ℝ := max M 1
  let K : ℝ := M' ^ 2
  let m : ℝ := m₀ / (K * Real.exp (|ξ| * L))
  let ε₀ : ℝ := min εm (min εs (1 / 2))
  have hM' : 0 < M' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hK : 0 < K := by dsimp [K]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hε₀ : 0 < ε₀ := lt_min hεm (lt_min hεs (by norm_num))
  refine ⟨m, ε₀, hm, hε₀, ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (by norm_num)))⟩
  have hεm : ε ∈ Ioo (0 : ℝ) εm :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hεs : ε ∈ Ioo (0 : ℝ) εs :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have ha : 0 < DGZ.aHat P' G ξ ε :=
    DGZ.aHat_pos (by have := hDGZ.dim; omega) hW (hG ε hε1) ξ
  have hae : 0 < aEps κ ξ ε :=
    l6a_aEps_pos hDGZ.dim κ hDGZ.kernel ξ hε.1
  have hmed' : aEps κ ξ ε ≤ K * DGZ.aHat P' G ξ ε := by
    have hMm : M ≤ M' := le_max_left _ _
    have hsq : M ^ 2 ≤ M' ^ 2 := by nlinarith
    exact (hmed ε hεm).2.trans
      (mul_le_mul_of_nonneg_right hsq ha.le)
  let D : Ω → C(Rd d × Rd d, ℝ) := fun ω =>
    l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))
  let B : Ω → C(Rd d × Rd d, ℝ) := fun ω =>
    toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  let X : Ω → ℝ := fun ω => l6a_convSphereMean κ ε (h ω)
  have heq : B =ᵐ[P] fun ω =>
      ((DGZ.aHat P' G ξ ε / aEps κ ξ ε) * Real.exp (ξ * X ω)) • D ω :=
    l6a_ae_raw_eq_scaled_centered hDGZ.dim κ hDGZ.kernel ξ
      (DGZ.aHat P' G ξ ε) hε.1 ha P h hh
  have hsub : ∀ᵐ ω ∂P,
      DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (B ω) ≤ m →
        L < |X ω| ∨
        DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (D ω) ≤ m₀ := by
    filter_upwards [heq] with ω heqω hbad
    by_contra hn
    push Not at hn
    have hfactor : (K * Real.exp (|ξ| * L))⁻¹ ≤
        (DGZ.aHat P' G ξ ε / aEps κ ξ ε) * Real.exp (ξ * X ω) :=
      l6a_medianFactor_lower hae ha hK hmed' hn.1
    have hfpos : 0 < (DGZ.aHat P' G ξ ε / aEps κ ξ ε) *
        Real.exp (ξ * X ω) := mul_pos (div_pos ha hae) (Real.exp_pos _)
    rw [heqω, l6a_nd_setInf_smul _ _ _ hfpos.le] at hbad
    have hml : m < (K * Real.exp (|ξ| * L))⁻¹ *
        DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (D ω) := by
      have he : 0 < (K * Real.exp (|ξ| * L))⁻¹ := inv_pos.mpr (mul_pos hK (Real.exp_pos _))
      calc
        m = (K * Real.exp (|ξ| * L))⁻¹ * m₀ := by
          dsimp [m]
          field_simp
        _ < _ := mul_lt_mul_of_pos_left hn.2 he
    have hdnonneg : 0 ≤ DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (D ω) :=
      le_of_lt (hm₀.trans hn.2)
    have hle := mul_le_mul_of_nonneg_right hfactor hdnonneg
    linarith
  have hbad := (measure_mono_ae hsub).trans (measure_union_le
    {ω | L < |X ω|}
    {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (D ω) ≤ m₀})
  calc
    P {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (B ω) ≤ m} ≤
        P {ω | L < |X ω|} +
          P {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁) (D ω) ≤ m₀} := hbad
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
      add_le_add (hXtail ε hε1) (hshell ε hεs)
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hq.le hq.le]
      congr 1
      ring

end HigherDimLQGMetric
