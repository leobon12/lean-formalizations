import HigherDimLQGMetric.LfppTight.MedianSmallFinal
import HigherDimLQGMetric.LfppTight.CenteredTight
import HigherDimLQGMetric.LfppTight.TightScalarTail
import HigherDimLQGMetric.LfppTight.SphereMeanVariance
import HigherDimLQGMetric.LfppTight.MedianPos

/-! A7(4): tightness of the normalized LGF LFPP metric for small cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

theorem l6a_ae_raw_eq_scaled_centered {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ a : ℝ) {ε : ℝ} (hε : 0 < ε) (ha : 0 < a)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) =ᵐ[P]
      (fun ω => ((a / aEps κ ξ ε) *
        Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) •
          l6a_metricOfFieldC ξ a⁻¹
            (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))) := by
  have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε
  filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh] with ω hc
  have hraw : Continuous fun z => convMollify κ ε (h ω) z := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hp : (ε, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) := ⟨hε, trivial⟩
    have hO : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d))) :=
      isOpen_Ioi.prod isOpen_univ
    exact (hc.continuousAt (hO.mem_nhds hp)).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hcent : Continuous (convMollifyNorm κ ε (h ω)) := hraw.sub continuous_const
  have hdist : Continuous (lfppDist κ ξ ε (h ω)) := by
    change Continuous (fun p : Rd d × Rd d =>
      DGZ.lfppMetric ξ (convMollify κ ε (h ω)) p.1 p.2)
    exact DGZ.continuous_lfppMetric hraw ξ
  apply ContinuousMap.ext
  intro p
  rw [toCMapRd_apply_of_continuous
    (hdist.const_smul (aEps κ ξ ε)⁻¹),
    show l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) =
      (⟨convMollifyNorm κ ε (h ω), hcent⟩ : C(Rd d, ℝ)) from dite_eq_left hcent,
    l6a_metricOfFieldC]
  simp only [ContinuousMap.smul_apply]
  change ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p =
    (a / aEps κ ξ ε * Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) •
      (toCMapRd (a⁻¹ • fieldLfpp ξ (convMollifyNorm κ ε (h ω)))) p
  rw [toCMapRd_apply_of_continuous
      ((continuous_fieldLfpp hcent).const_smul a⁻¹)]
  simp only [Pi.smul_apply, smul_eq_mul,
    fieldLfpp_eq_lfppDistOn hcent p]
  rw [l6a_lfppDist_sphereMean_split]
  field_simp [ha.ne', hae.ne']

theorem l6a_tight_medianFactor {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (G : ℝ → Rd d → Ω' → ℝ)
    (S : Set ℝ) (hS : S ⊆ Ioo (0 : ℝ) 1)
    {m : ℝ} (hm : 0 < m)
    (ha : ∀ ε ∈ S, 0 < DGZ.aHat P' G ξ ε)
    (hmed : ∀ ε ∈ S, m ^ 2 * DGZ.aHat P' G ξ ε ≤ aEps κ ξ ε) :
    IsTightMeasureSet {ν : Measure ℝ | ∃ ε ∈ S,
      ν = P.map (fun ω =>
        (DGZ.aHat P' G ξ ε / aEps κ ξ ε) *
          Real.exp (ξ * l6a_convSphereMean κ ε (h ω)))} := by
  let A : ℝ → Ω → ℝ := fun ε ω =>
    (DGZ.aHat P' G ξ ε / aEps κ ξ ε) *
      Real.exp (ξ * l6a_convSphereMean κ ε (h ω))
  have hAm : ∀ ε ∈ S, AEMeasurable (A ε) P := by
    intro ε hε
    have hX := l6a_aemeasurable_sphereMean hd κ hκ P h hh (hS hε).1
    have he : AEMeasurable
        (fun ω => Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) P :=
      Real.continuous_exp.measurable.comp_aemeasurable (hX.const_mul ξ)
    exact he.const_mul _
  have hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      Var[fun ω => l6a_convSphereMean κ ε (h ω); P] ≤ C :=
    l6a_uniform_sphereMean_variance hd κ hκ P h hh
  obtain ⟨C, hC0, hVar⟩ := hC
  apply l6a_tight_scalar_of_abs_tail P S A hAm
  intro θ hθ
  obtain ⟨L, hL, hXtail⟩ := l6a_uniform_sphereMean_tail_of_variance
    hd κ hκ P h hh hC0 hVar hθ
  let M : ℝ := (m ^ 2)⁻¹ * Real.exp (|ξ| * L) + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro ε hε
  have hε1 := hS hε
  have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε1.1
  have hratio0 : 0 ≤ DGZ.aHat P' G ξ ε / aEps κ ξ ε := by
    exact div_nonneg (ha ε hε).le hae.le
  have hratio : DGZ.aHat P' G ξ ε / aEps κ ξ ε ≤ (m ^ 2)⁻¹ := by
    apply (div_le_iff₀ hae).2
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have h : DGZ.aHat P' G ξ ε ≤ aEps κ ξ ε / m ^ 2 :=
      (le_div_iff₀ hm2).2 (by nlinarith [hmed ε hε])
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hsub : {ω | M < |A ε ω|} ⊆
      {ω | L < |l6a_convSphereMean κ ε (h ω)|} := by
    intro ω hbad
    by_contra hn
    have hX : |l6a_convSphereMean κ ε (h ω)| ≤ L := le_of_not_gt hn
    have hprod : ξ * l6a_convSphereMean κ ε (h ω) ≤ |ξ| * L := by
      have hh : |ξ * l6a_convSphereMean κ ε (h ω)| ≤ |ξ| * L := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hX (abs_nonneg ξ)
      exact (le_abs_self _).trans hh
    have he := Real.exp_le_exp.mpr hprod
    have hAle : |A ε ω| ≤ (m ^ 2)⁻¹ * Real.exp (|ξ| * L) := by
      dsimp [A]
      rw [abs_of_nonneg (mul_nonneg hratio0 (Real.exp_pos _).le)]
      exact (mul_le_mul_of_nonneg_left he hratio0).trans
        (mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le)
    change (m ^ 2)⁻¹ * Real.exp (|ξ| * L) + 1 < |A ε ω| at hbad
    linarith
  exact (measure_mono hsub).trans (hXtail ε hε1)

theorem l6a_small_normalized_tight (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      IsTightMeasureSet {μ : Measure C(Rd d × Rd d, ℝ) |
        ∃ ε ∈ Ioo (0 : ℝ) ε₀,
          μ = P.map (fun ω =>
            toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))} := by
  have hgap : 0 < ξ * (Q - Real.sqrt (2 * d)) :=
    mul_pos hDGZ.xi_pos (by linarith [hDGZ.subcritical])
  let β := ξ * (Q - Real.sqrt (2 * d)) / 2
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ : β < ξ * (Q - Real.sqrt (2 * d)) := by dsimp [β]; linarith
  obtain ⟨_, hExists⟩ := HigherDimLFPP.field_exists_impl d
    (by have := hDGZ.dim; omega : 1 ≤ d)
  obtain ⟨Ω', _, P', W, G, hP', hW, hG⟩ := hExists κ hDGZ.kernel
  letI : IsProbabilityMeasure P' := hP'
  obtain ⟨m, M, ε₀, hm, _, hε₀, hmedian⟩ :=
    l6a_median_comparison_small_final hL1e hDGZ hAdapter hβ0 hβ
      P h hh P' W hW G hG
  let εs := min ε₀ (1 / 2)
  have hεs : 0 < εs := lt_min hε₀ (by norm_num)
  have hεs1 : εs ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let S : Set ℝ := Ioo 0 εs
  let a : ℝ → ℝ := DGZ.aHat P' G ξ
  let A : ℝ → Ω → ℝ := fun ε ω =>
    (a ε / aEps κ ξ ε) * Real.exp (ξ * l6a_convSphereMean κ ε (h ω))
  let D : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω =>
    l6a_metricOfFieldC ξ (a ε)⁻¹
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω =>
    toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  have hS : S ⊆ Ioo (0 : ℝ) 1 := by
    intro ε hε
    exact ⟨hε.1, hε.2.trans_le hεs1⟩
  have hSmed (ε : ℝ) (hε : ε ∈ S) : ε ∈ Ioo (0 : ℝ) ε₀ :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have ha (ε : ℝ) (hε : ε ∈ S) : 0 < a ε :=
    DGZ.aHat_pos (by have := hDGZ.dim; omega : 0 < d)
      hW (hG ε (hS hε)) ξ
  have hmed (ε : ℝ) (hε : ε ∈ S) :
      m ^ 2 * a ε ≤ aEps κ ξ ε :=
    (hmedian ε (hSmed ε hε)).1
  have hAm : ∀ ε ∈ S, AEMeasurable (A ε) P := by
    intro ε hε
    have hX := l6a_aemeasurable_sphereMean hDGZ.dim κ hDGZ.kernel
      P h hh (hS hε).1
    have he : AEMeasurable
        (fun ω => Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) P :=
      Real.continuous_exp.measurable.comp_aemeasurable (hX.const_mul ξ)
    exact he.const_mul _
  have hDm : ∀ ε ∈ S, AEMeasurable (D ε) P := by
    intro ε hε
    exact l6a_aemeasurable_centered_metric hDGZ.dim κ hDGZ.kernel ξ
      (a ε)⁻¹ (hS hε).1 P h hh
  have hAt : IsTightMeasureSet {ν : Measure ℝ | ∃ ε ∈ S, ν = P.map (A ε)} :=
    l6a_tight_medianFactor hDGZ.dim κ hDGZ.kernel ξ P h hh
      P' G S hS hm ha hmed
  have hDt : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ S, ν = P.map (D ε)} := by
    apply (l6a_centered_tight hL1e hDGZ hAdapter P h hh P' W hW G hG).subset
    rintro ν ⟨ε, hε, rfl⟩
    exact ⟨ε, hS hε, rfl⟩
  have hT := l6a_tight_random_scale P S A D hAm hDm hAt hDt
  refine ⟨εs, hεs, hεs1, ?_⟩
  apply hT.subset
  rintro ν ⟨ε, hε, rfl⟩
  refine ⟨ε, hε, ?_⟩
  have heq : B ε =ᵐ[P] fun ω => A ε ω • D ε ω :=
    l6a_ae_raw_eq_scaled_centered hDGZ.dim κ hDGZ.kernel ξ (a ε)
      (hS hε).1 (ha ε hε) P h hh
  exact Measure.map_congr heq

end HigherDimLQGMetric
