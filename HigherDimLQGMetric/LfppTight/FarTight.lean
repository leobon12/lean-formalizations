import HigherDimLQGMetric.LfppTight.FarMedianRaw
import HigherDimLQGMetric.LfppTight.MetricLawMeas
import HigherDimLQGMetric.DGZ.TightCompact

/-! Tightness of normalized LGF LFPP on a compact cutoff interval away from zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_aemeasurable_raw_metric {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    AEMeasurable (fun ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) P := by
  have hm (z : Rd d) : AEMeasurable (fun ω => convMollify κ ε (h ω) z) P :=
    ((l10a_measurable_convMollify_apply κ ε z).comp hh.1.measurable).aemeasurable
  have hc : ∀ᵐ ω ∂P, Continuous fun z => convMollify κ ε (h ω) z :=
    l10a_ae_continuous_convMollify hd κ hκ P h hh hε
  change AEMeasurable (fun ω => toCMapRd
    ((aEps κ ξ ε)⁻¹ • fun p : Rd d × Rd d =>
      HigherDimLFPP.lfppDistOn ξ (convMollify κ ε (h ω)) univ p.1 p.2)) P
  exact l6a_aemeasurable_lfppMetricLaw P ξ
    (aEps κ ξ ε)⁻¹ (fun z ω => convMollify κ ε (h ω) z) hm hc

theorem l6a_far_normalized_tight {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {a : ℝ} (ha : 0 < a) :
    IsTightMeasureSet {μ : Measure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ico a 1,
        μ = P.map (fun ω => toCMapRd
          ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))} := by
  obtain ⟨t, ht, hmed⟩ := l6a_aEps_lower_far hd κ hκ ξ hξ P h hh ha
  let X : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω => toCMapRd
    ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  let S : Set (Measure C(Rd d × Rd d, ℝ)) :=
    {μ | ∃ ε ∈ Ico a 1, μ = P.map (X ε)}
  change IsTightMeasureSet S
  have hmet : ∀ μ ∈ S, μ {f : C(Rd d × Rd d, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z,
        f (x, z) ≤ f (x, y) + f (y, z))} = 0 := by
    rintro μ ⟨ε, hε, rfl⟩
    have hε0 : 0 < ε := ha.trans_le hε.1
    have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε0
    have hXm := l6a_aemeasurable_raw_metric hd κ hκ ξ hε0 P h hh
    change AEMeasurable (X ε) P at hXm
    have hset := (DGZ.tc_isClosed_metricCond (X := Rd d)).isOpen_compl.measurableSet
    rw [show {f : C(Rd d × Rd d, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z,
        f (x, z) ≤ f (x, y) + f (y, z))} =
      {f : C(Rd d × Rd d, ℝ) |
        (∀ x, f (x, x) = 0) ∧ ∀ x y z,
          f (x, z) ≤ f (x, y) + f (y, z)}ᶜ from rfl,
      Measure.map_apply_of_aemeasurable hXm hset]
    apply ae_iff.mp
    filter_upwards [l10a_ae_continuous_convMollify hd κ hκ P h hh hε0]
      with ω hc
    have hdist : Continuous (lfppDist κ ξ ε (h ω)) := by
      change Continuous (fun p : Rd d × Rd d =>
        DGZ.lfppMetric ξ (convMollify κ ε (h ω)) p.1 p.2)
      exact DGZ.continuous_lfppMetric hc ξ
    have hval (p : Rd d × Rd d) : X ε ω p =
        (aEps κ ξ ε)⁻¹ * DGZ.lfppMetric ξ (convMollify κ ε (h ω)) p.1 p.2 := by
      change (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) p = _
      rw [toCMapRd_apply_of_continuous (hdist.const_smul _)]
      rfl
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [hval, DGZ.lfppMetric_self, mul_zero]
    · rw [hval, hval, hval, ← mul_add]
      exact mul_le_mul_of_nonneg_left (DGZ.lfppMetric_triangle hc x y z)
        (inv_pos.mpr hae).le
  have hloc : ∀ (j : ℕ) (θ : ℝ), 0 < θ → ∃ Mj : ℝ, 0 ≤ Mj ∧
      ∀ μ ∈ S,
        μ {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j,
          ∀ y ∈ closedBall (0 : Rd d) j,
            f (x, y) ≤ Mj * dist x y ^ (1 : ℝ)} ≤ ENNReal.ofReal θ := by
    intro j θ hθ
    obtain ⟨L, hL0, hfield⟩ := l6a_far_field_sup_tail hd κ hκ P h hh
      (a := a) (R := (j : ℝ) + 1) (θ := θ) ha hθ
    let Mj : ℝ := Real.exp (|ξ| * L) / t
    have hMj : 0 ≤ Mj := by dsimp [Mj]; positivity
    refine ⟨Mj, hMj, ?_⟩
    rintro μ ⟨ε, hε, rfl⟩
    have hε0 : 0 < ε := ha.trans_le hε.1
    have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε0
    have hXm := l6a_aemeasurable_raw_metric hd κ hκ ξ hε0 P h hh
    change AEMeasurable (X ε) P at hXm
    have hset := (DGZ.tc_isClosed_holderCond
      (β := (1 : ℝ)) (closedBall (0 : Rd d) j) Mj).isOpen_compl.measurableSet
    rw [show {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j,
      ∀ y ∈ closedBall (0 : Rd d) j,
        f (x, y) ≤ Mj * dist x y ^ (1 : ℝ)} =
      {f : C(Rd d × Rd d, ℝ) | ∀ x ∈ closedBall (0 : Rd d) j,
        ∀ y ∈ closedBall (0 : Rd d) j,
          f (x, y) ≤ Mj * dist x y ^ (1 : ℝ)}ᶜ from rfl,
      Measure.map_apply_of_aemeasurable hXm hset]
    have hcont := l10a_ae_continuous_convMollify hd κ hκ P h hh hε0
    have hsub : ∀ᵐ ω ∂P,
        (¬ ∀ x ∈ closedBall (0 : Rd d) j,
          ∀ y ∈ closedBall (0 : Rd d) j,
            X ε ω (x, y) ≤ Mj * dist x y ^ (1 : ℝ)) →
        (∃ η ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) ((j : ℝ) + 1),
          L < |convMollify κ η (h ω) z|) := by
      filter_upwards [hcont] with ω hc hbad
      by_contra hn
      have hL : ∀ z ∈ closedBall (0 : Rd d) ((j : ℝ) + 1),
          |convMollify κ ε (h ω) z| ≤ L := by
        intro z hz
        exact le_of_not_gt (fun hlt => hn ⟨ε, ⟨hε.1, hε.2.le⟩, z, hz, hlt⟩)
      have hdist : Continuous (lfppDist κ ξ ε (h ω)) := by
        change Continuous (fun p : Rd d × Rd d =>
          DGZ.lfppMetric ξ (convMollify κ ε (h ω)) p.1 p.2)
        exact DGZ.continuous_lfppMetric hc ξ
      have hval (p : Rd d × Rd d) : X ε ω p =
          (aEps κ ξ ε)⁻¹ * DGZ.lfppMetric ξ
            (convMollify κ ε (h ω)) p.1 p.2 := by
        change (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) p = _
        rw [toCMapRd_apply_of_continuous (hdist.const_smul _)]
        rfl
      apply hbad
      intro x hx y hy
      have hraw := l6a_fieldBound_localUpper (ξ := ξ) hc hL x hx y hy
      rw [hval, Real.rpow_one, dist_eq_norm]
      have hdist0 : 0 ≤ DGZ.lfppMetric ξ (convMollify κ ε (h ω)) x y :=
        DGZ.lfppMetric_nonneg ξ _ x y
      have hratio : (aEps κ ξ ε)⁻¹ ≤ t⁻¹ :=
        (inv_le_inv₀ hae ht).2 (hmed ε hε)
      calc
        (aEps κ ξ ε)⁻¹ * DGZ.lfppMetric ξ (convMollify κ ε (h ω)) x y ≤
            (aEps κ ξ ε)⁻¹ * (Real.exp (|ξ| * L) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hraw (inv_pos.mpr hae).le
        _ ≤ t⁻¹ * (Real.exp (|ξ| * L) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_right hratio (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        _ = Mj * ‖x - y‖ := by dsimp [Mj]; ring
    exact (measure_mono_ae hsub).trans hfield
  exact DGZ.isTightMeasureSet_of_holderBounds DGZ.tc_closedBall_mono
    DGZ.tc_closedBall_mem_nhds (by norm_num : (0 : ℝ) < 1) hmet hloc

end HigherDimLQGMetric
