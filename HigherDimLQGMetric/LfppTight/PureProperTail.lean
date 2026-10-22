import HigherDimLQGMetric.LfppTight.CrossProperDet

/-! High-probability absolute distance to a sufficiently large sphere. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_pure_proper_tail (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, (n : ℝ) < R ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n)
        (sphere 0 R)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))} ≤
          ENNReal.ofReal θ := by
  let q : ℝ := min (θ / 4) (1 / 8)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  have hq1 : q ≤ 1 / 8 := min_le_right _ _
  have hqθ : 2 * q ≤ θ := by
    have hh := min_le_left (θ / 4) (1 / 8)
    dsimp [q]
    linarith
  let p : ℝ := 1 - q
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hp : p < 1 := by dsimp [p]; linarith
  obtain ⟨k, hsepTail⟩ := l6a_metricSep_tail hL1e hDGZ hAdapter
    P h hh 0 0 hq
  let δ : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let C : ℝ := ((n : ℝ) + 1) / δ
  have hC : 0 < C := div_pos (by positivity) hδ
  have hCn : (n : ℝ) ≤ C * δ := by
    dsimp [C]
    rw [div_mul_cancel₀ _ hδ.ne']
    linarith
  obtain ⟨R₀, ε₀, hR₀, hε₀, hcross⟩ :=
    l6a_cross_normalized_direct hL1e hDGZ hAdapter P h hh hp hC
  let s : ℝ := max ((n : ℝ) + 2) (2 / ε₀)
  have hs : (n : ℝ) + 1 < s := by
    have hh := le_max_left ((n : ℝ) + 2) (2 / ε₀)
    dsimp [s]
    linarith
  have hs0 : 0 < s := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hεmax : 1 < ε₀ * s := by
    have h := le_max_right ((n : ℝ) + 2) (2 / ε₀)
    have h2 : 2 ≤ ε₀ * s := by
      calc
        (2 : ℝ) = ε₀ * (2 / ε₀) := by field_simp [hε₀.ne']
        _ ≤ ε₀ * s := mul_le_mul_of_nonneg_left h hε₀.le
    linarith
  let R : ℝ := R₀ * s
  have hR : (n : ℝ) < R := by
    have h1 : s < R₀ * s := (lt_mul_iff_one_lt_left hs0).2 hR₀
    dsimp [R]
    linarith
  refine ⟨R, hR, ?_⟩
  intro ε hε
  have hεcross : ε ∈ Ioo (0 : ℝ) (ε₀ * s) :=
    ⟨hε.1, hε.2.trans hεmax⟩
  let B : Ω → C(Rd d × Rd d, ℝ) := fun ω =>
    toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  let S : Set C(Rd d × Rd d, ℝ) :=
    {D | supPairs D (ball (0 : Rd d) s) ≤
      ENNReal.ofReal C⁻¹ * infPairs D (sphere 0 s) (sphere 0 R)}
  have hSm : MeasurableSet S := l6a_measurableSet_cross _ _ _ C⁻¹
  have hBm : AEMeasurable B P :=
    l6a_aemeasurable_raw_metric hDGZ.dim κ hDGZ.kernel ξ hε.1 P h hh
  have hcrossN : ENNReal.ofReal p ≤ P (B ⁻¹' S) := by
    have hprob : P (B ⁻¹' S) =
        P {ω | supPairs (lfppDist κ ξ ε (h ω)) (ball (0 : Rd d) s) ≤
          ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
            (sphere 0 s) (sphere 0 R)} := by
      apply measure_congr
      filter_upwards [l10a_ae_continuous_convMollify hDGZ.dim κ
        hDGZ.kernel P h hh hε.1] with ω hc
      exact propext (l6a_cross_norm_iff_raw_general hDGZ.dim κ
        hDGZ.kernel ξ hε.1 (h ω) hc _ _ _ C⁻¹)
    rw [hprob]
    change ENNReal.ofReal p ≤ P {ω | supPairs (lfppDist κ ξ ε (h ω))
      (ball (0 : Rd d) s) ≤ ENNReal.ofReal C⁻¹ *
        infPairs (lfppDist κ ξ ε (h ω)) (sphere 0 s)
          (sphere 0 (R₀ * s))}
    exact hcross s hs0 0 ε hεcross
  have hcrossBad : P (B ⁻¹' S)ᶜ ≤ ENNReal.ofReal q := by
    rw [prob_compl_eq_one_sub₀ (hBm.nullMeasurable hSm)]
    apply tsub_le_iff_right.mpr
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal q + ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hq.le hp0.le]
        congr 1
        dsimp [p]
        ring
      _ ≤ ENNReal.ofReal q + P (B ⁻¹' S) := add_le_add le_rfl hcrossN
  have hsepBad : P {ω | B ω ∉ metricSepSet_select 0 0 k} ≤
      ENNReal.ofReal q := hsepTail ε hε
  have hae : 0 < aEps κ ξ ε :=
    l6a_aEps_pos hDGZ.dim κ hDGZ.kernel ξ hε.1
  have hsub : ∀ᵐ ω ∂P,
      ¬ (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n)
        (sphere 0 R) (B ω) →
      B ω ∉ metricSepSet_select 0 0 k ∨ ω ∈ (B ⁻¹' S)ᶜ := by
    filter_upwards [l10a_ae_continuous_convMollify hDGZ.dim κ
      hDGZ.kernel P h hh hε.1] with ω hc hbad
    by_cases hsep : B ω ∈ metricSepSet_select 0 0 k
    · by_cases hcr : B ω ∈ S
      · have hfar : (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n)
            (sphere 0 R) (B ω) := by
          change (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n)
            (sphere 0 R) (DGZ.normMetricC ξ (convMollify κ ε (h ω))
              (aEps κ ξ ε))
          apply l6a_cross_sep_implies_far (by have := hDGZ.dim; omega : 0 < d)
            ξ (aEps κ ξ ε) hae (convMollify κ ε (h ω)) hc n k hs hR₀ hC
            (by simpa only [δ] using hCn)
          · exact hsep
          · exact hcr
        exact False.elim (hbad hfar)
      · exact Or.inr hcr
    · exact Or.inl hsep
  have hbad := (measure_mono_ae hsub).trans (measure_union_le
    {ω | B ω ∉ metricSepSet_select 0 0 k} (B ⁻¹' S)ᶜ)
  calc
    P {ω | ¬ (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n)
      (sphere 0 R) (B ω)} ≤
        P {ω | B ω ∉ metricSepSet_select 0 0 k} + P (B ⁻¹' S)ᶜ := hbad
    _ ≤ ENNReal.ofReal q + ENNReal.ofReal q :=
      add_le_add hsepBad hcrossBad
    _ ≤ ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hq.le hq.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)

end HigherDimLQGMetric
