import HigherDimLQGMetric.Limits.ScaleCompact
import HigherDimLQGMetric.Limits.LengthLFPP
import HigherDimLQGMetric.LfppTight.MedianPos

/-!
# Uniform lower median bound for LFPP limit laws

Prokhorov compactness and the strict positivity of point distances give one
positive lower bound for every law in the compact closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- The normalized LFPP unit distance has at least half its mass below one. -/
theorem l6c_half_scaled_lfpp_unit {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) (ha : 0 < aEps κ ξ ε) :
    (2 : ℝ≥0∞)⁻¹ ≤ P {ω | (toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) (0, e₁ d) ≤ 1} := by
  let a := aEps κ ξ ε
  let raw : Ω → ℝ := fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)
  have hm : AEMeasurable raw P :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ P h hh hε
  have hmed := l6a_aEps_eq_sample_lowerMedian hd κ hκ ξ hε P h hh
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | raw ω ≤ a} := by
    apply (l6c_half_le_measure_iff_lowerMedian_le hm).mpr
    exact (by rw [←hmed] : lowerMedian P raw ≤ a)
  have hc := l10a_ae_continuous_convMollify hd κ hκ P h hh hε
  have heq : {ω | (toCMapRd (a⁻¹ • lfppDist κ ξ ε (h ω))) (0, e₁ d) ≤ 1}
      =ᵐ[P] {ω | raw ω ≤ a} := by
    filter_upwards [hc] with ω hcont
    have hlfpp : Continuous (lfppDist κ ξ ε (h ω)) := by
      have hf : lfppDist κ ξ ε (h ω) = fieldLfpp ξ (convMollify κ ε (h ω)) := by
        funext p
        exact (fieldLfpp_eq_lfppDistOn hcont p).symm
      rw [hf]
      exact continuous_fieldLfpp hcont
    have hscaled : Continuous (a⁻¹ • lfppDist κ ξ ε (h ω)) := hlfpp.const_smul _
    apply propext
    rw [toCMapRd_apply_of_continuous hscaled]
    simp only [Pi.smul_apply, smul_eq_mul]
    simpa only [mul_one] using
      (inv_mul_le_iff₀ ha : a⁻¹ * raw ω ≤ 1 ↔ raw ω ≤ a * 1)
  exact hhalf.trans_eq (measure_congr heq).symm

/-- The lower median of the normalized unit point distance is uniformly
positive over the closure of all small-cutoff LFPP laws. -/
theorem l6c_uniform_lfppMedian_pos
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    let S : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
      {ν | ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ μ ∈ closure S,
      m₀ ≤ lowerMedian (μ : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d)) := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  intro S
  have hA := (hL6a d ξ κ) hB2 P h hh.1.isLGFPlusBddCont
  have hK : IsCompact (closure S) := by
    let _ := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
    apply isCompact_closure_of_isTightMeasureSet
    refine hA.2.2.1.subset ?_
    rintro μ ⟨ν, hν, rfl⟩
    exact hν
  apply l6c_uniform_lowerMedian_pos (closure S) hK
    (fun D : C(Rd d × Rd d, ℝ) => D (0, e₁ d)) (continuous_eval_const _)
  intro μ hμ
  filter_upwards [hA.2.2.2 μ hμ] with D hD
  let M : ContMetric d := ⟨D, hD.1⟩
  have hd : 0 < d := by
    obtain ⟨Q, hQ, _⟩ := hB2
    exact lt_of_lt_of_le (by norm_num : 0 < 2) hQ.dim
  exact M.apply_pos (HigherDimLFPP.e₁_ne_zero hd).symm

/-- The lower median of the unit distance is at most one in every law in the
closure, by the closed-set half-mass condition. -/
theorem l6c_lfppMedian_le_one
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hμ : μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}) :
    lowerMedian (μ : Measure C(Rd d × Rd d, ℝ))
      (fun D => D (0, e₁ d)) ≤ 1 := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  have hA := (hL6a d ξ κ) hB2 P h hh.1.isLGFPlusBddCont
  obtain ⟨Q, hQ, _⟩ := hB2
  apply l6c_lowerMedian_le_of_closure
    {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}
    (fun D => D (0, e₁ d)) (continuous_eval_const _) 1 ?_ μ hμ
  intro ν hν
  obtain ⟨ε, hε, hν⟩ := hν
  apply (l6c_half_le_measure_iff_lowerMedian_le
    (P := (ν : Measure C(Rd d × Rd d, ℝ)))
    (continuous_eval_const _).measurable.aemeasurable).mp
  rw [hν]
  change (2 : ℝ≥0∞)⁻¹ ≤
    (P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))))
      ((fun D : C(Rd d × Rd d, ℝ) => D (0, e₁ d)) ⁻¹' Iic 1)
  rw [Measure.map_apply_of_aemeasurable (hA.2.1 ε hε)
    (isClosed_Iic.preimage (continuous_eval_const _)).measurableSet]
  exact l6c_half_scaled_lfpp_unit hQ.dim κ hQ.kernel ξ P h hh hε.1 (hA.1 ε hε)

end HigherDimLQGMetric
