import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Trunc.LFPP
import HigherDimLQGMetric.Locality.MovingLaw

/-! The full–truncated mollifier error as a measurable compact-open random function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A continuous version of the mollifier error, with a zero fallback only
at distribution inputs for which the full convolution is discontinuous. -/
def l7a_truncErrorC {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (hε : 0 < ε) (g : DistRd d) : C(Rd d, ℝ) := by
  classical
  by_cases hc : Continuous (convMollify κ ε g)
  · exact ⟨fun z => convMollify κ ε g z - truncMollify κ ε g z,
      hc.sub (l2c_continuous_truncMollify hd hκ hε g)⟩
  · exact 0

theorem l7a_truncErrorC_eq_of_continuous {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (hε : 0 < ε) (g : DistRd d)
    (hc : Continuous (convMollify κ ε g)) (z : Rd d) :
    l7a_truncErrorC hd κ hκ ε hε g z =
      convMollify κ ε g z - truncMollify κ ε g z := by
  simp [l7a_truncErrorC, hc]

/-- At every positive scale, the continuous error map is almost surely
measurable under a normalized LGF. -/
theorem l7a_aemeasurable_truncErrorC {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    AEMeasurable (fun ω => l7a_truncErrorC hd κ hκ ε hε (h ω)) P := by
  have hc : ∀ᵐ ω ∂P, Continuous (convMollify κ ε (h ω)) :=
    l10a_ae_continuous_convMollify hd κ hκ P h hh hε
  let Y : Rd d → Ω → ℝ := fun z ω => l7a_truncErrorC hd κ hκ ε hε (h ω) z
  have hYc (ω : Ω) : Continuous fun z => Y z ω :=
    (l7a_truncErrorC hd κ hκ ε hε (h ω)).continuous
  have hYm (z : Rd d) : AEMeasurable (Y z) P := by
    have hm : Measurable (fun ω =>
        convMollify κ ε (h ω) z - truncMollify κ ε (h ω) z) :=
      ((l10a_measurable_convMollify_apply κ ε z).comp hh.1.measurable).sub
        ((measurable_distOn_apply (truncTest κ ε z)).comp hh.1.measurable)
    have heq : Y z =ᵐ[P] (fun ω =>
        convMollify κ ε (h ω) z - truncMollify κ ε (h ω) z) :=
      hc.mono (fun ω hω => l7a_truncErrorC_eq_of_continuous hd κ hκ ε hε
        (h ω) hω z)
    exact (aemeasurable_congr heq.symm).1 hm.aemeasurable
  exact l10a_aemeasurable_toContMap Y hYm hYc

/-- The same measurability argument only needs an almost-sure continuous full
convolution; normalization is a way to supply that hypothesis. -/
theorem l7a_aemeasurable_truncErrorC_of_continuous {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistRd d) (hg : Measurable g)
    (hc : ∀ᵐ ω ∂P, Continuous (convMollify κ ε (g ω))) :
    AEMeasurable (fun ω => l7a_truncErrorC hd κ hκ ε hε (g ω)) P := by
  let Y : Rd d → Ω → ℝ := fun z ω => l7a_truncErrorC hd κ hκ ε hε (g ω) z
  have hYc (ω : Ω) : Continuous fun z => Y z ω :=
    (l7a_truncErrorC hd κ hκ ε hε (g ω)).continuous
  have hYm (z : Rd d) : AEMeasurable (Y z) P := by
    have hm : Measurable (fun ω =>
        convMollify κ ε (g ω) z - truncMollify κ ε (g ω) z) :=
      ((l10a_measurable_convMollify_apply κ ε z).comp hg).sub
        ((measurable_distOn_apply (truncTest κ ε z)).comp hg)
    have heq : Y z =ᵐ[P] (fun ω =>
        convMollify κ ε (g ω) z - truncMollify κ ε (g ω) z) :=
      hc.mono (fun ω hω => l7a_truncErrorC_eq_of_continuous hd κ hκ ε hε
        (g ω) hω z)
    exact (aemeasurable_congr heq.symm).1 hm.aemeasurable
  exact l10a_aemeasurable_toContMap Y hYm hYc

/-- The truncated error tends to zero in the compact-open topology along
every positive scale sequence, on one event independent of the sequence. -/
theorem l7a_ae_truncErrorC_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hL2c : L2c_trunc) (εs : ℕ → ℝ)
    (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => l7a_truncErrorC hd κ hκ (εs n) (hεs n) (h ω))
      atTop (𝓝 (0 : C(Rd d, ℝ))) := by
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (convMollify κ (εs n) (h ω)) :=
    ae_all_iff.mpr fun n =>
      l10a_ae_continuous_convMollify hd κ hκ P h hh (hεs n)
  have htrunc := hL2c d hd κ hκ P h hh
  have hεWithin : Tendsto εs atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεt, Filter.Eventually.of_forall hεs⟩
  filter_upwards [hc, htrunc] with ω hcω htω
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : Rd d)
  let R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR' : K ⊆ closedBall (0 : Rd d) R' :=
    hKR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hraw : TendstoUniformlyOn
      (fun n z => convMollify κ (εs n) (h ω) z -
        truncMollify κ (εs n) (h ω) z) 0 atTop
      (closedBall (0 : Rd d) R') := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have ht := Metric.tendstoUniformlyOn_iff.mp (htω R' hR') η hη
    filter_upwards [hεWithin.eventually ht] with n hn z hz
    exact hn z hz
  have hE : TendstoUniformlyOn
      (fun n z => l7a_truncErrorC hd κ hκ (εs n) (hεs n) (h ω) z)
      0 atTop (closedBall (0 : Rd d) R') := by
    rw [Metric.tendstoUniformlyOn_iff] at hraw ⊢
    intro η hη
    filter_upwards [hraw η hη] with n hn z hz
    simpa only [l7a_truncErrorC_eq_of_continuous hd κ hκ (εs n)
      (hεs n) (h ω) (hcω n) z] using hn z hz
  exact hE.mono hKR'

end HigherDimLQGMetric
