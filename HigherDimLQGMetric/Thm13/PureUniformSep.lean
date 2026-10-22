import HigherDimLQGMetric.Thm13.PureLocalSep
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Continuity

/-! Uniform local separation follows from compactness of the scale law family
and genuine-metric support of every law in its closure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Topology Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

local instance (d : ℕ) : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

theorem l8_tightFamily_localSep_tail
    {d : ℕ} (hd : 2 ≤ d) {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hT : TightFamily P X S) (n m : ℕ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ k : ℕ, ∀ i ∈ S,
      (P.map (X i)) (l8_localSepOpen n m k)ᶜ ≤ η := by
  classical
  let Law : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ν | ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)}
  have hKL : IsCompact (closure Law) := by
    apply isCompact_closure_of_isTightMeasureSet
    apply hT.2.1.subset
    rintro ν ⟨μ, ⟨i, hi, hμ⟩, rfl⟩
    exact ⟨i, hi, hμ⟩
  let O : ℕ → Set C(Rd d × Rd d, ℝ) := fun k => l8_localSepOpen n m k
  have hO : ∀ k, IsOpen (O k) := fun k => l8_localSepOpen_isOpen n m k
  have hOm : Monotone O := l8_localSepOpen_mono n m
  have hsmall : ∀ ν ∈ closure Law,
      ∃ k : ℕ, (ν : Measure C(Rd d × Rd d, ℝ)) (O k)ᶜ < η := by
    intro ν hν
    have hgood : ∀ᵐ E ∂(ν : Measure C(Rd d × Rd d, ℝ)),
        ∃ k, E ∈ O k :=
      (hT.2.2 ν hν).mono fun E hE =>
        l8_metric_mem_localSepOpen (by omega : 0 < d) E hE.1 n m
    have hanti : Antitone (fun k => (O k)ᶜ) := by
      intro k l hkl
      exact compl_subset_compl.mpr (hOm hkl)
    have hinter : (ν : Measure C(Rd d × Rd d, ℝ))
        (⋂ k, (O k)ᶜ) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hgood] with E ⟨k, hk⟩ hE
      exact (mem_iInter.mp hE k) hk
    have hlim : Tendsto (fun k => (ν : Measure C(Rd d × Rd d, ℝ))
        (O k)ᶜ) atTop (𝓝 0) := by
      have ht := tendsto_measure_iInter_atTop
        (μ := (ν : Measure C(Rd d × Rd d, ℝ)))
        (fun k => (hO k).isClosed_compl.measurableSet.nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      simpa only [Function.comp_def, hinter] using ht
    exact (hlim.eventually (gt_mem_nhds hη)).exists
  have hUniform : ∃ k : ℕ, ∀ ν ∈ closure Law,
      (ν : Measure C(Rd d × Rd d, ℝ)) (O k)ᶜ ≤ η := by
    by_contra hNo
    simp only [not_exists, not_forall, not_le] at hNo
    choose ν hν hbad using hNo
    obtain ⟨μ, hμ, φ, hφ, hconv⟩ :=
      hKL.tendsto_subseq (x := ν) hν
    obtain ⟨k, hk⟩ := hsmall μ hμ
    have hport : (atTop.limsup fun j =>
        ((ν (φ j) : ProbabilityMeasure C(Rd d × Rd d, ℝ)) :
          Measure C(Rd d × Rd d, ℝ)) (O k)ᶜ) ≤
        (μ : Measure C(Rd d × Rd d, ℝ)) (O k)ᶜ :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
        (hO k).isClosed_compl
    have hev : ∀ᶠ j : ℕ in atTop,
        ((ν (φ j) : ProbabilityMeasure C(Rd d × Rd d, ℝ)) :
          Measure C(Rd d × Rd d, ℝ)) (O k)ᶜ < η :=
      eventually_lt_of_limsup_lt (hport.trans_lt hk)
    have hφk : ∀ᶠ j : ℕ in atTop, k ≤ φ j :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop k)
    obtain ⟨j, hj, hkj⟩ := (hev.and hφk).exists
    have hsub : (O (φ j))ᶜ ⊆ (O k)ᶜ :=
      compl_subset_compl.mpr (hOm hkj)
    have hbad' := hbad (φ j)
    exact (not_lt_of_ge ((measure_mono hsub).trans hj.le)) hbad'
  obtain ⟨k, hk⟩ := hUniform
  refine ⟨k, fun i hi => ?_⟩
  let ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    ⟨P.map (X i), (Measure.isProbabilityMeasure_map_iff (hT.1 i hi)).mpr inferInstance⟩
  exact hk ν (subset_closure ⟨i, hi, rfl⟩)

end HigherDimLQGMetric
