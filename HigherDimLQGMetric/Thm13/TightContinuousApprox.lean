import HigherDimLQGMetric.Thm13.ScaleWeyl

/-! Continuous scale tightness from compact metric approximations of the pure scale family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Topology Filter Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

local instance (d : ℕ) : PolishSpace C(Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _
local instance (d : ℕ) : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

theorem l8_tight_cont_of_pure_compact
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D : DistRd d → ContMetric d) (hDm : Measurable D)
    (hN : L8NormalizedWeyl ξ D)
    (c : ℝ → ℝ) (hc : ∀ r, 0 < r → 0 < c r)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusCont h P) (R : ℝ) (hR : 0 < R)
    (hK : ∀ {ε : ℝ≥0∞}, 0 < ε →
      ∃ K : Set C(Rd d × Rd d, ℝ), IsCompact K ∧
        K ⊆ {M | IsContinuousMetric M} ∧
        ∀ (h₀ : Ω → DistRd d), IsNormalizedLGF h₀ P →
          ∀ r ∈ Ioo (0 : ℝ) R,
            (P.map (fun ω => normalizedAtScale ξ D c (h₀ ω) r)) Kᶜ ≤ ε) :
    TightOver P (fun r ω => normalizedAtScale ξ D c (h ω) r)
      (Ioo 0 R) := by
  obtain ⟨h₀, f, hh₀, hf, hdec⟩ := l8_lgfPlusCont_decomp hd P h hh
  let A : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ D c (h₀ ω) r
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ D c (h ω) r
  have hAm : ∀ r ∈ Ioo (0 : ℝ) R, Measurable (A r) := by
    intro r _
    have hs : A r = scaledField ξ D c r 0 ∘ h₀ := by
      funext ω
      exact (scaledField_zero ξ D c r (h₀ ω)).symm
    rw [hs]
    exact (measurable_scaledField hDm _ r 0).comp hh₀.1.measurable
  have hBm : ∀ r ∈ Ioo (0 : ℝ) R, Measurable (B r) := by
    intro r _
    have hs : B r = scaledField ξ D c r 0 ∘ h := by
      funext ω
      exact (scaledField_zero ξ D c r (h ω)).symm
    rw [hs]
    exact (measurable_scaledField hDm _ r 0).comp hh.1
  have happrox : ∀ {ε : ℝ≥0∞}, 0 < ε →
      ∃ T : Set C(Rd d × Rd d, ℝ), IsCompact T ∧
        T ⊆ {E | IsContinuousMetric E} ∧
        ∀ r ∈ Ioo (0 : ℝ) R, (P.map (B r)) Tᶜ ≤ ε := by
    intro ε hε
    let ε₀ : ℝ≥0∞ := min (ε / 2) (1 / 2)
    have hε₀ : 0 < ε₀ := lt_min
      (by exact ENNReal.div_pos hε.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (by norm_num)
    obtain ⟨K, hKc, hKm, hKmass⟩ := hK hε₀
    have hKn : K.Nonempty := by
      by_contra hn
      have : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      let r₀ : ℝ := R / 2
      have hr₀ : r₀ ∈ Ioo (0 : ℝ) R := ⟨by dsimp [r₀]; positivity,
        by dsimp [r₀]; linarith⟩
      have hm := hKmass h₀ hh₀ r₀ hr₀
      rw [this, compl_empty, measure_univ] at hm
      have hlt : ε₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
      exact (not_le_of_gt hlt) hm
    let ν : Measure C(Rd d, ℝ) := P.map f
    have : IsProbabilityMeasure ν := inferInstance
    obtain ⟨F, hF, hFmass⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
        (isTightMeasureSet_singleton (μ := ν)) ε₀ hε₀
    let W : ℕ → ℝ := fun n =>
      Classical.choose (s8a_uniform_abs_scaledWeight
        (show 1 ≤ d by omega) hF R n)
    have hW : ∀ n, 0 ≤ W n ∧ ∀ u ∈ F, ∀ r ∈ Icc 0 R,
        ∀ x ∈ closedBall (0 : Rd d) (n + 2),
          |s8a_scaledWeight u r x| ≤ W n := by
      intro n
      exact Classical.choose_spec (s8a_uniform_abs_scaledWeight
        (show 1 ≤ d by omega) hF R n)
    let C : ℕ → ℝ := fun n => ξ * W n
    obtain ⟨T, hT, hTm, hTgood⟩ := s8a_exists_localCompact_of_bounds hKc hKn hKm C
    refine ⟨T, hT, hTm, ?_⟩
    intro r hr
    have hbadA : P (A r ⁻¹' Kᶜ) ≤ ε₀ := by
      rw [← Measure.map_apply₀ (hAm r hr).aemeasurable
        hKc.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
      exact hKmass h₀ hh₀ r hr
    have hbadF : P (f ⁻¹' Fᶜ) ≤ ε₀ := by
      rw [← Measure.map_apply₀ hf.aemeasurable
        hF.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
      exact hFmass ν (by simp)
    have hsub : ∀ᵐ ω ∂P, ω ∈ B r ⁻¹' Tᶜ →
        ω ∈ A r ⁻¹' Kᶜ ∪ f ⁻¹' Fᶜ := by
      filter_upwards [hN P h₀ hh₀,
        hh₀.1.ae_exists_tendsto_sphereAvgSeq hd hr.1 0] with
        ω ⟨hDω, hWω⟩ ⟨a, ha⟩ hbad
      by_contra hnot
      simp only [mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at hnot
      have hAK : A r ω ∈ K := hnot.1
      have hFF : f ω ∈ F := hnot.2
      have hw : ∀ (n : ℕ) z, z ∈ ball (0 : Rd d) (n + 2) →
          -C n ≤ ξ * s8a_scaledWeight (f ω) r z ∧
          ξ * s8a_scaledWeight (f ω) r z ≤ C n := by
        intro n z hz
        have hb := (hW n).2 (f ω) hFF r ⟨hr.1.le, hr.2.le⟩ z
          (ball_subset_closedBall hz)
        have ha := abs_le.mp hb
        dsimp [C]
        constructor <;> nlinarith [mul_nonneg hξ (hW n).1]
      have hmetric : IsContinuousMetric (B r ω) :=
        s8a_normalizedAtScale_isContinuousMetric ξ D c (h ω) hr.1 (hc r hr.1)
      have hs : sphereAvg (addFun (h₀ ω) (f ω)) r 0 =
          sphereAvg (h₀ ω) r 0 + sphereAvg (ofCont (f ω)) r 0 := by
        rw [sphereAvg_addFun_of_tendsto
          (tendsto_sphereAvgSeq_sphereAvg ⟨a, ha⟩)]
        exact congrArg (sphereAvg (h₀ ω) r 0 + ·)
          (sphereAvg_ofCont (f ω) r 0).symm
      let M : ContMetric d :=
        ⟨A r ω, s8a_normalizedAtScale_isContinuousMetric ξ D c (h₀ ω) hr.1 (hc r hr.1)⟩
      have hMl : M.IsLength := by
        let a₀ : ℝ := (c r)⁻¹ * Real.exp (-ξ * sphereAvg (h₀ ω) r 0)
        have ha₀ : 0 < a₀ := mul_pos (inv_pos.mpr (hc r hr.1)) (Real.exp_pos _)
        let M₀ : ContMetric d := ((D (h₀ ω)).affine r hr.1.ne' 0).smul a₀ ha₀
        have heq : M = M₀ := by
          apply Subtype.ext
          ext p
          simp only [M, M₀, A, a₀, ContMetric.smul_apply,
            ContMetric.affine_apply, normalizedAtScale,
            ContinuousMap.smul_apply, ContinuousMap.comp_apply,
            ContinuousMap.coe_mk, smul_eq_mul, add_zero]
        rw [heq]
        exact ContMetric.isLength_smul ha₀
          (ContMetric.isLength_affine hr.1.ne' 0 hDω)
      have he' : ∀ x y, ENNReal.ofReal (B r ω (x, y)) =
          weylScale ξ (s8a_scaledWeight (f ω) r) M x y := by
        intro x y
        simpa only [B, hdec ω] using
          (l8_normalizedAtScale_weyl ξ D c (h₀ ω) (f ω)
            hDω (hWω (f ω)) hr.1 (hc r hr.1) hs x y)
      have hgood : B r ω ∈ T :=
        hTgood M hAK hMl ξ (s8a_scaledWeight (f ω) r) hw
          (B r ω) hmetric he'
      exact hbad hgood
    have hbad : P (B r ⁻¹' Tᶜ) ≤ P (A r ⁻¹' Kᶜ ∪ f ⁻¹' Fᶜ) :=
      measure_mono_ae hsub
    rw [Measure.map_apply₀ (hBm r hr).aemeasurable
      hT.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
    calc P (B r ⁻¹' Tᶜ) ≤ P (A r ⁻¹' Kᶜ ∪ f ⁻¹' Fᶜ) := hbad
      _ ≤ P (A r ⁻¹' Kᶜ) + P (f ⁻¹' Fᶜ) := measure_union_le _ _
      _ ≤ ε₀ + ε₀ := add_le_add hbadA hbadF
      _ ≤ ε / 2 + ε / 2 := add_le_add (min_le_left _ _) (min_le_left _ _)
      _ = ε := by
        rw [← two_mul]
        exact ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  exact s8a_tightOver_of_compact_metric_approx P B
    (fun r hr => (hBm r hr).aemeasurable) happrox

end HigherDimLQGMetric
