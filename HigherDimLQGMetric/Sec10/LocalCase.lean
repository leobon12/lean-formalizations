import HigherDimLQGMetric.Sec10.LocalFamily

/-! Locally bounded perturbations: tightness over a bounded interval of scales. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Topology Filter Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

local instance : PolishSpace C(Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _
local instance : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

/-- A compact approximation of every law, with all compact sets consisting of genuine
metrics, proves the three clauses of `TightOver`. -/
theorem s8a_tightOver_of_compact_metric_approx
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set ℝ} (B : ℝ → Ω → C(Rd d × Rd d, ℝ))
    (hBm : ∀ r ∈ S, AEMeasurable (B r) P)
    (happrox : ∀ {ε : ℝ≥0∞}, 0 < ε →
      ∃ C : Set C(Rd d × Rd d, ℝ), IsCompact C ∧
        C ⊆ {E | IsContinuousMetric E} ∧
        ∀ r ∈ S, (P.map (B r)) Cᶜ ≤ ε) : TightOver P B S := by
  refine ⟨hBm, ?_, ?_⟩
  · rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨C, hC, _, hbound⟩ := happrox hε
    exact ⟨C, hC, fun ν ⟨r, hr, hν⟩ => hν ▸ hbound r hr⟩
  · intro ν hν
    let T : Set C(Rd d × Rd d, ℝ) := {E | IsContinuousMetric E}
    have hzero : (ν : Measure C(Rd d × Rd d, ℝ)) Tᶜ = 0 := by
      apply le_antisymm _ bot_le
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨C, hC, hCm, hbound⟩ := happrox hε
      obtain ⟨νs, hνs, hlim⟩ := mem_closure_iff_seq_limit.mp hν
      have hseq : ∀ n, (νs n : Measure C(Rd d × Rd d, ℝ)) Cᶜ ≤ ε := by
        intro n
        obtain ⟨r, hr, heq⟩ := hνs n
        rw [heq]
        exact hbound r hr
      have hliminf : (atTop.liminf fun n =>
          (νs n : Measure C(Rd d × Rd d, ℝ)) Cᶜ) ≤ ε := by
        calc (atTop.liminf fun n =>
              (νs n : Measure C(Rd d × Rd d, ℝ)) Cᶜ)
            ≤ atTop.liminf (fun _ : ℕ => ε) :=
              Filter.liminf_le_liminf (Filter.Eventually.of_forall hseq)
          _ = ε := Filter.liminf_const ε
      have hνC : (ν : Measure C(Rd d × Rd d, ℝ)) Cᶜ ≤ ε :=
        (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
          hC.isClosed.isOpen_compl).trans hliminf
      have hTC : Tᶜ ⊆ Cᶜ := compl_subset_compl.mpr hCm
      simpa using (measure_mono hTC).trans hνC
    apply measure_eq_zero_iff_ae_notMem.mp hzero |>.mono
    intro E hE
    simpa only [T, mem_compl_iff, mem_ofPred_eq, not_not] using hE

/-- Sharp-normalizer tightness on every bounded scale interval for an LGF with an arbitrary
continuous perturbation. -/
theorem IsStrongExpMetric.tightOver_cont {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hd : 2 ≤ d) (hξ : 0 < ξ)
    (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) (R : ℝ) (_hR : 0 < R) :
    TightOver P (fun r ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r)
      (Ioo 0 R) := by
  obtain ⟨hmh, f, hf, hg⟩ := hh
  let g : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hgf : ∀ ω, addFun (g ω) (f ω) = h ω := by
    intro ω
    simp only [g, addFun]
    exact sub_add_cancel _ _
  let A : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => (D (s8a_pureRescaled g r ω)).1
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r
  have hAm : ∀ r ∈ Ioo (0 : ℝ) R, Measurable (A r) := by
    intro r hr
    exact (measurable_subtype_coe.comp hD.measurable).comp
      (s8a_pureRescaled_isLGF hg hr.1).measurable
  have hBm : ∀ r ∈ Ioo (0 : ℝ) R, Measurable (B r) := by
    intro r _
    have hs : B r = scaledField ξ D (fun s => s ^ (ξ * Q)) r 0 ∘ h := by
      funext ω
      exact (scaledField_zero ξ D (fun s => s ^ (ξ * Q)) r (h ω)).symm
    rw [hs]
    exact (measurable_scaledField hD.measurable _ r 0).comp hmh
  let μ : Measure C(Rd d × Rd d, ℝ) := P.map (A 1)
  have : IsProbabilityMeasure μ := inferInstance
  have hAlaw : ∀ r ∈ Ioo (0 : ℝ) R, P.map (A r) = μ := by
    intro r hr
    have hDm : Measurable fun u : DistRd d => (D u).1 :=
      measurable_subtype_coe.comp hD.measurable
    change P.map ((fun u : DistRd d => (D u).1) ∘ s8a_pureRescaled g r) =
      P.map ((fun u : DistRd d => (D u).1) ∘ s8a_pureRescaled g 1)
    rw [← Measure.map_map hDm (s8a_pureRescaled_isLGF hg hr.1).measurable,
      ← Measure.map_map hDm (s8a_pureRescaled_isLGF hg one_pos).measurable,
      s8a_map_pureRescaled_eq hd hg hr.1, s8a_map_pureRescaled_eq hd hg one_pos]
  have hμ : ∀ᵐ E ∂μ, IsContinuousMetric E := by
    exact (ae_map_iff (μ := P) (f := A 1)
      ((measurable_subtype_coe.comp hD.measurable).comp
        (s8a_pureRescaled_isLGF hg one_pos).measurable).aemeasurable
      (measurableSet_isContinuousMetric_select d)).2
      (ae_of_all _ fun ω => (D _).2)
  have happrox : ∀ {ε : ℝ≥0∞}, 0 < ε →
      ∃ T : Set C(Rd d × Rd d, ℝ), IsCompact T ∧
        T ⊆ {E | IsContinuousMetric E} ∧
        ∀ r ∈ Ioo (0 : ℝ) R, (P.map (B r)) Tᶜ ≤ ε := by
    intro ε hε
    let ε₀ : ℝ≥0∞ := min (ε / 2) (1 / 2)
    have hε₀ : 0 < ε₀ := lt_min
      (by exact ENNReal.div_pos hε.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (by norm_num)
    obtain ⟨K, hK, hKm, hKmass⟩ := s8a_exists_compact_metrics μ hμ hε₀
    have hKn : K.Nonempty := by
      by_contra hn
      have : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      rw [this, compl_empty, measure_univ] at hKmass
      have hlt : ε₀ ≤ 1 / 2 := min_le_right _ _
      have : (1 / 2 : ℝ≥0∞) < 1 := by norm_num
      exact (not_lt_of_ge (hlt.trans this.le)) hKmass
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
    obtain ⟨T, hT, hTm, hTgood⟩ := s8a_exists_localCompact_of_bounds hK hKn hKm C
    refine ⟨T, hT, hTm, ?_⟩
    intro r hr
    have hbadA : P (A r ⁻¹' Kᶜ) < ε₀ := by
      rw [← Measure.map_apply₀ (hAm r hr).aemeasurable
        hK.isClosed.isOpen_compl.measurableSet.nullMeasurableSet, hAlaw r hr]
      exact hKmass
    have hbadF : P (f ⁻¹' Fᶜ) ≤ ε₀ := by
      rw [← Measure.map_apply₀ hf.aemeasurable
        hF.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
      exact hFmass ν (by simp)
    have hsub : ∀ᵐ ω ∂P, ω ∈ B r ⁻¹' Tᶜ →
        ω ∈ A r ⁻¹' Kᶜ ∪ f ⁻¹' Fᶜ := by
      have hg' := s8a_pureRescaled_isLGF hg hr.1
      filter_upwards [hD.ae_normalizedAtScale_perturb hd hg hf hr.1,
        hD.length P (s8a_pureRescaled g r) hg'.isLGFPlusCont] with ω he hlen hbad
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
        constructor <;> nlinarith
      have hmetric : IsContinuousMetric (B r ω) :=
        s8a_normalizedAtScale_isContinuousMetric ξ D _ (h ω) hr.1
          (s8a_sharpNormalizer_pos r hr.1)
      have he' : ∀ x y, ENNReal.ofReal (B r ω (x, y)) =
          weylScale ξ (s8a_scaledWeight (f ω) r)
            (D (s8a_pureRescaled g r ω)) x y := by
        intro x y
        simpa only [B, g, hgf ω] using he x y
      have hgood : B r ω ∈ T :=
        hTgood (D (s8a_pureRescaled g r ω)) hAK hlen ξ
          (s8a_scaledWeight (f ω) r) hw (B r ω) hmetric he'
      exact hbad hgood
    have hbad : P (B r ⁻¹' Tᶜ) ≤ P (A r ⁻¹' Kᶜ ∪ f ⁻¹' Fᶜ) :=
      measure_mono_ae hsub
    rw [Measure.map_apply₀ (hBm r hr).aemeasurable
      hT.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
    calc P (B r ⁻¹' Tᶜ) ≤ P (A r ⁻¹' Kᶜ ∪ f ⁻¹' Fᶜ) := hbad
      _ ≤ P (A r ⁻¹' Kᶜ) + P (f ⁻¹' Fᶜ) := measure_union_le _ _
      _ ≤ ε₀ + ε₀ := add_le_add hbadA.le hbadF
      _ ≤ ε / 2 + ε / 2 := add_le_add (min_le_left _ _) (min_le_left _ _)
      _ = ε := by
        rw [← two_mul]
        exact ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  exact s8a_tightOver_of_compact_metric_approx P B
    (fun r hr => (hBm r hr).aemeasurable) happrox

end HigherDimLQGMetric
