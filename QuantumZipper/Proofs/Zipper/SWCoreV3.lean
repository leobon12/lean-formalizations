import QuantumZipper.Proofs.Zipper.SWCoreV1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V (3): energy distance between two displaced unit semicircles (variance modulus)

Task SWC-V (`handoff/SW-CORE.md` §5, item (iii)): the variance modulus of the pushed-semicircle
pairings in the map and the centre. After a common affine rescaling, two pushed semicircles are
`fc(0,1).map T₁`, `fc(0,1).map T₂` with `‖T₁ u − T₂ u‖ ≤ Δ` on the closed unit disc (`Δ` =
sup-distance of the maps plus the centre shift, divided by `r ψ'(t)`). For measurable `T₁, T₂`,
`c`-co-Lipschitz and bounded by `Bf` on the closed unit disc,

  `|kernelCov2 neumannH (μ₀.map T₁, μ₀.map T₂) (…)| ≤ 2 · holderK (12/c + 1) Bf · Δ^{1/6}`
                                                               (`swcv_kernelCov2_two`).

Sheffield–Wang, arXiv:1605.06171, Lemma 3.4 and the variance modulus used before (3.23) (p. 16).
Own assembly of the repository's energy tools (`RegCont.abs_integral_neuPot_sub_le_of_disp`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open TwoPoint

section Two

variable {T₁ T₂ : ℂ → ℂ}

/-- Frostman bound for the image of `fc(0,1)` under a `c`-co-Lipschitz map. -/
theorem swcv_frostman_map_gen {T : ℂ → ℂ} (hTm : Measurable T) {c : ℝ} (hc : 0 < c)
    (hco : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, c * ‖u - v‖ ≤ ‖T u - T v‖) :
    TwoPoint.IsFrostman ((foldedCircle 0 1).map T) (1 / 3) (12 / c + 1) := by
  have : IsProbabilityMeasure ((foldedCircle 0 1).map T) :=
    (Measure.isProbabilityMeasure_map_iff hTm.aemeasurable).2 inferInstance
  refine swcv_frostman_third (by have : 0 < 12 / c := by positivity
                                 linarith) fun p s hs => ?_
  rw [Measure.map_apply hTm measurableSet_closedBall]
  have hnull : foldedCircle 0 1 (closedBall (0 : ℂ) 1)ᶜ = 0 := by
    have h := ae_iff.1 (swcv_ae_norm_fc01.mono fun u (hu : ‖u‖ = 1) =>
      (show u ∈ closedBall (0 : ℂ) 1 by rw [mem_closedBall, dist_zero_right, hu]))
    exact h
  by_cases hex : ∃ u₀ ∈ closedBall (0 : ℂ) 1, T u₀ ∈ closedBall p s
  · obtain ⟨u₀, hu₀, hTu₀⟩ := hex
    have hsub : T ⁻¹' closedBall p s ⊆ closedBall u₀ (2 * s / c) ∪ (closedBall (0 : ℂ) 1)ᶜ := by
      intro u hu
      by_cases hu1 : u ∈ closedBall (0 : ℂ) 1
      · left
        rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hc]
        have h1 := hco u hu1 u₀ hu₀
        have h2 : ‖T u - T u₀‖ ≤ 2 * s := by
          have a1 : ‖T u - p‖ ≤ s := by rw [← dist_eq_norm]; exact hu
          have a2 : ‖T u₀ - p‖ ≤ s := by rw [← dist_eq_norm]; exact hTu₀
          calc ‖T u - T u₀‖ = ‖(T u - p) - (T u₀ - p)‖ := by ring_nf
            _ ≤ ‖T u - p‖ + ‖T u₀ - p‖ := norm_sub_le _ _
            _ ≤ 2 * s := by linarith
        linarith
      · right; exact hu1
    calc foldedCircle 0 1 (T ⁻¹' closedBall p s)
        ≤ foldedCircle 0 1 (closedBall u₀ (2 * s / c)) +
            foldedCircle 0 1 (closedBall (0 : ℂ) 1)ᶜ :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (6 * (2 * s / c) / 1) + 0 := by
          rw [hnull]
          exact add_le_add (RegCont.foldedCircle_closedBall_le_arc 0 u₀ one_pos
            (by positivity)) le_rfl
      _ ≤ ENNReal.ofReal ((12 / c + 1) * s) := by
          rw [add_zero]
          refine ENNReal.ofReal_le_ofReal ?_
          have : 6 * (2 * s / c) / 1 = 12 / c * s := by field_simp; ring
          rw [this]; nlinarith
  · push_neg at hex
    have hsub : T ⁻¹' closedBall p s ⊆ (closedBall (0 : ℂ) 1)ᶜ := fun u hu hu1 => hex u hu1 hu
    rw [measure_mono_null hsub hnull]
    exact bot_le

/-- One bracket for two maps. -/
theorem swcv_bracket2_le (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) {Δ Bf CF : ℝ}
    (hΔ : 0 ≤ Δ) (hBf : 0 ≤ Bf) (hCF : 0 ≤ CF)
    (hdisp : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T₁ u - T₂ u‖ ≤ Δ)
    (hb₁ : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T₁ u‖ ≤ Bf)
    (hb₂ : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T₂ u‖ ≤ Bf)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ Bf) (hmκ : κ.real univ = 1) :
    |∫ x, neuPot κ x ∂((foldedCircle 0 1).map T₁) -
        ∫ x, neuPot κ x ∂((foldedCircle 0 1).map T₂)| ≤
      holderK CF Bf * Δ ^ ((1 / 3 : ℝ) / 2) := by
  have hπ := Real.pi_pos
  set G : ℝ → ℂ := fun θ => foldH (circleMap 0 1 θ) with hG
  have hGm : Measurable G := measurable_foldH.comp (continuous_circleMap 0 1).measurable
  have hG1 : ∀ θ, G θ ∈ closedBall (0 : ℂ) 1 := fun θ => by
    simp only [hG, mem_closedBall, dist_zero_right, norm_foldH, norm_circleMap_zero,
      abs_one, le_refl]
  set F₁ : ℝ → ℂ := fun θ => T₁ (G θ) with hF₁
  set F₂ : ℝ → ℂ := fun θ => T₂ (G θ) with hF₂
  have hF₁m : Measurable F₁ := hT₁.comp hGm
  have hF₂m : Measurable F₂ := hT₂.comp hGm
  have hNm := measurable_neuPot κ
  rw [integral_map hT₁.aemeasurable hNm.aestronglyMeasurable,
    integral_map hT₂.aemeasurable hNm.aestronglyMeasurable,
    integral_foldedCircle_eq (g := fun x => neuPot κ (T₁ x)) (hNm.comp hT₁) 0 1,
    integral_foldedCircle_eq (g := fun x => neuPot κ (T₂ x)) (hNm.comp hT₂) 0 1]
  have hPb : ∀ x : ℂ, ‖x‖ ≤ Bf → |neuPot κ x| ≤ potMax CF Bf := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf hBκ hx
    rwa [hmκ] at this
  have hIoc : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hi : ∀ F : ℝ → ℂ, Measurable F → (∀ θ, ‖F θ‖ ≤ Bf) →
      Integrable (fun θ => neuPot κ (F θ)) (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    fun F hF hFb => Integrable.of_bound (hNm.comp hF).aestronglyMeasurable (potMax CF Bf)
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hFb θ))
  have hF₁b : ∀ θ, ‖F₁ θ‖ ≤ Bf := fun θ => hb₁ _ (hG1 θ)
  have hF₂b : ∀ θ, ‖F₂ θ‖ ≤ Bf := fun θ => hb₂ _ (hG1 θ)
  have key := RegCont.abs_integral_neuPot_sub_le_of_disp hF₁m hF₂m (Bf := Bf) (CF := CF)
    (Δ := Δ) (β := 0) hCF hBf hF₁b hF₂b (Bad := ∅) MeasurableSet.empty
    (by simp) (fun θ _ => hdisp _ (hG1 θ)) hΔ κ hFκ hBκ hmκ
  rw [← mul_sub, ← integral_sub (hi F₁ hF₁m hF₁b) (hi F₂ hF₂m hF₂b), abs_mul,
    abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 * π))]
  rw [zero_mul, add_zero] at key
  calc (2 * π)⁻¹ * |∫ θ in Ico 0 (2 * π), (neuPot κ (F₁ θ) - neuPot κ (F₂ θ))|
      ≤ (2 * π)⁻¹ * (2 * π * (holderK CF Bf * Δ ^ ((1 / 3 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = holderK CF Bf * Δ ^ ((1 / 3 : ℝ) / 2) := by field_simp

/-- **Energy distance between two displaced unit semicircles** (variance modulus). -/
theorem swcv_kernelCov2_two (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) {Δ Bf c : ℝ}
    (hΔ : 0 ≤ Δ) (hBf : 0 ≤ Bf) (hc : 0 < c)
    (hdisp : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T₁ u - T₂ u‖ ≤ Δ)
    (hb₁ : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T₁ u‖ ≤ Bf)
    (hb₂ : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T₂ u‖ ≤ Bf)
    (hco₁ : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, c * ‖u - v‖ ≤ ‖T₁ u - T₁ v‖)
    (hco₂ : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, c * ‖u - v‖ ≤ ‖T₂ u - T₂ v‖) :
    |kernelCov2 neumannH ((foldedCircle 0 1).map T₁, (foldedCircle 0 1).map T₂)
        ((foldedCircle 0 1).map T₁, (foldedCircle 0 1).map T₂)| ≤
      2 * (holderK (12 / c + 1) Bf * Δ ^ ((1 / 3 : ℝ) / 2)) := by
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have : IsProbabilityMeasure (μ₀.map T₁) :=
    (Measure.isProbabilityMeasure_map_iff hT₁.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (μ₀.map T₂) :=
    (Measure.isProbabilityMeasure_map_iff hT₂.aemeasurable).2 inferInstance
  have hCF : 0 ≤ 12 / c + 1 := by positivity
  have hB : ∀ {T : ℂ → ℂ}, Measurable T → (∀ u ∈ closedBall (0 : ℂ) 1, ‖T u‖ ≤ Bf) →
      ∀ᵐ y ∂(μ₀.map T), ‖y‖ ≤ Bf := fun {T} hT hb => by
    rw [ae_map_iff hT.aemeasurable (measurableSet_le continuous_norm.measurable
      measurable_const)]
    filter_upwards [swcv_ae_norm_fc01] with u hu
    exact hb u (by rw [mem_closedBall, dist_zero_right, hu])
  have h1 := swcv_bracket2_le hT₁ hT₂ hΔ hBf hCF hdisp hb₁ hb₂ (μ₀.map T₁)
    (swcv_frostman_map_gen hT₁ hc hco₁) (hB hT₁ hb₁) (by simp)
  have h2 := swcv_bracket2_le hT₁ hT₂ hΔ hBf hCF hdisp hb₁ hb₂ (μ₀.map T₂)
    (swcv_frostman_map_gen hT₂ hc hco₂) (hB hT₂ hb₂) (by simp)
  have e : kernelCov2 neumannH (μ₀.map T₁, μ₀.map T₂) (μ₀.map T₁, μ₀.map T₂) =
      (∫ x, neuPot (μ₀.map T₁) x ∂(μ₀.map T₁) - ∫ x, neuPot (μ₀.map T₁) x ∂(μ₀.map T₂)) -
        (∫ x, neuPot (μ₀.map T₂) x ∂(μ₀.map T₁) - ∫ x, neuPot (μ₀.map T₂) x ∂(μ₀.map T₂)) := by
    unfold kernelCov2 kernelCov neuPot
    ring
  rw [e]
  calc |_ - _| ≤ |∫ x, neuPot (μ₀.map T₁) x ∂(μ₀.map T₁) - ∫ x, neuPot (μ₀.map T₁) x ∂(μ₀.map T₂)| +
        |∫ x, neuPot (μ₀.map T₂) x ∂(μ₀.map T₁) - ∫ x, neuPot (μ₀.map T₂) x ∂(μ₀.map T₂)| :=
          abs_sub _ _
    _ ≤ _ := by linarith

end Two

end SWCore
end QuantumZipper
