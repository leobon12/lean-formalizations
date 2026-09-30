import QuantumZipper.Proofs.Zipper.SWCoreDefs
import QuantumZipper.Proofs.Zipper.RegContEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V (1): energy distance of a displaced unit semicircle

Task SWC-V (`handoff/SW-CORE.md` §5). Sheffield–Wang, arXiv:1605.06171, Lemma 3.4 (3.17)–(3.19),
p. 15: after rescaling, the pushed semicircle `fc(t,r).map ψ` is the unit semicircle moved by a map
`T` with `‖T u − u‖ ≤ C r` and bi-Lipschitz constants close to `1`; SW use this to compare the
pushed and round regularizations (their (3.20)).

Here, at unit scale: for a measurable `T` that is `½`-co-Lipschitz and bounded by `2` on the
closed unit disc and moves every point of it by at most `Δ`,

  `|kernelCov2 neumannH (μ₀.map T, μ₀) (μ₀.map T, μ₀)| ≤ 2 · holderK 24 2 · Δ^{1/6}`,
  `μ₀ = fc(0,1)`                                                   (`swcv_kernelCov2_unit`),

i.e. the Neumann energy (the variance of `X(μ₀.map T) − X(μ₀)` for the free field) is Hölder
small in the displacement. Proof: the energy is a difference of two brackets
`∫ neuPot κ d(μ₀.map T) − ∫ neuPot κ dμ₀` (`κ = μ₀.map T`, `κ = μ₀`), each controlled by the
Hölder modulus of the Neumann potential of a `1/3`-Frostman measure
(`RegCont.abs_integral_neuPot_sub_le_of_disp`); the Frostman bounds come from the arc bound for
folded circles and the co-Lipschitz property. The exponent `1/6` (instead of SW's linear bound)
is harmless for the chaining/Borel–Cantelli step (geometric in `k`). Own assembly of the
repository's energy tools.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open TwoPoint

/-- The unit folded circle lives on the unit sphere. -/
theorem swcv_ae_norm_fc01 : ∀ᵐ u ∂foldedCircle 0 1, ‖u‖ = 1 := by
  have hs : MeasurableSet {u : ℂ | ‖u‖ = 1} :=
    measurableSet_eq_fun continuous_norm.measurable measurable_const
  rw [foldedCircle, ae_map_iff measurable_foldH.aemeasurable hs]
  filter_upwards [K3.ae_mem_sphere_circleUnif_k3 (0 : ℂ) one_pos] with w hw
  show ‖foldH w‖ = 1
  rw [norm_foldH]
  simpa using hw

/-- Linear ball bounds give a `1/3`-Frostman bound for probability measures. -/
theorem swcv_frostman_third {ν : Measure ℂ} [IsProbabilityMeasure ν] {C : ℝ} (hC : 1 ≤ C)
    (h : ∀ p : ℂ, ∀ s : ℝ, 0 < s → ν (closedBall p s) ≤ ENNReal.ofReal (C * s)) :
    TwoPoint.IsFrostman ν (1 / 3) C := by
  intro p s hs
  rcases le_total s 1 with hs1 | hs1
  · have h1 : s ≤ s ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (h p s hs)).trans ?_
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  · have h1 : 1 ≤ s ^ (1 / 3 : ℝ) := Real.one_le_rpow hs1 (by norm_num)
    calc (ν (closedBall p s)).toReal ≤ 1 := by
          rw [← measureReal_def]; exact measureReal_le_one
      _ ≤ C * s ^ (1 / 3 : ℝ) := by nlinarith

theorem swcv_frostman_fc01 : TwoPoint.IsFrostman (foldedCircle 0 1) (1 / 3) 24 := by
  refine swcv_frostman_third (by norm_num) fun p s hs => ?_
  refine (RegCont.foldedCircle_closedBall_le_arc 0 p one_pos hs.le).trans ?_
  exact ENNReal.ofReal_le_ofReal (by linarith)

section Unit

variable {T : ℂ → ℂ}

theorem swcv_frostman_map (hTm : Measurable T)
    (hco : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, ‖u - v‖ / 2 ≤ ‖T u - T v‖) :
    TwoPoint.IsFrostman ((foldedCircle 0 1).map T) (1 / 3) 24 := by
  have : IsProbabilityMeasure ((foldedCircle 0 1).map T) := (Measure.isProbabilityMeasure_map_iff hTm.aemeasurable).2 inferInstance
  refine swcv_frostman_third (by norm_num) fun p s hs => ?_
  rw [Measure.map_apply hTm measurableSet_closedBall]
  have hnull : foldedCircle 0 1 (closedBall (0 : ℂ) 1)ᶜ = 0 := by
    have h := ae_iff.1 (swcv_ae_norm_fc01.mono fun u (hu : ‖u‖ = 1) =>
      (show u ∈ closedBall (0 : ℂ) 1 by rw [mem_closedBall, dist_zero_right, hu]))
    exact h
  by_cases hex : ∃ u₀ ∈ closedBall (0 : ℂ) 1, T u₀ ∈ closedBall p s
  · obtain ⟨u₀, hu₀, hTu₀⟩ := hex
    have hsub : T ⁻¹' closedBall p s ⊆ closedBall u₀ (4 * s) ∪ (closedBall (0 : ℂ) 1)ᶜ := by
      intro u hu
      by_cases hu1 : u ∈ closedBall (0 : ℂ) 1
      · left
        rw [mem_closedBall, dist_eq_norm]
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
        ≤ foldedCircle 0 1 (closedBall u₀ (4 * s)) + foldedCircle 0 1 (closedBall (0 : ℂ) 1)ᶜ :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (6 * (4 * s) / 1) + 0 := by
          rw [hnull]
          exact add_le_add (RegCont.foldedCircle_closedBall_le_arc 0 u₀ one_pos (by linarith))
            le_rfl
      _ = ENNReal.ofReal (24 * s) := by rw [add_zero]; congr 1; ring
  · push_neg at hex
    have hsub : T ⁻¹' closedBall p s ⊆ (closedBall (0 : ℂ) 1)ᶜ := fun u hu hu1 => hex u hu1 hu
    rw [measure_mono_null hsub hnull]
    exact bot_le

/-- One bracket `∫ neuPot κ d(μ₀.map T) − ∫ neuPot κ dμ₀`. -/
theorem swcv_bracket_le (hTm : Measurable T) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdisp : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T u - u‖ ≤ Δ)
    (hb : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T u‖ ≤ 2)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ (1 / 3) 24)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ 2) (hmκ : κ.real univ = 1) :
    |∫ x, neuPot κ x ∂((foldedCircle 0 1).map T) - ∫ x, neuPot κ x ∂foldedCircle 0 1| ≤
      holderK 24 2 * Δ ^ ((1 / 3 : ℝ) / 2) := by
  have hπ := Real.pi_pos
  set F' : ℝ → ℂ := fun θ => foldH (circleMap 0 1 θ) with hF'
  set F : ℝ → ℂ := fun θ => T (F' θ) with hF
  have hF'm : Measurable F' := measurable_foldH.comp (continuous_circleMap 0 1).measurable
  have hFm : Measurable F := hTm.comp hF'm
  have hF'1 : ∀ θ, F' θ ∈ closedBall (0 : ℂ) 1 := fun θ => by
    simp only [hF', mem_closedBall, dist_zero_right, norm_foldH, norm_circleMap_zero,
      abs_one, le_refl]
  have hNm := measurable_neuPot κ
  rw [integral_map hTm.aemeasurable hNm.aestronglyMeasurable,
    integral_foldedCircle_eq (g := fun x => neuPot κ (T x)) (hNm.comp hTm) 0 1, integral_foldedCircle_eq hNm 0 1]
  have hPb : ∀ x : ℂ, ‖x‖ ≤ 2 → |neuPot κ x| ≤ potMax 24 2 := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) (by norm_num) (by norm_num) hBκ hx
    rwa [hmκ] at this
  have hIoc : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hi : ∀ G : ℝ → ℂ, Measurable G → (∀ θ, ‖G θ‖ ≤ 2) →
      Integrable (fun θ => neuPot κ (G θ)) (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    fun G hG hGb => Integrable.of_bound (hNm.comp hG).aestronglyMeasurable (potMax 24 2)
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hGb θ))
  have hFb : ∀ θ, ‖F θ‖ ≤ 2 := fun θ => hb _ (hF'1 θ)
  have hF'b : ∀ θ, ‖F' θ‖ ≤ 2 := fun θ => by
    have := hF'1 θ
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have key := RegCont.abs_integral_neuPot_sub_le_of_disp hFm hF'm (Bf := 2) (CF := 24)
    (Δ := Δ) (β := 0) (by norm_num) (by norm_num) hFb hF'b (Bad := ∅) MeasurableSet.empty
    (by simp) (fun θ _ => hdisp _ (hF'1 θ)) hΔ κ hFκ hBκ hmκ
  rw [← mul_sub, ← integral_sub (hi F hFm hFb) (hi F' hF'm hF'b), abs_mul,
    abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 * π))]
  rw [zero_mul, add_zero] at key
  calc (2 * π)⁻¹ * |∫ θ in Ico 0 (2 * π), (neuPot κ (F θ) - neuPot κ (F' θ))|
      ≤ (2 * π)⁻¹ * (2 * π * (holderK 24 2 * Δ ^ ((1 / 3 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = holderK 24 2 * Δ ^ ((1 / 3 : ℝ) / 2) := by field_simp

/-- **Energy distance of a displaced unit semicircle** (SW Lemma 3.4, energy form). -/
theorem swcv_kernelCov2_unit (hTm : Measurable T) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdisp : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T u - u‖ ≤ Δ)
    (hco : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, ‖u - v‖ / 2 ≤ ‖T u - T v‖)
    (hb : ∀ u ∈ closedBall (0 : ℂ) 1, ‖T u‖ ≤ 2) :
    |kernelCov2 neumannH ((foldedCircle 0 1).map T, foldedCircle 0 1)
        ((foldedCircle 0 1).map T, foldedCircle 0 1)| ≤
      2 * (holderK 24 2 * Δ ^ ((1 / 3 : ℝ) / 2)) := by
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have : IsProbabilityMeasure (μ₀.map T) := (Measure.isProbabilityMeasure_map_iff hTm.aemeasurable).2 inferInstance
  have hB0 : ∀ᵐ y ∂μ₀, ‖y‖ ≤ 2 := swcv_ae_norm_fc01.mono fun u hu => by rw [hu]; norm_num
  have hB1 : ∀ᵐ y ∂(μ₀.map T), ‖y‖ ≤ 2 := by
    rw [ae_map_iff hTm.aemeasurable (measurableSet_le continuous_norm.measurable
      measurable_const)]
    filter_upwards [swcv_ae_norm_fc01] with u hu
    exact hb u (by rw [mem_closedBall, dist_zero_right, hu])
  have h1 := swcv_bracket_le hTm hΔ hdisp hb (μ₀.map T) (swcv_frostman_map hTm hco) hB1
    (by simp)
  have h0 := swcv_bracket_le hTm hΔ hdisp hb μ₀ swcv_frostman_fc01 hB0 (by simp)
  have e : kernelCov2 neumannH (μ₀.map T, μ₀) (μ₀.map T, μ₀) =
      (∫ x, neuPot (μ₀.map T) x ∂(μ₀.map T) - ∫ x, neuPot (μ₀.map T) x ∂μ₀) -
        (∫ x, neuPot μ₀ x ∂(μ₀.map T) - ∫ x, neuPot μ₀ x ∂μ₀) := by
    unfold kernelCov2 kernelCov neuPot
    ring
  rw [e]
  calc |_ - _| ≤ |∫ x, neuPot (μ₀.map T) x ∂(μ₀.map T) - ∫ x, neuPot (μ₀.map T) x ∂μ₀| +
        |∫ x, neuPot μ₀ x ∂(μ₀.map T) - ∫ x, neuPot μ₀ x ∂μ₀| := abs_sub _ _
    _ ≤ _ := by linarith

end Unit

end SWCore
end QuantumZipper
