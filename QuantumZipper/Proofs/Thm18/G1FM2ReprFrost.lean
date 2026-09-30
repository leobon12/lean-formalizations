import QuantumZipper.Proofs.Thm18.G1FMAdm
import QuantumZipper.Proofs.Thm18.G1PathCoordFam
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1FM2-REPR (1): uniform Frostman bounds for measures pushed by `S ψ`

For `ψ` with `G1RC.PsiGood ψ` and a disc `B̄(w, ρ)` with `ρ < Im w`, every finite measure `μ` of
mass `≤ M`, `α`-Frostman with constant `C₀` and concentrated on `B̄(w, ρ)` is pushed by
`z ↦ S ψ(z)` to a measure supported in a fixed `ballH R` and `α`-Frostman with a constant `C₁`
depending only on `(ψ, w, ρ, S, α, C₀, M)` (`G1FM2.pushFrost_unif`).

This is the argument of `G1FM.isAdmissibleH_pushFm` (G1FMAdm.lean) made uniform in `μ`: Koebe
distortion bounds `‖ψ'‖` below on the disc, and the Koebe `1/4`-covering theorem plus
injectivity puts the disc part of the preimage of a small ball `B̄(y, t)` into a ball of radius
proportional to `t` (Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 1.3 and Cor. 1.4,
as cited there). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

open G1RC CircleFubini CA.Koebe

/-- **Uniform Frostman bound for pushed measures.** -/
theorem pushFrost_unif {ψ : ℂ → ℂ} (hψ : PsiGood ψ) {w : ℂ} {ρ S α C₀ M : ℝ} (hρ : 0 ≤ ρ)
    (hρw : ρ < w.im) (hS : 0 < S) (hα : 0 < α) (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) :
    ∃ R C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (μ : Measure ℂ) [IsFiniteMeasure μ], (μ univ).toReal ≤ M →
      TwoPoint.IsFrostman μ α C₀ → (∀ᵐ x ∂μ, dist x w ≤ ρ) →
      (μ.map fun z => (S : ℂ) * ψ z) (ballH R)ᶜ = 0 ∧
        TwoPoint.IsFrostman (μ.map fun z => (S : ℂ) * ψ z) α C₁ := by
  obtain ⟨hψm, hd, hinj, hmaps, hbdd⟩ := hψ
  set f : ℂ → ℂ := fun z => (S : ℂ) * ψ z with hf
  have hfm : Measurable f := measurable_const.mul hψm
  set m := w.im - ρ with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hDH : ∀ z, dist z w ≤ ρ → m ≤ z.im ∧ ‖z‖ ≤ ‖w‖ + ρ := by
    intro z hz
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← dist_eq_norm] at h1
    refine ⟨by linarith [neg_abs_le (z.im - w.im)], ?_⟩
    have := norm_le_norm_add_norm_sub' z w
    rw [← dist_eq_norm] at this
    linarith
  obtain ⟨a, ha, hlow⟩ := deriv_lower_of_injOn hd hinj (R1 := ‖w‖ + ρ + 1) (by positivity)
  set a' := a * m ^ koebeDistExp with ha'
  have ha'0 : 0 < a' := mul_pos ha (Real.rpow_pos_of_pos hm0 _)
  have hκ := koebeCovConst_pos
  have hder : ∀ z, dist z w ≤ ρ → a' ≤ ‖deriv ψ z‖ := by
    intro z hz
    obtain ⟨h1, h2⟩ := hDH z hz
    have hzH : z ∈ H := show 0 < z.im by linarith
    refine le_trans ?_ (hlow z hzH (by linarith))
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hm0.le h1 koebeDistExp_pos.le) ha.le
  set t₀ := S * koebeCovConst * a' * m / 4 with ht₀
  have ht₀0 : 0 < t₀ := by positivity
  set C₁ := M / t₀ ^ α + C₀ * (4 / (S * koebeCovConst * a')) ^ α with hC₁
  obtain ⟨Mψ, hMψ⟩ := hbdd (‖w‖ + ρ)
  refine ⟨S * Mψ, C₁, by positivity, fun μ _ hMμ hF hae => ⟨?_, ?_⟩⟩
  · show (μ.map f) (closedBall 0 (S * Mψ) ∩ Hbar)ᶜ = 0
    rw [Measure.map_apply hfm
      (isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet).compl]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
    simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq] at hx ⊢
    intro hxd
    obtain ⟨h1, h2⟩ := hDH x hxd
    have hxH : x ∈ H := show 0 < x.im by linarith
    refine hx ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, hf]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (hMψ x hxH h2) hS.le
    · have := hmaps hxH
      show (0 : ℝ) ≤ ((S : ℂ) * ψ x).im
      rw [Complex.im_ofReal_mul]
      exact (mul_pos hS this).le
  · intro y t ht
    rw [Measure.map_apply hfm isClosed_closedBall.measurableSet]
    have hA0 : 0 ≤ M / t₀ ^ α * t ^ α := by positivity
    have hB0 : 0 ≤ C₀ * (4 / (S * koebeCovConst * a')) ^ α * t ^ α := by positivity
    rw [hC₁, add_mul]
    rcases le_or_gt t₀ t with htt | htt
    · have h1 : (μ (f ⁻¹' closedBall y t)).toReal ≤ M :=
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))).trans hMμ
      have h2 : M ≤ M / t₀ ^ α * t ^ α := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht₀0.le htt hα.le) hM
      linarith
    · set E := f ⁻¹' closedBall y t ∩ {z | dist z w ≤ ρ} with hE
      have hEq : μ (f ⁻¹' closedBall y t) ≤ μ E := by
        refine (measure_le_inter_add_sdiff μ _ {z | dist z w ≤ ρ}).trans ?_
        have h0 : μ (f ⁻¹' closedBall y t \ {z | dist z w ≤ ρ}) = 0 :=
          measure_mono_null (fun x hx => hx.2) (ae_iff.1 hae)
        rw [h0, add_zero]
      rcases E.eq_empty_or_nonempty with hne | ⟨z0, hz0⟩
      · have : μ (f ⁻¹' closedBall y t) = 0 :=
          le_antisymm (hEq.trans (by rw [hne, measure_empty])) bot_le
        rw [this, ENNReal.toReal_zero]
        linarith
      set ρ' := 4 * t / (S * koebeCovConst * a') with hρ'
      have hρ'0 : 0 < ρ' := by positivity
      obtain ⟨hz0m, -⟩ := hDH z0 hz0.2
      have hρ'm : ρ' < m := by
        rw [hρ', div_lt_iff₀ (by positivity)]
        rw [ht₀] at htt
        linarith
      have hball : ball z0 ρ' ⊆ H :=
        (ball_subset_ball (by linarith)).trans (ball_im_subset_H' z0)
      have hsub : E ⊆ closedBall z0 ρ' := by
        rintro z ⟨hzy, hzD⟩
        obtain ⟨hzm, -⟩ := hDH z hzD
        have hzH : z ∈ H := show 0 < z.im by linarith
        have h1 : ‖f z - f z0‖ ≤ 2 * t := by
          have a1 := mem_closedBall.1 (show f z ∈ closedBall y t from hzy)
          have a2 := mem_closedBall.1 (show f z0 ∈ closedBall y t from hz0.1)
          rw [← dist_eq_norm]
          linarith [dist_triangle_right (f z) (f z0) y]
        have e1 : ‖f z - f z0‖ = S * ‖ψ z - ψ z0‖ := by
          rw [hf]
          simp only
          rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
        have hd0 := hder z0 hz0.2
        have h2 : ‖ψ z - ψ z0‖ < koebeCovConst * ρ' * ‖deriv ψ z0‖ := by
          have h3 : koebeCovConst * ρ' * a' = 4 * t / S := by
            rw [hρ']; field_simp
          have h4 : koebeCovConst * ρ' * a' ≤ koebeCovConst * ρ' * ‖deriv ψ z0‖ :=
            mul_le_mul_of_nonneg_left hd0 (by positivity)
          have h5 : ‖ψ z - ψ z0‖ ≤ 2 * t / S := by
            rw [le_div_iff₀ hS]; linarith
          have h6 : 2 * t / S < 4 * t / S := by
            apply div_lt_div_of_pos_right _ hS; linarith
          linarith
        have hmem : ψ z ∈ ball (ψ z0) (koebeCovConst * ρ' * ‖deriv ψ z0‖) := by
          rw [mem_ball, dist_eq_norm]; exact h2
        obtain ⟨z'', hz'', heq⟩ := ball_subset_image_koebe (hd.mono hball) (hinj.mono hball) hmem
        rw [← hinj (hball hz'') hzH heq]
        exact ball_subset_closedBall hz''
      have h1 : (μ (f ⁻¹' closedBall y t)).toReal ≤ C₀ * ρ' ^ α :=
        (ENNReal.toReal_mono (measure_ne_top _ _) (hEq.trans (measure_mono hsub))).trans
          (hF z0 ρ' hρ'0)
      have e2 : C₀ * ρ' ^ α = C₀ * (4 / (S * koebeCovConst * a')) ^ α * t ^ α := by
        rw [hρ', show 4 * t / (S * koebeCovConst * a') = 4 / (S * koebeCovConst * a') * t by
          ring, Real.mul_rpow (by positivity) ht.le]
        ring
      linarith

end G1FM2
end Thm18Asm
end QuantumZipper
