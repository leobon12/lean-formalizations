import QuantumZipper.Proofs.Thm18.G1ProfileConv
import QuantumZipper.Proofs.Thm18.G1FrostAlphaKoebe
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarAdm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE (4): pushed first-mode measures are admissible

For `ψ` with the properties `G1RC.PsiGood` (holomorphic and injective on `ℍ`, `ψ(ℍ) ⊆ ℍ`,
bounded on bounded sets), `S > 0` and a first-mode measure `fmMeas w v s` whose support
`B̄(w, ‖v‖ + s)` lies in `ℍ`, the pushed measure `(fmMeas w v s).map (S ψ)` is admissible
(`G1FM.isAdmissibleH_pushFm`).

Route: `fmMeas w v s` is `1/3`-Frostman (`D3Plus.isFrostman_fmArc`, `RegContEnergy`'s
`isFrostman_bindFc`); on the disc `D = B̄(w, ‖v‖ + s)` the map `ψ` has `‖ψ'‖ ≥ a' > 0` (Koebe
distortion, `G1RC.deriv_lower_of_injOn`), and by the Koebe `1/4`-covering theorem
(`CA.Koebe.ball_subset_image_koebe`) plus injectivity, the `D`-part of the preimage of a small
ball `B̄(y, t)` lies in a ball of radius `4t/(S κ a')`; so the pushed measure is `1/3`-Frostman
and `FrostmanReg.isAdmissibleH_of_frostman` concludes. Own elementary argument on top of the
cited repository lemmas (the Koebe theorems: Pommerenke, *Boundary Behaviour of Conformal Maps*,
Thm 1.3 and Cor. 1.4, as cited there).
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM

open G1RC CircleFubini CA.Koebe

/-- The arc measure lies on the circle `∂B(w, ‖v‖)`. -/
theorem ae_dist_fmArc_le (w v : ℂ) : ∀ᵐ y ∂D3Plus.fmArc w v, dist y w ≤ ‖v‖ := by
  unfold D3Plus.fmArc
  refine (ae_map_iff (D3Plus.measurable_fmArcMap w v).aemeasurable
    (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).2
    (ae_of_all _ fun φ => ?_)
  show dist (w + v * Complex.exp ((φ : ℂ) * Complex.I)) w ≤ ‖v‖
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The first-mode measure lies in `B̄(w, ‖v‖ + s)` (when that disc lies in `Hbar`). -/
theorem ae_dist_fmMeas_le {w v : ℂ} {s : ℝ} (hs : 0 ≤ s) (hvw : ‖v‖ ≤ w.im) :
    ∀ᵐ x ∂D3Plus.fmMeas w v s, dist x w ≤ ‖v‖ + s := by
  unfold D3Plus.fmMeas
  have := isFiniteMeasure_bind_circle (r := s) (D3Plus.fmArc w v)
  rw [ae_iff, bind_circle_apply (D3Plus.fmArc w v) (A := {a : ℂ | ¬dist a w ≤ ‖v‖ + s})
    (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const).compl]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_dist_fmArc_le w v] with y hy
  have hyH : y ∈ Hbar := by
    have h1 : |(y - w).im| ≤ ‖y - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← dist_eq_norm] at h1
    show (0 : ℝ) ≤ y.im
    linarith [neg_abs_le (y.im - w.im)]
  have := foldedCircle_ae_dist_le' hyH hs
  rw [ae_iff] at this
  refine measure_mono_null (fun x hx => ?_) this
  simp only [mem_ofPred_eq, not_le] at hx ⊢
  linarith [dist_triangle x y w]

/-- **Pushed first-mode measures are admissible.** -/
theorem isAdmissibleH_pushFm {ψ : ℂ → ℂ} (hψ : PsiGood ψ) {w v : ℂ} {s S : ℝ} (hs : 0 ≤ s)
    (hv : 0 < ‖v‖) (hvw : ‖v‖ + s < w.im) (hS : 0 < S) :
    IsAdmissibleH ((D3Plus.fmMeas w v s).map fun z => (S : ℂ) * ψ z) := by
  obtain ⟨hψm, hd, hinj, hmaps, hbdd⟩ := hψ
  set μ := D3Plus.fmMeas w v s with hμ
  set f : ℂ → ℂ := fun z => (S : ℂ) * ψ z with hf
  have hfm : Measurable f := measurable_const.mul hψm
  have : IsFiniteMeasure μ := isFiniteMeasure_bind_circle (r := s) (D3Plus.fmArc w v)
  set ρ := ‖v‖ + s with hρ
  set m := w.im - ρ with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  -- points of the disc
  have hDH : ∀ z, dist z w ≤ ρ → m ≤ z.im ∧ ‖z‖ ≤ ‖w‖ + ρ := by
    intro z hz
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← dist_eq_norm] at h1
    refine ⟨by linarith [neg_abs_le (z.im - w.im)], ?_⟩
    have := norm_le_norm_add_norm_sub' z w
    rw [← dist_eq_norm] at this
    linarith
  have hae := ae_dist_fmMeas_le (w := w) (v := v) hs (by linarith)
  -- Frostman bound of `μ`
  obtain ⟨C₀, hF⟩ : ∃ C₀, TwoPoint.IsFrostman μ (1 / 3) C₀ :=
    ⟨_, RegCont.isFrostman_bindFc (D3Plus.isFrostman_fmArc w v hv) hs⟩
  have hC₀ : 0 ≤ C₀ := by
    have := hF w 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    exact ENNReal.toReal_nonneg.trans this
  -- lower bound of `‖ψ'‖` on the disc
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
  set Mμ := (μ univ).toReal with hMμ
  have hMμ0 : 0 ≤ Mμ := ENNReal.toReal_nonneg
  set C₁ := Mμ / t₀ ^ (1 / 3 : ℝ) +
    C₀ * (4 / (S * koebeCovConst * a')) ^ (1 / 3 : ℝ) with hC₁
  have hFp : TwoPoint.IsFrostman (μ.map f) (1 / 3) C₁ := by
    intro y t ht
    rw [Measure.map_apply hfm isClosed_closedBall.measurableSet]
    have hA0 : 0 ≤ Mμ / t₀ ^ (1 / 3 : ℝ) * t ^ (1 / 3 : ℝ) := by positivity
    have hB0 : 0 ≤ C₀ * (4 / (S * koebeCovConst * a')) ^ (1 / 3 : ℝ) * t ^ (1 / 3 : ℝ) := by
      positivity
    rw [hC₁, add_mul]
    rcases le_or_gt t₀ t with htt | htt
    · -- large balls: total mass
      have h1 : (μ (f ⁻¹' closedBall y t)).toReal ≤ Mμ :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
      have h2 : Mμ ≤ Mμ / t₀ ^ (1 / 3 : ℝ) * t ^ (1 / 3 : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht₀0.le htt (by norm_num)) hMμ0
      linarith
    · -- small balls: Koebe covering
      set E := f ⁻¹' closedBall y t ∩ {z | dist z w ≤ ρ} with hE
      have hEq : μ (f ⁻¹' closedBall y t) ≤ μ E := by
        refine (measure_le_inter_add_sdiff μ _ {z | dist z w ≤ ρ}).trans ?_
        have h0 : μ (f ⁻¹' closedBall y t \ {z | dist z w ≤ ρ}) = 0 :=
          measure_mono_null (fun x hx => hx.2) (ae_iff.1 hae)
        rw [h0, add_zero]
      rcases E.eq_empty_or_nonempty with hne | ⟨z0, hz0⟩
      · have : μ (f ⁻¹' closedBall y t) = 0 := le_antisymm (hEq.trans (by rw [hne, measure_empty])) bot_le
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
      have h1 : (μ (f ⁻¹' closedBall y t)).toReal ≤ C₀ * ρ' ^ (1 / 3 : ℝ) :=
        (ENNReal.toReal_mono (measure_ne_top _ _) (hEq.trans (measure_mono hsub))).trans
          (hF z0 ρ' hρ'0)
      have e2 : C₀ * ρ' ^ (1 / 3 : ℝ) =
          C₀ * (4 / (S * koebeCovConst * a')) ^ (1 / 3 : ℝ) * t ^ (1 / 3 : ℝ) := by
        rw [hρ', show 4 * t / (S * koebeCovConst * a') = 4 / (S * koebeCovConst * a') * t by
          ring, Real.mul_rpow (by positivity) ht.le]
        ring
      linarith
  obtain ⟨Mψ, hMψ⟩ := hbdd (‖w‖ + ρ)
  have hsupp : (μ.map f) (closedBall 0 (S * Mψ) ∩ Hbar)ᶜ = 0 := by
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
  exact FrostmanReg.isAdmissibleH_of_frostman hsupp hFp (by norm_num)

end G1FM
end Thm18Asm
end QuantumZipper
