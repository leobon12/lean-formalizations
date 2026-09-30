import QuantumZipper.Proofs.Thm11.AddendumMartPath

/-!
# Theorem 1.1 addendum, AD-4: L²-bounded a.e. convergence implies L¹ convergence

A standard Vitali-type fact (cf. mathlib `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`, where
uniform integrability comes from the L² bound), used for the frozen one-point fields, whose
second moments are bounded uniformly (AD-3 energy identity `Thm11Add.integral_frozenField_sq`
with the bounded FD-8 function `g`).  Own elementary proof (truncation at level `K` plus Fatou,
`lintegral_liminf_le'`), stated with lower Lebesgue integrals to avoid integrability side
conditions.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace Thm11Asm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem enorm_le_ofReal_sq_add_one (x : ℝ) : ‖x‖ₑ ≤ ENNReal.ofReal (x ^ 2) + 1 := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) zero_le_one]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg x, sq_abs x])

theorem lintegral_enorm_le_sq_add_one [IsProbabilityMeasure P] (h : Ω → ℝ) :
    ∫⁻ ω, ‖h ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (h ω ^ 2) ∂P + 1 := by
  calc ∫⁻ ω, ‖h ω‖ₑ ∂P ≤ ∫⁻ ω, (ENNReal.ofReal (h ω ^ 2) + 1) ∂P :=
        lintegral_mono fun ω => enorm_le_ofReal_sq_add_one _
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- Fatou for squares. -/
theorem lintegral_sq_lim_le {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) P)
    (hsq : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂P ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P ≤ C := by
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (g ω ^ 2) =
      liminf (fun n => ENNReal.ofReal (f n ω ^ 2)) atTop := by
    filter_upwards [hlim] with ω h
    exact (((ENNReal.continuous_ofReal.tendsto _).comp (h.pow 2))).liminf_eq.symm
  calc ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω ^ 2)) atTop ∂P := lintegral_congr_ae hae
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂P) atTop :=
        lintegral_liminf_le' fun n => ((hf n).pow_const 2).ennreal_ofReal
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hsq)

theorem abs_le_min_add_sq_div {x K : ℝ} (hK : 0 < K) : |x| ≤ min |x| K + x ^ 2 / K := by
  rcases le_or_gt |x| K with h | h
  · rw [min_eq_left h]; have : 0 ≤ x ^ 2 / K := by positivity
    linarith
  · rw [min_eq_right h.le]
    have : |x| ≤ x ^ 2 / K := by
      rw [le_div_iff₀ hK, ← sq_abs]; nlinarith [abs_nonneg x]
    linarith

/-- **L²-bounded + a.e. convergence ⇒ L¹ convergence** on a probability space. -/
theorem tendsto_lintegral_enorm_sub_of_sq_le [IsProbabilityMeasure P]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : AEMeasurable g P)
    (hsq : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂P ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ∂P) atTop (𝓝 0) := by
  have hg2 := lintegral_sq_lim_le hf hsq hlim
  -- second moment of the difference
  have hdiff : ∀ n, ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂P ≤ 4 * C := fun n => by
    calc ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂P
        ≤ ∫⁻ ω, (2 * ENNReal.ofReal (f n ω ^ 2) + 2 * ENNReal.ofReal (g ω ^ 2)) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f n ω + g ω)])
      _ = 2 * ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂P + 2 * ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P := by
          rw [lintegral_add_left' ((((hf n).pow_const 2).ennreal_ofReal).const_mul 2),
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * C + 2 * C := by gcongr; exact hsq n
      _ = 4 * C := by ring
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  rcases eq_or_ne ε ⊤ with hεt | hεt
  · exact Eventually.of_forall fun _ => hεt ▸ le_top
  set e := ε.toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hε.ne' hεt
  set c := C.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set K : ℝ := 8 * (c + 1) / e with hK
  have hK0 : 0 < K := by positivity
  -- truncated part → 0 by dominated convergence
  have hDCT : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (min |f n ω - g ω| K) ∂P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := P)
      (F := fun n ω => ENNReal.ofReal (min |f n ω - g ω| K)) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal K)
      (fun n => ((continuous_abs.measurable.comp_aemeasurable ((hf n).sub hg)).min aemeasurable_const).ennreal_ofReal)
      (fun n => Eventually.of_forall fun ω => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      (by simp) ?_
    · simpa using h
    filter_upwards [hlim] with ω h
    have h1 : Tendsto (fun n => min |f n ω - g ω| K) atTop (𝓝 (min |g ω - g ω| K)) :=
      (((h.sub tendsto_const_nhds).abs).min tendsto_const_nhds)
    rw [sub_self, abs_zero, min_eq_left hK0.le] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hDCT) (ENNReal.ofReal (e / 2))
    (by simp [he0])] with n hn
  calc ∫⁻ ω, ‖f n ω - g ω‖ₑ ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (min |f n ω - g ω| K) +
          ENNReal.ofReal (1 / K) * ENNReal.ofReal ((f n ω - g ω) ^ 2)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := abs_le_min_add_sq_div (x := f n ω - g ω) hK0
        rw [one_div_mul_eq_div]; exact this
    _ = ∫⁻ ω, ENNReal.ofReal (min |f n ω - g ω| K) ∂P +
          ENNReal.ofReal (1 / K) * ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂P := by
        have hm : AEMeasurable (fun ω => ENNReal.ofReal (min |f n ω - g ω| K)) P :=
          ((continuous_abs.measurable.comp_aemeasurable ((hf n).sub hg)).min
            aemeasurable_const).ennreal_ofReal
        rw [lintegral_add_left' hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (1 / K) * (4 * C) := by
        gcongr; exact hdiff n
    _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) := by
        gcongr
        rw [← ENNReal.ofReal_toReal hC, ← hc, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK, one_div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
    _ = ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, he,
          ENNReal.ofReal_toReal hεt]

end Thm11Asm
end QuantumZipper
