import HigherDimLQGMetric.Markov.ProjId
import HigherDimLQGMetric.LGF.StochFubini

/-! Generic stochastic Fubini for real L² processes on Euclidean space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

section SFub

variable {Y : Rd d → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x)) (hYL2 : ∀ x, MemLp (Y x) 2 P)
  (hv : ∀ R : ℝ, ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ∫ ω, Y x ω ^ 2 ∂P ≤ C)

-- Joint measurability follows from continuity of each path and measurability at each point.
include hYc hYm in
theorem markov_measurable_Y₂ : Measurable fun p : Ω × Rd d => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

include hYc hYm hYL2 hv in
/-- The swap `E[(∫ ψ Y) Z] = ∫ ψ(x) E[Y(x) Z] dx` for `Z ∈ L²(P)`. -/
theorem markov_integral_integral_mul_Y_mul {ψ : Rd d → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, ψ x * Y x ω) * Z ω ∂P = ∫ x, ψ x * ∫ ω, Y x ω * Z ω ∂P := by
  obtain ⟨Mψ, L, hψ⟩ := exists_isBddSupp_of_continuous hψc hψs
  obtain ⟨Ck, hCk⟩ := hv L
  set H : Ω × Rd d → ℝ := fun p => ψ p.2 * Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod volume) :=
    (((hψc.measurable.comp measurable_snd).mul
      (markov_measurable_Y₂ hYc hYm)).aestronglyMeasurable).mul hZ.1.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x
    have h1 := (hYL2 x).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((hYL2 x).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = _ := by rw [integral_div, integral_add h1 hZ2]
  have hY2 : ∀ x : Rd d, ‖x‖ ≤ L → ∫ ω, Y x ω ^ 2 ∂P ≤ Ck := fun x hx => by
    exact hCk x hx
  have hHi : Integrable H (P.prod volume) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hH, mul_assoc]
      exact ((hYL2 x).integrable_mul hZ).const_mul _
    · refine Integrable.mono' (hψ.integrable.norm.mul_const ((Ck + ∫ ω, Z ω ^ 2 ∂P) / 2))
        hHm.norm.prod_swap.integral_prod_right' (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖H (ω, x)‖ ∂P = ‖ψ x‖ * ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P := by
        simp only [hH, norm_mul]
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      by_cases hx : L < ‖x‖
      · rw [hψ.eq_zero x hx]
        simp
      · push Not at hx
        refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (norm_nonneg _)
        gcongr
        exact hY2 x hx
  have e1 : ∀ ω, (∫ x, ψ x * Y x ω) * Z ω = ∫ x, H (ω, x) := fun ω => by
    rw [← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun ω x => H (ω, x)) hHi]
  congr 1
  funext x
  simp only [hH]
  rw [← integral_const_mul]
  congr 1
  funext ω
  ring

include hYc hYm hYL2 hv in
/-- `ω ↦ ∫ ψ(x) Y(x, ω) dx` is in `L²(P)`. -/
theorem markov_memLp_integral_mul_Y {ψ : Rd d → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    MemLp (fun ω => ∫ x, ψ x * Y x ω) 2 P := by
  obtain ⟨Mψ, L, hψ⟩ := exists_isBddSupp_of_continuous hψc hψs
  obtain ⟨Ck, hCk⟩ := hv L
  have hjm := markov_measurable_Y₂ hYc hYm
  have hAm : Measurable fun ω => ∫ x, ψ x * Y x ω :=
    (((hψc.measurable.comp measurable_snd).mul hjm).stronglyMeasurable.integral_prod_right'
      (ν := volume)).measurable
  set Q : Ω × Rd d → ℝ := fun p => |ψ p.2| * Y p.2 p.1 ^ 2 with hQ
  have hQm : Measurable Q :=
    (continuous_abs.measurable.comp (hψc.measurable.comp measurable_snd)).mul (hjm.pow_const 2)
  have hQi : Integrable Q (P.prod volume) := by
    rw [integrable_prod_iff' hQm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hQ]
      exact (hYL2 x).integrable_sq.const_mul _
    · refine Integrable.mono' (hψ.integrable.norm.mul_const Ck)
        hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖Q (ω, x)‖ ∂P = ‖ψ x‖ * ∫ ω, Y x ω ^ 2 ∂P := by
        simp only [hQ, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, sq_abs]
        rw [integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      by_cases hx : L < ‖x‖
      · rw [hψ.eq_zero x hx]
        simp
      · push Not at hx
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact hCk x hx
  have hQ1 := hQi.integral_prod_left
  rw [memLp_two_iff_integrable_sq hAm.aestronglyMeasurable]
  refine (hQ1.const_mul (∫ x, |ψ x|)).mono' (hAm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hc : Continuous fun x => Y x ω := hYc ω
  have hint1 : Integrable fun x => ψ x * Y x ω :=
    (hψc.mul hc).integrable_of_hasCompactSupport hψs.mul_right
  have hint2 : Integrable fun x => |ψ x| * Y x ω ^ 2 := by
    have : Integrable (fun x => ψ x * Y x ω ^ 2) :=
      (hψc.mul ((continuous_pow 2).comp hc)).integrable_of_hasCompactSupport hψs.mul_right
    refine this.abs.congr (Eventually.of_forall fun x => ?_)
    simp only [abs_mul, abs_pow, sq_abs]
  exact LQGMetric.GFFExist.sq_integral_mul_le (μ := volume) (a := fun x => ψ x)
    (b := fun x => Y x ω)
    hψ.integrable hint1 hint2

end SFub

end HigherDimLQGMetric
