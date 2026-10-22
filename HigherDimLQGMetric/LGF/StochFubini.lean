import HigherDimLQGMetric.LGF.Density
import HigherDimLFPP.Field.WhiteNoise
import LQGMetric.Field.ExistKernel

/-!
# A generic stochastic Fubini step for white-noise fields on `ℝ^d` (packet F2, target 1, part 5)

Let `W` be a white noise on `L²(ℝ × ℝ^d)`, `v : ℝ^d → L²` a family with `‖v x‖` locally bounded, and
`Y` a version of `x ↦ W(v x)` that is continuous in `x` for every `ω` and measurable in `ω`. For a
continuous compactly supported weight `ψ` put `A(ω) = ∫ ψ(x) Y(x, ω) dx`. Then

* `memLp_integral_mul_Y`: `A ∈ L²(P)`;
* `integral_integral_mul_Y_mul`: `E[A Z] = ∫ ψ(x) E[Y(x) Z] dx` for `Z ∈ L²(P)`;
* `integral_Y_mul_W`: `E[Y(x) W(g)] = ⟪v x, g⟫`.

(Fubini on `Ω × ℝ^d`, with the bound `E|Y(x) Z| ≤ (E Y(x)² + E Z²)/2`.) Port of LQGMetric's
`Field/ExistSFub2.lean` (`integral_A_mul`, `memLp_A`) from `ℂ` and `∂_re∂_im φ` to `ℝ^d` and a
general weight `ψ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : HigherDimLFPP.WN d → Ω → ℝ}

/-- `E[W(f) W(g)] = ⟪f, g⟫`. -/
theorem wn_integral_mul (hW : HigherDimLFPP.IsWhiteNoise P W) (f g : HigherDimLFPP.WN d) :
    ∫ ω, W f ω * W g ω ∂P = ⟪f, g⟫ := by
  have := hW.isProbabilityMeasure
  have hf := hW.memLp f 2 (by norm_num)
  have hg := hW.memLp g 2 (by norm_num)
  have h := covariance_eq_sub hf hg
  rw [hW.cov_eq, hW.integral_eq_zero f, zero_mul, sub_zero] at h
  rw [h]
  rfl

section SFub

variable (hW : HigherDimLFPP.IsWhiteNoise P W) {v : Rd d → HigherDimLFPP.WN d}
  {Y : Rd d → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
  (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (v x))
  (hv : ∀ R : ℝ, ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ‖v x‖ ^ 2 ≤ C)
include hW hYW

theorem memLp_Y (x : Rd d) : MemLp (Y x) 2 P := (hW.memLp _ 2 (by norm_num)).ae_eq (hYW x).symm

omit hW in
theorem integral_Y_mul (x : Rd d) {Z : Ω → ℝ} :
    ∫ ω, Y x ω * Z ω ∂P = ∫ ω, W (v x) ω * Z ω ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h]

theorem integral_Y_mul_W (x : Rd d) (g : HigherDimLFPP.WN d) :
    ∫ ω, Y x ω * W g ω ∂P = ⟪v x, g⟫ := by
  rw [integral_Y_mul hYW x, wn_integral_mul hW]

theorem integral_sq_Y (x : Rd d) : ∫ ω, Y x ω ^ 2 ∂P = ‖v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h, sq]

omit hW hYW in
include hYc hYm in
theorem measurable_Y₂ : Measurable fun p : Ω × Rd d => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

include hYc hYm hv in
/-- The swap `E[(∫ ψ Y) Z] = ∫ ψ(x) E[Y(x) Z] dx` for `Z ∈ L²(P)`. -/
theorem integral_integral_mul_Y_mul {ψ : Rd d → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, ψ x * Y x ω) * Z ω ∂P = ∫ x, ψ x * ∫ ω, Y x ω * Z ω ∂P := by
  have := hW.isProbabilityMeasure
  obtain ⟨Mψ, L, hψ⟩ := exists_isBddSupp_of_continuous hψc hψs
  obtain ⟨Ck, hCk⟩ := hv L
  set H : Ω × Rd d → ℝ := fun p => ψ p.2 * Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod volume) :=
    (((hψc.measurable.comp measurable_snd).mul
      (measurable_Y₂ hYc hYm)).aestronglyMeasurable).mul hZ.1.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x
    have h1 := (memLp_Y hW hYW x).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((memLp_Y hW hYW x).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = _ := by rw [integral_div, integral_add h1 hZ2]
  have hY2 : ∀ x : Rd d, ‖x‖ ≤ L → ∫ ω, Y x ω ^ 2 ∂P ≤ Ck := fun x hx => by
    rw [integral_sq_Y hW hYW x]
    exact hCk x hx
  have hHi : Integrable H (P.prod volume) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hH, mul_assoc]
      exact ((memLp_Y hW hYW x).integrable_mul hZ).const_mul _
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

include hYc hYm hv in
/-- `ω ↦ ∫ ψ(x) Y(x, ω) dx` is in `L²(P)`. -/
theorem memLp_integral_mul_Y {ψ : Rd d → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    MemLp (fun ω => ∫ x, ψ x * Y x ω) 2 P := by
  have := hW.isProbabilityMeasure
  obtain ⟨Mψ, L, hψ⟩ := exists_isBddSupp_of_continuous hψc hψs
  obtain ⟨Ck, hCk⟩ := hv L
  have hjm := measurable_Y₂ hYc hYm
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
      exact (memLp_Y hW hYW x).integrable_sq.const_mul _
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
        rw [integral_sq_Y hW hYW x]
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
